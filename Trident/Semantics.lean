-- Trident.Semantics
-- The operational semantics of Triton IR.
-- This is the core interpreter: given an instruction and a machine state,
-- what is the new machine state?
--
-- CRITICAL DESIGN DECISION:
-- evalOp is written to be PROVABLE, not just executable.
-- This means:
--   1. Each case returns Option TritonValue (not partial/panic)
--   2. Pattern matching is exhaustive and explicit
--   3. Helper lemmas are stated alongside each case
--   4. The recursive structure mirrors what induction proofs need
--
-- In CompCert terms, this is the "target language semantics" —
-- the formal definition of what each TTIR instruction means.

import Trident.Machine
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Zip

namespace Trident

open TritonValue

/-
1. SINGLE INSTRUCTION SEMANTICS
evalOp: executes one SSA instruction, returns the resulting value.
Returns `none` if the instruction's preconditions are not met
(wrong number of args, wrong types, etc.)
-/
def evalOp (op : TritonOp) (args : List String) (state : MachineState)
    : Option TritonValue :=
  match op with

  -- get_program_id: returns the block index as a scalar
  | .get_program_id _ =>
      some (scalar (Int.ofNat state.pid))

  -- constant: returns a literal integer value
  | .constant v =>
      some (scalar v)

  -- make_range: produces [0, 1, ..., block_size-1] as a tile
  | .make_range =>
      let rangeList := (List.range state.block_size).map Int.ofNat
      some (tensor [state.block_size] rangeList)

  -- splat: broadcasts a scalar to fill an entire tile
  | .splat =>
      match args with
      | [v] =>
        match state.lookup v with
        | some (scalar s) =>
            some (tensor [state.block_size] (List.replicate state.block_size s))
        | _ => none
      | _ => none

  -- addptr: pointer arithmetic, tile-wise
  -- Handles scalar+scalar, scalar+tensor, tensor+tensor
  | .addptr =>
      match args with
      | [ptrVar, offVar] =>
        match state.lookup ptrVar, state.lookup offVar with
        | some (scalar p), some (scalar o) =>
            some (scalar (p + o))
        | some (scalar p), some (tensor shape offsets) =>
            some (tensor shape (offsets.map (· + p)))
        | some (tensor s1 ptrs), some (tensor s2 offsets) =>
            if s1 == s2
            then some (tensor s1 ((ptrs.zip offsets).map (fun (p, o) => p + o)))
            else none
        | _, _ => none
      | _ => none

  -- load: reads values from virtual memory using pointer addresses
  | .load =>
      match args with
      | [ptrVar] =>
        match state.lookup ptrVar with
        | some (scalar p) =>
            some (scalar (state.readMem p.natAbs))
        | some (tensor shape ptrs) =>
            some (tensor shape (ptrs.map (fun p => state.readMem p.natAbs)))
        | _ => none
      | _ => none

  -- store: writes values to virtual memory (returns unit, mutates state separately)
  -- Note: store is handled in evalInstr below, not here
  | .store => none

  -- addi: element-wise integer addition (scalar or tile)
  | .addi =>
      match args with
      | [a, b] =>
        match state.lookup a, state.lookup b with
        | some (scalar x), some (scalar y) =>
            some (scalar (x + y))
        | some (tensor s1 xs), some (tensor s2 ys) =>
            if s1 == s2
            then some (tensor s1 ((xs.zip ys).map (fun (x, y) => x + y)))
            else none
        | _, _ => none
      | _ => none

  -- muli: element-wise integer multiplication
  | .muli =>
      match args with
      | [a, b] =>
        match state.lookup a, state.lookup b with
        | some (scalar x), some (scalar y) =>
            some (scalar (x * y))
        | some (tensor s1 xs), some (tensor s2 ys) =>
            if s1 == s2
            then some (tensor s1 ((xs.zip ys).map (fun (x, y) => x * y)))
            else none
        | _, _ => none
      | _ => none

  -- subi: element-wise integer subtraction
  | .subi =>
      match args with
      | [a, b] =>
        match state.lookup a, state.lookup b with
        | some (scalar x), some (scalar y) =>
            some (scalar (x - y))
        | some (tensor s1 xs), some (tensor s2 ys) =>
            if s1 == s2
            then some (tensor s1 ((xs.zip ys).map (fun (x, y) => x - y)))
            else none
        | _, _ => none
      | _ => none

  -- reduce_add: sums all elements of a tile to a scalar
  | .reduce_add =>
      match args with
      | [v] =>
        match state.lookup v with
        | some (tensor _ vals) =>
            some (scalar (vals.foldl (· + ·) 0))
        | _ => none
      | _ => none

  -- reduce_max: finds maximum element of a tile
  | .reduce_max =>
      match args with
      | [v] =>
        match state.lookup v with
        | some (tensor _ (hd :: tl)) =>
            some (scalar (tl.foldl max hd))
        | _ => none
      | _ => none

  -- All other ops: placeholder (extend as needed)
  | _ => none

/-
2. SINGLE INSTRUCTION EXECUTION
evalInstr executes one full SSA instruction, binding the result
into the environment and handling stores (which mutate memory).
This is separated from evalOp so stores can update MachineState.
-/
def evalInstr (instr : TritonInstr) (state : MachineState) : MachineState :=
  match instr.op with
  -- Store is special: it mutates memory instead of binding a variable
  | .store =>
      match instr.args with
      | [ptrVar, valVar] =>
        match state.lookup ptrVar, state.lookup valVar with
        | some (scalar p), some (scalar v) =>
            state.writeMem p.natAbs v
        | some (tensor _ ptrs), some (tensor _ vals) =>
            -- Store each element of the value tile to the corresponding pointer
            (ptrs.zip vals).foldl
              (fun s (p, v) => s.writeMem p.natAbs v)
              state
        | _, _ => state
      | _ => state
  -- All other instructions: evaluate and bind result
  | _ =>
      match evalOp instr.op instr.args state with
      | some val => state.bind instr.result val
      | none     => state  -- On failure, state is unchanged

/-
3. KERNEL EXECUTION
evalKernel runs a full sequence of instructions, threading state through.
This is the top-level interpreter function.
-/
def evalKernel (kernel : TritonKernel) (state : MachineState) : MachineState :=
  kernel.foldl (fun s instr => evalInstr instr s) state

/-
4. KEY SEMANTICS LEMMAS
These are the "simulation lemmas" used by Proofs/ files.
They state how evalOp behaves on each case — these are the
building blocks of correctness proofs.
-/

-- get_program_id always succeeds and returns the pid
@[simp]
lemma evalOp_get_program_id (axis : Nat) (args : List String) (s : MachineState) :
    evalOp (.get_program_id axis) args s = some (scalar (Int.ofNat s.pid)) := by
  simp [evalOp]

-- constant always succeeds and returns the literal value
@[simp]
lemma evalOp_constant (v : Int) (args : List String) (s : MachineState) :
    evalOp (.constant v) args s = some (scalar v) := by
  simp [evalOp]

-- make_range produces a tile of [0 .. block_size-1]
@[simp]
lemma evalOp_make_range (args : List String) (s : MachineState) :
    evalOp .make_range args s =
    some (tensor [s.block_size] ((List.range s.block_size).map Int.ofNat)) := by
  simp [evalOp]

-- evalInstr for non-store ops binds the result of evalOp
lemma evalInstr_bind (instr : TritonInstr) (s : MachineState)
    (h_not_store : instr.op ≠ .store)
    (val : TritonValue)
    (h_eval : evalOp instr.op instr.args s = some val) :
    (evalInstr instr s).lookup instr.result = some val := by
  simp [evalInstr, h_not_store, h_eval, MachineState.bind, MachineState.lookup]

-- evalKernel on empty kernel is identity
@[simp]
lemma evalKernel_nil (s : MachineState) : evalKernel [] s = s := by
  simp [evalKernel]

-- evalKernel on a single instruction is evalInstr
@[simp]
lemma evalKernel_cons (instr : TritonInstr) (rest : TritonKernel) (s : MachineState) :
    evalKernel (instr :: rest) s = evalKernel rest (evalInstr instr s) := by
  simp [evalKernel, List.foldl]

end Trident
