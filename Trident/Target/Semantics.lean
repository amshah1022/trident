-- Trident.Target.Semantics
-- Operational semantics of Triton IR.
-- Defines what each instruction DOES when it executes.
--
-- CompCert equivalent: backend/RTL.v semantics section
--
-- DESIGN PRINCIPLE: Written for PROVABILITY, not just executability.
-- Every case is explicit, every helper is named and lemmatized,
-- the recursive structure mirrors what induction proofs need.

import Trident.Target.Dialect
import Trident.Common.Memory

namespace Trident

open TritonValue

-- ── Single Operation Semantics ────────────────────────────────────────────────

/--
`evalOp` gives the meaning of one Triton operation.
Returns `none` if preconditions fail (wrong args, type mismatch).
Returns `some val` on success.
-/
def evalOp (op : TritonOp) (args : List String) (s : MachineState)
    : Option TritonValue :=
  match op with

  | .get_program_id _ =>
      some (scalar (Int.ofNat s.pid))

  | .constant v =>
      some (scalar v)

  | .make_range =>
      some (tensor [s.block_size] ((List.range s.block_size).map Int.ofNat))

  | .splat =>
      match args with
      | [v] => match s.lookup v with
        | some (scalar x) =>
            some (tensor [s.block_size] (List.replicate s.block_size x))
        | _ => none
      | _ => none

  | .addptr =>
      match args with
      | [p, o] => match s.lookup p, s.lookup o with
        | some (scalar base), some (scalar off) =>
            some (scalar (base + off))
        | some (scalar base), some (tensor sh offs) =>
            some (tensor sh (offs.map (· + base)))
        | some (tensor sh1 bases), some (tensor sh2 offs) =>
            if sh1 == sh2
            then some (tensor sh1 ((bases.zip offs).map fun (b, o) => b + o))
            else none
        | _, _ => none
      | _ => none

  | .load =>
      match args with
      | [p] => match s.lookup p with
        | some (scalar addr) =>
            some (scalar (s.readMem addr.natAbs))
        | some (tensor sh addrs) =>
            some (tensor sh (addrs.map fun a => s.readMem a.natAbs))
        | _ => none
      | _ => none

  | .addi =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          va.zipWith (· + ·) vb
      | _ => none

  | .subi =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          va.zipWith (· - ·) vb
      | _ => none

  | .muli =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          va.zipWith (· * ·) vb
      | _ => none

  | .reduce_sum _ =>
      match args with
      | [v] => match s.lookup v with
        | some (tensor _ vals) => some (scalar (vals.foldl (· + ·) 0))
        | _ => none
      | _ => none

  | .reduce_max _ =>
      match args with
      | [v] => match s.lookup v with
        | some (tensor _ (hd :: tl)) => some (scalar (tl.foldl max hd))
        | _ => none
      | _ => none

  -- Store and all unimplemented ops handled in evalInstr
  | _ => none

-- ── Instruction Execution ─────────────────────────────────────────────────────

/--
`evalInstr` executes one full SSA instruction.
- For `store`: writes to memory, returns updated state
- For everything else: evaluates op and binds result variable
-/
def evalInstr (instr : TritonInstr) (s : MachineState) : MachineState :=
  match instr.op with
  | .store =>
      match instr.args with
      | [p, v] => match s.lookup p, s.lookup v with
        | some (scalar addr), some (scalar val) =>
            s.writeMem addr.natAbs val
        | some (tensor _ addrs), some (tensor _ vals) =>
            s.writeTile (addrs.map Int.natAbs) vals
        | _, _ => s
      | _ => s
  | _ =>
      match evalOp instr.op instr.args s with
      | some val => s.bind instr.result val
      | none     => s

-- ── Kernel Execution ──────────────────────────────────────────────────────────

/-- Run a complete kernel: fold evalInstr over the instruction list -/
def evalKernel (kernel : TritonKernel) (s : MachineState) : MachineState :=
  kernel.foldl (fun st instr => evalInstr instr st) s

-- ── Semantics Lemmas ──────────────────────────────────────────────────────────
-- Named lemmas for each op.
-- These are the building blocks that simulation proofs use.
-- @[simp] lets the simp tactic apply them automatically.

@[simp]
theorem evalOp_get_program_id (axis : Nat) (args : List String) (s : MachineState) :
    evalOp (.get_program_id axis) args s = some (scalar (Int.ofNat s.pid)) := by
  simp [evalOp]

@[simp]
theorem evalOp_constant (v : Int) (args : List String) (s : MachineState) :
    evalOp (.constant v) args s = some (scalar v) := by
  simp [evalOp]

@[simp]
theorem evalOp_make_range (args : List String) (s : MachineState) :
    evalOp .make_range args s =
    some (tensor [s.block_size] ((List.range s.block_size).map Int.ofNat)) := by
  simp [evalOp]

@[simp]
theorem evalKernel_nil (s : MachineState) :
    evalKernel [] s = s := by
  simp [evalKernel]

@[simp]
theorem evalKernel_cons (i : TritonInstr) (rest : TritonKernel) (s : MachineState) :
    evalKernel (i :: rest) s = evalKernel rest (evalInstr i s) := by
  simp [evalKernel, List.foldl]

theorem evalInstr_non_store_bind
    (instr : TritonInstr) (s : MachineState) (val : TritonValue)
    (h_op : evalOp instr.op instr.args s = some val)
    (h_not_store : instr.op ≠ .store) :
    evalInstr instr s = s.bind instr.result val := by
  simp [evalInstr, h_op]

-- evalInstr only changes the result variable's binding
theorem evalInstr_lookup_other
    (instr : TritonInstr) (s : MachineState) (v : String)
    (h_diff : v ≠ instr.result)
    (h_not_store : instr.op ≠ .store)
    (val : TritonValue)
    (h_op : evalOp instr.op instr.args s = some val) :
    (evalInstr instr s).lookup v = s.lookup v := by
  rw [evalInstr_non_store_bind instr s val h_op h_not_store]
  exact MachineState.bind_lookup_other _ _ _ _ (Ne.symm h_diff)

-- ── TargetSemantics Instance ──────────────────────────────────────────────────
-- Packages the target semantics for use with ForwardSimulation.

/-- Build initial state for a kernel given inputs and launch params -/
def buildInitState
    (inputs  : List (List Int))
    (pid bs gs : Nat)
    (extraEnv : String → Option TritonValue := fun _ => none)
    : MachineState :=
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := fun _ => 0
  , env        := extraEnv }

end Trident
