-- Trident.Machine
-- The virtual GPU hardware state model.
-- In CompCert terms, this is the "machine model" —
-- the concrete state that the target language (TTIR) executes over.

import Trident.Dialect
import Mathlib.Data.List.Basic

namespace Trident

/-
1. RUNTIME VALUES
The actual data that lives in registers and memory during kernel execution.
Scalars hold a single value; tensors hold a full tile of values.
-/
inductive TritonValue
  | scalar (val : Int)
  | tensor (shape : List Nat) (vals : List Int)
  deriving BEq, Repr

/-
2. MACHINE STATE
The complete state of one GPU thread block (one program ID) mid-execution.

Fields:
  pid        — which block this is (0 .. grid_size-1)
  block_size — number of elements this block processes
  grid_size  — total number of blocks in the launch
  memory     — virtual flat memory: address → value
  env        — SSA variable environment: name → value
-/
structure MachineState where
  pid        : Nat
  block_size : Nat
  grid_size  : Nat
  memory     : Nat → Int         -- Virtual memory (address space)
  env        : String → Option TritonValue  -- SSA variable bindings

/-
3. STATE OPERATIONS
Helper functions for reading and updating the machine state.
Keeping these as named lemmas makes proofs cleaner — we can
rewrite with them instead of unfolding the struct manually.
-/

-- Look up a variable in the environment
def MachineState.lookup (s : MachineState) (v : String) : Option TritonValue :=
  s.env v

-- Bind a new SSA variable in the environment
-- Returns a new MachineState with the variable defined
def MachineState.bind (s : MachineState) (v : String) (val : TritonValue) : MachineState :=
  { s with env := fun name => if name == v then some val else s.env name }

-- Read from virtual memory at a given address
def MachineState.readMem (s : MachineState) (addr : Nat) : Int :=
  s.memory addr

-- Write to virtual memory — returns updated state
def MachineState.writeMem (s : MachineState) (addr : Nat) (val : Int) : MachineState :=
  { s with memory := fun a => if a == addr then val else s.memory a }

/-
4. SAFETY SPECIFICATION
The mathematical property that load operations must satisfy.
This is the formal statement of "no out-of-bounds memory access."
Separating it from evalOp means we can state and prove it independently.
-/
def IsSafeLoad (ptrVar : String) (bufferSize : Nat) (state : MachineState) : Prop :=
  match state.env ptrVar with
  | some (TritonValue.scalar p)       => p.natAbs < bufferSize
  | some (TritonValue.tensor _ ptrs)  => ∀ p ∈ ptrs, p.natAbs < bufferSize
  | none                              => False

/-
5. KEY LEMMAS ABOUT STATE
These lemmas are the "machine lemmas" that proofs will use.
Having them named and proved here means Proofs/ files stay clean.
-/

-- Binding a variable and immediately looking it up returns that variable
@[simp]
lemma bind_lookup_self (s : MachineState) (v : String) (val : TritonValue) :
    (s.bind v val).lookup v = some val := by
  simp [MachineState.bind, MachineState.lookup]

-- Binding one variable doesn't affect lookups of other variables
@[simp]
lemma bind_lookup_other (s : MachineState) (v w : String) (val : TritonValue) (h : v ≠ w) :
    (s.bind v val).lookup w = s.lookup w := by
  simp [MachineState.bind, MachineState.lookup, h]

-- Writing memory at one address doesn't affect other addresses
@[simp]
lemma writeMem_readMem_self (s : MachineState) (addr : Nat) (val : Int) :
    (s.writeMem addr val).readMem addr = val := by
  simp [MachineState.writeMem, MachineState.readMem]

@[simp]
lemma writeMem_readMem_other (s : MachineState) (a b : Nat) (val : Int) (h : a ≠ b) :
    (s.writeMem a val).readMem b = s.readMem b := by
  simp [MachineState.writeMem, MachineState.readMem, h]

end Trident
