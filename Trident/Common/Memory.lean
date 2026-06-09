-- Trident.Common.Memory
-- The virtual GPU machine state.
-- Models one thread block's view of memory and registers.
--
-- CompCert equivalent: common/Memory.v
-- Key difference from CompCert: GPU memory is flat (no stack frames,
-- no heap allocation, no undefined behavior from C).
-- This makes our memory model significantly simpler.

import Trident.Common.Values

namespace Trident

/--
`MachineState` is the complete state of one GPU thread block mid-execution.

Fields:
  pid        — which block this is (0 .. grid_size - 1)
  block_size — number of elements this block processes (BLOCK_SIZE constexpr)
  grid_size  — total number of blocks launched
  memory     — flat virtual memory: address → integer value
  env        — SSA variable environment: name → value
-/
structure MachineState where
  pid        : Nat
  block_size : Nat
  grid_size  : Nat
  memory     : Nat → Int
  env        : String → Option TritonValue
  deriving Inhabited

namespace MachineState

-- ── Environment operations ────────────────────────────────────────────────────

/-- Look up an SSA variable -/
@[inline]
def lookup (s : MachineState) (v : String) : Option TritonValue :=
  s.env v

/-- Bind an SSA variable to a value, returning the updated state -/
@[inline]
def bind (s : MachineState) (v : String) (val : TritonValue) : MachineState :=
  { s with env := fun name => if name == v then some val else s.env name }

-- ── Memory operations ─────────────────────────────────────────────────────────

/-- Read one integer from virtual memory -/
@[inline]
def readMem (s : MachineState) (addr : Nat) : Int :=
  s.memory addr

/-- Write one integer to virtual memory -/
@[inline]
def writeMem (s : MachineState) (addr : Nat) (val : Int) : MachineState :=
  { s with memory := fun a => if a == addr then val else s.memory a }

/-- Write a full tile of values starting at base address -/
def writeTile (s : MachineState) (addrs : List Nat) (vals : List Int) : MachineState :=
  (addrs.zip vals).foldl (fun st (a, v) => st.writeMem a v) s

-- ── Key lemmas ────────────────────────────────────────────────────────────────
-- These are the "machine lemmas" that simulation proofs use.
-- Named and proved here so Proofs/ files stay clean.

@[simp]
theorem bind_lookup_self (s : MachineState) (v : String) (val : TritonValue) :
    (s.bind v val).lookup v = some val := by
  simp [bind, lookup]

@[simp]
theorem bind_lookup_other (s : MachineState) (v w : String) (val : TritonValue)
    (h : v ≠ w) : (s.bind v val).lookup w = s.lookup w := by
  simp [bind, lookup]; intro heq; simp [heq] at h

@[simp]
theorem writeMem_readMem_self (s : MachineState) (addr : Nat) (val : Int) :
    (s.writeMem addr val).readMem addr = val := by
  simp [writeMem, readMem]

@[simp]
theorem writeMem_readMem_other (s : MachineState) (a b : Nat) (val : Int)
    (h : a ≠ b) : (s.writeMem a val).readMem b = s.readMem b := by
  simp [writeMem, readMem]; intro heq; simp [heq] at h

-- Binding does not affect memory
@[simp]
theorem bind_readMem (s : MachineState) (v : String) (val : TritonValue) (a : Nat) :
    (s.bind v val).readMem a = s.readMem a := by
  simp [bind, readMem]

-- writeMem does not affect the environment
@[simp]
theorem writeMem_lookup (s : MachineState) (addr : Nat) (val : Int) (v : String) :
    (s.writeMem addr val).lookup v = s.lookup v := by
  simp [writeMem, lookup]

end MachineState
end Trident
