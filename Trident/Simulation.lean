-- Trident.Simulation
-- The forward simulation framework.
--
-- This is the heart of the CompCert methodology applied to Trident.
--
-- CompCert's correctness theorem has this shape:
--   For all C programs P compiled to assembly A:
--   if P terminates with result R under C semantics,
--   then A terminates with result R under assembly semantics.
--
-- Trident's correctness theorem has this shape:
--   For all SpecLang specs S compiled to TTIR kernel K:
--   for all valid inputs I and all pid values:
--   evalKernel K (initState I pid) produces the same output
--   as evalSpec S I restricted to pid's tile.
--
-- The FORWARD SIMULATION RELATION is the proof technique:
-- we show that every step of the TTIR execution corresponds to
-- a step in the SpecLang semantics, maintaining a correspondence
-- invariant (the "simulation invariant") throughout.

import Trident.Semantics
import Trident.SourceLang
import Mathlib.Data.List.Basic

namespace Trident

/-
1. THE SIMULATION INVARIANT
The simulation invariant R relates a MachineState to a partial
spec computation. It says: "this machine state corresponds to
having computed spec outputs for indices [0 .. progress)."

For our kernels, after full execution, progress = block_size,
meaning all elements in the tile have been computed correctly.
-/
def SimulationInvariant
    (spec   : SpecKernel)
    (inputs : List (List Int))
    (pid    : Nat)
    (bs     : Nat)           -- block_size
    (state  : MachineState)
    (outputVar : String)
    (progress : Nat)         -- how many elements are correctly computed so far
    : Prop :=
  -- For every index i that has been "processed" so far,
  -- the value in memory at the output location matches the spec
  ∀ i < progress,
    state.readMem (pid * bs + i) =
    (spec.spec inputs).getD i 0

/-
2. THE FORWARD SIMULATION THEOREM TYPE
This is the shape of the correctness theorem every kernel proof must establish.
It says: after running the full kernel, the output in memory
matches the mathematical spec for every index in this block's tile.
-/
def ForwardSimulation
    (kernel    : TritonKernel)
    (target    : CompilationTarget)
    (inputs    : List (List Int))
    (pid bs gs : Nat)
    (baseState : MachineState)
    : Prop :=
  -- The final state after running the kernel
  let finalState := evalKernel kernel baseState
  -- For every index i in this block's tile
  ∀ i < bs,
    -- The output in memory matches the spec
    finalState.readMem (pid * bs + i) =
    (target.source.spec inputs).getD (pid * bs + i) 0

/-
3. GLOBAL CORRECTNESS
The global correctness theorem says: for ALL pid values,
the union of all tiles covers the full spec output.
This is the compositionality argument — the step from
per-block correctness to whole-array correctness.

This is the theorem that appears at the top of a Trident paper.
-/
def GlobalCorrectness
    (kernel    : TritonKernel)
    (target    : CompilationTarget)
    (inputs    : List (List Int))
    (bs gs     : Nat)
    (mkState   : Nat → MachineState)  -- how to build initial state for each pid
    : Prop :=
  ∀ pid < gs,
    ForwardSimulation kernel target inputs pid bs gs (mkState pid)

/-
4. HELPER: TILE SLICE
The portion of the full output array that pid is responsible for.
pid handles indices [pid * bs .. (pid+1) * bs - 1].
-/
def tileSlice (fullOutput : List Int) (pid bs : Nat) : List Int :=
  (List.range bs).map (fun i => fullOutput.getD (pid * bs + i) 0)

/-
5. COMPOSITIONALITY LEMMA (statement)
If every pid correctly computes its tile, the full output is correct.
The proof of this lives in each kernel's Proofs/ file.
-/
theorem compositionality_from_tiles
    (fullSpec   : List Int)
    (tileSpecs  : Nat → List Int)
    (gs bs      : Nat)
    (h_tiles    : ∀ pid < gs, tileSpecs pid = tileSlice fullSpec pid bs)
    (h_length   : fullSpec.length = gs * bs)
    (i          : Nat)
    (h_i        : i < gs * bs) :
    (tileSpecs (i / bs)).getD (i % bs) 0 = fullSpec.getD i 0 := by
  have h_pid : i / bs < gs := by
    apply Nat.div_lt_iff_lt_mul (by omega) |>.mpr
    omega
  have h_tile := h_tiles (i / bs) h_pid
  simp [tileSlice] at h_tile
  rw [h_tile]
  simp [tileSlice]
  congr 1
  omega

end Trident
