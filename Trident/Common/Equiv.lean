-- Trident.Common.Equiv
-- Layer 2: Semantic equivalence checker
-- Runs a parsed kernel against the proved reference on concrete inputs
-- and compares outputs. This is the bridge between Layer 1 (proofs)
-- and real .ttir files.

import Trident.Target.Semantics
import Trident.Compiler
import Trident.Proofs.VectorAddProof

namespace Trident

/-- Init state for compiled reference kernel (uses a_base/b_base/c_base) -/
def refInitState (a b : List Int) (pid bs gs : Nat) : MachineState :=
  vectorAddInitState a b pid bs gs

/-- Init state for parsed real TTIR kernels (uses arg0/arg1/arg2 naming) -/
def parsedInitState (a b : List Int) (pid bs gs : Nat) : MachineState :=
  let n := a.length
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := layoutMemory a b
  , env        := fun v => match v with
      | "arg0"   => some (TritonValue.scalar 0)
      | "arg1"   => some (TritonValue.scalar (Int.ofNat n))
      | "arg2"   => some (TritonValue.scalar (Int.ofNat (2 * n)))
      | "a_base" => some (TritonValue.scalar 0)
      | "b_base" => some (TritonValue.scalar (Int.ofNat n))
      | "c_base" => some (TritonValue.scalar (Int.ofNat (2 * n)))
      | "bsize"  => some (TritonValue.scalar (Int.ofNat bs))
      | _        => none }

/-- Run reference kernel and extract output tile -/
def runRef (a b : List Int) (pid bs gs : Nat) : List Int :=
  let s  := refInitState a b pid bs gs
  let s' := evalKernel compiledVectorAdd s
  (List.range bs).map fun i =>
    s'.readMem (2 * a.length + pid * bs + i)

/-- Run parsed kernel and extract output tile -/
def runAndExtract (kernel : TritonKernel) (a b : List Int)
    (pid bs gs : Nat) : List Int :=
  let s  := parsedInitState a b pid bs gs
  let s' := evalKernel kernel s
  (List.range bs).map fun i =>
    s'.readMem (2 * a.length + pid * bs + i)

/--
  Check semantic equivalence between a parsed kernel and compiledVectorAdd
  by running both on several concrete inputs and comparing outputs.
  NOT a proof — a dynamic check that transfers proof confidence to new kernels.
-/
def checkVectorAddEquiv (parsed : TritonKernel) : Bool :=
  let tests : List (List Int × List Int × Nat × Nat) := [
    ([1, 2, 3, 4],                    [10, 20, 30, 40],         4, 1),
    ([0, 0, 0, 0],                    [0, 0, 0, 0],             4, 1),
    ([100, 200],                      [1, 2],                   2, 1),
    ([1, 2, 3, 4, 5, 6, 7, 8],        [8, 7, 6, 5, 4, 3, 2, 1], 8, 1),
  ]
  tests.all fun (a, b, bs, gs) =>
    let ref := runRef              a b 0 bs gs
    let got := runAndExtract parsed a b 0 bs gs
    ref == got

/-- Result type for the equivalence check -/
inductive EquivResult
  | equivalent                       : EquivResult
  | notEquivalent (msg : String)     : EquivResult
  | parseError                       : EquivResult

/-- Full check with result -/
def verifyAgainstVectorAdd (parsed : TritonKernel) : EquivResult :=
  if checkVectorAddEquiv parsed
  then .equivalent
  else .notEquivalent "outputs differ on test inputs"

end Trident
