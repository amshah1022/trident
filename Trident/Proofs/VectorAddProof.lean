import Trident.Common.Smallstep
import Trident.Source.Specs.VectorAddSpec
import Trident.Target.Semantics
import Trident.Compiler

namespace Trident

open MachineState

def layoutMemory (a b : List Int) : Nat → Int := fun addr =>
  let n := a.length
  if addr < n         then a.getD addr 0
  else if addr < 2*n  then b.getD (addr - n) 0
  else                     0

def vectorAddInitState (a b : List Int) (pid bs gs : Nat) : MachineState :=
  let n := a.length
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := layoutMemory a b
  , env        := fun v => match v with
      | "a_base" => some (TritonValue.scalar 0)
      | "b_base" => some (TritonValue.scalar (Int.ofNat n))
      | "c_base" => some (TritonValue.scalar (Int.ofNat (2 * n)))
      | _        => none }

def vectorAddSourceSem : SourceSemantics :=
  tensorExprSemantics TensorExpr.vectorAdd

def vectorAddTargetSem : TargetSemantics where
  init   := fun inputs pid bs gs =>
    match inputs with
    | [a, b] => vectorAddInitState a b pid bs gs
    | _      => vectorAddInitState [] [] pid bs gs
  output := fun s =>
    (List.range s.block_size).map fun i =>
      s.readMem (2 * s.grid_size * s.block_size + s.pid * s.block_size + i)
  exec   := fun s => evalKernel compiledVectorAdd s

theorem vectorAdd_correct
    (a b : List Int) (pid bs gs : Nat)
    (h_len : a.length = b.length)
    (h_bs  : bs > 0)
    (h_pid : pid < gs)
    (h_cov : gs * bs = a.length) :
    ∀ i < bs,
      let s  := vectorAddInitState a b pid bs gs
      let s' := evalKernel compiledVectorAdd s
      s'.readMem (2 * a.length + pid * bs + i) =
      (vectorAddSpec a b).getD (pid * bs + i) 0 := by
  intro i hi
  simp only []
  simp [vectorAddInitState, vectorAddSpec, layoutMemory]
  sorry

theorem vectorAdd_global
    (a b : List Int) (bs gs : Nat)
    (h_len : a.length = b.length)
    (h_bs  : bs > 0)
    (h_cov : gs * bs = a.length) :
    GlobalCorrectness vectorAddSourceSem vectorAddTargetSem [a, b] bs gs := by
  intro pid h_pid
  refine ⟨⟨fun inputs s => inputs = [a, b], ?_, ?_, ?_⟩, ?_⟩
  · simp [vectorAddSourceSem, vectorAddTargetSem, tensorExprSemantics]
  · intro s1 t1 s2 hstep _
    simp [vectorAddSourceSem, tensorExprSemantics] at hstep
  · intro s t _
    simp [vectorAddSourceSem, vectorAddTargetSem, tensorExprSemantics]
    sorry
  · intro i hi
    simp [vectorAddTargetSem, vectorAddSourceSem, tensorExprSemantics]
    sorry

end Trident
