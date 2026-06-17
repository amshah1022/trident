import Trident.Common.Symbolic
import Trident.Target.Semantics
import Trident.Proofs.VectorAddProof

namespace Trident
open TritonValue

-- concreteMem maps logical indices to values
-- Expr.var "a" i → a[i] requires mem i = a[i]
-- Expr.var "b" i → b[i] requires mem i = b[i]
-- BUT same i could refer to both a and b!
-- Resolution: use layoutMemory for physical addresses
-- and note that Expr.var "b" (addr-n) has index addr-n ∈ [0,n)
-- while layoutMemory maps addr-n to a[addr-n], not b[addr-n]
-- 
-- So we need a different concreteMem that maps i to b[i] for b-vars
-- Since evalExpr ignores the name, we can't distinguish a vs b by name
-- The soundness theorem must use a mem that works for BOTH:
-- concreteMem i = a[i] for i in a-range
-- concreteMem i = b[i] for i in b-range
-- These overlap! So we need to restrict the theorem to non-overlapping cases
-- OR change Symbolic.lean to use flat addresses

-- APPROACH: Define soundness for the flat memory layout
-- where evalExpr uses layoutMemory as the concrete memory
-- and the symbolic state uses FLAT addresses for b vars

-- For now, prove initStates_faithful with a sorry on the b-var case
-- and focus on the structure

def concreteMem (a b : List Int) : Nat → Int := layoutMemory a b

def StatesFaithful (s : MachineState) (ss : SymState) (mem : Nat → Int) : Prop :=
  s.pid = ss.pid
  ∧ s.block_size = ss.block_size
  ∧ s.grid_size = ss.grid_size
  ∧ (∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
  ∧ (∀ v val, s.env v = some (scalar val) →
      ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
  ∧ (∀ v sh vals, s.env v = some (tensor sh vals) →
      ∃ n g, ss.env v = some (SymValue.tensor n g)
        ∧ ∀ i, evalExpr (g i) mem = vals.getD i 0)

theorem initStates_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (vectorAddInitState a b pid bs gs)
      (symVectorAddInitState pid bs gs a.length)
      (concreteMem a b) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro addr
    simp only [symVectorAddInitState, vectorAddInitState, concreteMem]
    by_cases h1 : addr < a.length
    · simp only [h1, ↓reduceIte, evalExpr, layoutMemory, h1, ↓reduceIte]
    · by_cases h2 : addr < 2 * a.length
      · -- Expr.var "b" (addr - a.length): evalExpr gives layoutMemory a b (addr - a.length)
        -- but we need layoutMemory a b addr
        -- these are different! This is the fundamental mismatch
        simp only [h1, h2, ↓reduceIte, evalExpr]
        -- goal: layoutMemory a b (addr - a.length) = layoutMemory a b addr
        -- this is FALSE in general
        -- the symbolic interpreter uses wrong indices for b
        -- With flat address fix: evalExpr (Expr.var "b" addr) mem = mem addr = layoutMemory a b addr ✓
      · simp only [h1, h2, ↓reduceIte, evalExpr]; symm; unfold layoutMemory; simp [h1, h2]
  · intro v val hv
    simp only [vectorAddInitState] at hv
    simp only [symVectorAddInitState]
    split at hv <;> simp_all [evalExpr]
  · intro v sh vals hv
    simp only [vectorAddInitState] at hv
    split at hv <;> simp_all

-- ── Per-Instruction Faithfulness ────────────────────────────────────────────

/-- Each instruction preserves StatesFaithful -/
theorem evalInstr_faithful (instr : TritonInstr)
    (s : MachineState) (ss : SymState) (mem : Nat -> Int)
    (h : StatesFaithful s ss mem) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  sorry

theorem symEvalKernel_faithful (K : TritonKernel)
    (s : MachineState) (ss : SymState) (mem : Nat -> Int)
    (h : StatesFaithful s ss mem) :
    StatesFaithful (evalKernel K s) (symEvalKernel K ss) mem := by
  induction K generalizing s ss with
  | nil => simp [evalKernel, symEvalKernel]; exact h
  | cons instr rest ih =>
    simp only [evalKernel, symEvalKernel, List.foldl]
    exact ih (evalInstr instr s) (symEvalInstr instr ss)
      (evalInstr_faithful instr s ss mem h)

theorem symEval_sound (K : TritonKernel) (a b : List Int)
    (pid bs gs i : Nat) :
    evalExpr
      ((symEvalKernel K (symVectorAddInitState pid bs gs a.length)).memory
        (2 * a.length + pid * bs + i))
      (concreteMem a b) =
    MachineState.readMem (evalKernel K (vectorAddInitState a b pid bs gs))
      (2 * a.length + pid * bs + i) := by
  have hf := symEvalKernel_faithful K
    (vectorAddInitState a b pid bs gs)
    (symVectorAddInitState pid bs gs a.length)
    (concreteMem a b)
    (initStates_faithful a b pid bs gs)
  obtain ⟨_, _, _, h_mem, _⟩ := hf
  simp only [MachineState.readMem]
  exact h_mem (2 * a.length + pid * bs + i)

#check @symEval_sound

end Trident
