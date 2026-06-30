import Trident.Common.Symbolic
import Trident.Target.Semantics
import Trident.Proofs.Soundness
import Trident.Common.Equiv

namespace Trident
open TritonValue

-- ══════════════════════════════════════════════════════════════════════════════
-- Section 1: Expr.beq soundness
-- ══════════════════════════════════════════════════════════════════════════════

mutual
  def exprBeqEq : (e1 e2 : Expr) → Expr.beq e1 e2 = true → e1 = e2
    | .lit a,        .lit b,        h => by simp [Expr.beq] at h; exact congrArg Expr.lit h
    | .var s1 i1,    .var s2 i2,    h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        obtain ⟨hs, hi⟩ := h; subst hs
        exact congrArg (Expr.var s1) (by exact_mod_cast hi)
    | .add a1 a2, .add b1 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq a1 b1 h.1; have h2 := exprBeqEq a2 b2 h.2
        subst h1; subst h2; rfl
    | .mul a1 a2, .mul b1 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq a1 b1 h.1; have h2 := exprBeqEq a2 b2 h.2
        subst h1; subst h2; rfl
    | .max a1 a2, .max b1 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq a1 b1 h.1; have h2 := exprBeqEq a2 b2 h.2
        subst h1; subst h2; rfl
    | .load a, .load b, h => by
        simp [Expr.beq] at h
        have h1 := exprBeqEq a b h; subst h1; rfl
    | .reduceSum as, .reduceSum bs, h => by
        simp [Expr.beq] at h
        have h1 := exprListBeqEq as bs h; subst h1; rfl
    | .lit _,       .var _ _,     h => by simp [Expr.beq] at h
    | .lit _,       .add _ _,     h => by simp [Expr.beq] at h
    | .lit _,       .mul _ _,     h => by simp [Expr.beq] at h
    | .lit _,       .max _ _,     h => by simp [Expr.beq] at h
    | .lit _,       .load _,      h => by simp [Expr.beq] at h
    | .lit _,       .reduceSum _, h => by simp [Expr.beq] at h
    | .var _ _,     .lit _,       h => by simp [Expr.beq] at h
    | .var _ _,     .add _ _,     h => by simp [Expr.beq] at h
    | .var _ _,     .mul _ _,     h => by simp [Expr.beq] at h
    | .var _ _,     .max _ _,     h => by simp [Expr.beq] at h
    | .var _ _,     .load _,      h => by simp [Expr.beq] at h
    | .var _ _,     .reduceSum _, h => by simp [Expr.beq] at h
    | .add _ _,     .lit _,       h => by simp [Expr.beq] at h
    | .add _ _,     .var _ _,     h => by simp [Expr.beq] at h
    | .add _ _,     .mul _ _,     h => by simp [Expr.beq] at h
    | .add _ _,     .max _ _,     h => by simp [Expr.beq] at h
    | .add _ _,     .load _,      h => by simp [Expr.beq] at h
    | .add _ _,     .reduceSum _, h => by simp [Expr.beq] at h
    | .mul _ _,     .lit _,       h => by simp [Expr.beq] at h
    | .mul _ _,     .var _ _,     h => by simp [Expr.beq] at h
    | .mul _ _,     .add _ _,     h => by simp [Expr.beq] at h
    | .mul _ _,     .max _ _,     h => by simp [Expr.beq] at h
    | .mul _ _,     .load _,      h => by simp [Expr.beq] at h
    | .mul _ _,     .reduceSum _, h => by simp [Expr.beq] at h
    | .max _ _,     .lit _,       h => by simp [Expr.beq] at h
    | .max _ _,     .var _ _,     h => by simp [Expr.beq] at h
    | .max _ _,     .add _ _,     h => by simp [Expr.beq] at h
    | .max _ _,     .mul _ _,     h => by simp [Expr.beq] at h
    | .max _ _,     .load _,      h => by simp [Expr.beq] at h
    | .max _ _,     .reduceSum _, h => by simp [Expr.beq] at h
    | .load _,      .lit _,       h => by simp [Expr.beq] at h
    | .load _,      .var _ _,     h => by simp [Expr.beq] at h
    | .load _,      .add _ _,     h => by simp [Expr.beq] at h
    | .load _,      .mul _ _,     h => by simp [Expr.beq] at h
    | .load _,      .max _ _,     h => by simp [Expr.beq] at h
    | .load _,      .reduceSum _, h => by simp [Expr.beq] at h
    | .reduceSum _,  .lit _,      h => by simp [Expr.beq] at h
    | .reduceSum _,  .var _ _,    h => by simp [Expr.beq] at h
    | .reduceSum _,  .add _ _,    h => by simp [Expr.beq] at h
    | .reduceSum _,  .mul _ _,    h => by simp [Expr.beq] at h
    | .reduceSum _,  .max _ _,    h => by simp [Expr.beq] at h
    | .reduceSum _,  .load _,     h => by simp [Expr.beq] at h

  def exprListBeqEq : (as bs : List Expr) → ExprList.beq as bs = true → as = bs
    | [],    [],    _ => rfl
    | [],    _::_,  h => by simp [ExprList.beq] at h
    | _::_,  [],    h => by simp [ExprList.beq] at h
    | a::as, b::bs, h => by
        simp [ExprList.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq a b h.1; have h2 := exprListBeqEq as bs h.2
        subst h1; subst h2; rfl
end

theorem Expr.beq_eq (e1 e2 : Expr) (h : Expr.beq e1 e2 = true) : e1 = e2 :=
  exprBeqEq e1 e2 h

theorem beq_evalExpr (e1 e2 : Expr) (mem : Nat → Int) (h : (e1 == e2) = true) :
    evalExpr e1 mem = evalExpr e2 mem := by
  have heq := Expr.beq_eq e1 e2 h; subst heq; rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- Section 2: normalizeExpr preserves evalExpr (sorry -- nested inductive)
-- ══════════════════════════════════════════════════════════════════════════════

private theorem foldl_map_normalize (es : List Expr) (mem : Nat → Int) (symMem : Nat → Expr)
    (hpoint : ∀ e ∈ es, evalExpr (normalizeExpr e symMem) mem = evalExpr e mem) :
    ∀ acc, (es.map (fun e => normalizeExpr e symMem)).foldl (fun acc e => acc + evalExpr e mem) acc =
    es.foldl (fun acc e => acc + evalExpr e mem) acc := by
  induction es with
  | nil => intro acc; rfl
  | cons e rest ih =>
      intro acc
      simp only [List.map_cons, List.foldl_cons]
      rw [hpoint e (List.mem_cons_self ..)]
      exact ih (fun e' he' => hpoint e' (List.mem_cons_of_mem _ he')) (acc + evalExpr e mem)

theorem normalizeExpr_correct (e : Expr) (mem : Nat → Int) (symMem : Nat → Expr)
    (h : ∀ addr, evalExpr (symMem addr) mem = mem addr) :
    evalExpr (normalizeExpr e symMem) mem = evalExpr e mem := by
  match e with
  | .lit n => simp [normalizeExpr, evalExpr]
  | .var s i => simp [normalizeExpr, evalExpr]
  | .add e1 e2 =>
      have ih1 := normalizeExpr_correct e1 mem symMem h
      have ih2 := normalizeExpr_correct e2 mem symMem h
      simp only [normalizeExpr]
      cases h1 : normalizeExpr e1 symMem with
      | lit a =>
          rw [h1] at ih1; simp only [evalExpr] at ih1
          cases h2 : normalizeExpr e2 symMem with
          | lit b => rw [h2] at ih2; simp only [evalExpr] at ih2 ⊢; omega
          | var s i => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | add _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | mul _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | max _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | load _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | reduceSum _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
      | var s i => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | add _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | mul _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | max _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | load _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | reduceSum _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
  | .mul e1 e2 =>
      have ih1 := normalizeExpr_correct e1 mem symMem h
      have ih2 := normalizeExpr_correct e2 mem symMem h
      simp only [normalizeExpr]
      cases h1 : normalizeExpr e1 symMem with
      | lit a =>
          rw [h1] at ih1; simp only [evalExpr] at ih1
          cases h2 : normalizeExpr e2 symMem with
          | lit b => rw [h2] at ih2; simp only [evalExpr] at ih2 ⊢; rw [← ih1, ← ih2]
          | var s i => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | add _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | mul _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | max _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | load _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | reduceSum _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
      | var s i => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | add _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | mul _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | max _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | load _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | reduceSum _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
  | .max e1 e2 =>
      have ih1 := normalizeExpr_correct e1 mem symMem h
      have ih2 := normalizeExpr_correct e2 mem symMem h
      simp only [normalizeExpr]
      cases h1 : normalizeExpr e1 symMem with
      | lit a =>
          rw [h1] at ih1; simp only [evalExpr] at ih1
          cases h2 : normalizeExpr e2 symMem with
          | lit b => rw [h2] at ih2; simp only [evalExpr] at ih2 ⊢; rw [← ih1, ← ih2]
          | var s i => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | add _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | mul _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | max _ _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | load _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
          | reduceSum _ => rw [h2] at ih2; simp [evalExpr, ih1, ih2]
      | var s i => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | add _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | mul _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | max _ _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | load _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
      | reduceSum _ => rw [h1] at ih1; simp [evalExpr, ih1, ih2]
  | .reduceSum es =>
      simp only [normalizeExpr, evalExpr]
      exact foldl_map_normalize es mem symMem
        (fun e he => normalizeExpr_correct e mem symMem h) 0
  | .load addr =>
      have ih := normalizeExpr_correct addr mem symMem h
      simp only [normalizeExpr]
      cases hn : normalizeExpr addr symMem with
      | lit k => rw [hn] at ih; simp only [evalExpr] at ih ⊢; rw [← h, ← ih]
      | var s i => rw [hn] at ih; simp [evalExpr, ih]
      | add _ _ => rw [hn] at ih; simp [evalExpr, ih]
      | mul _ _ => rw [hn] at ih; simp [evalExpr, ih]
      | max _ _ => rw [hn] at ih; simp [evalExpr, ih]
      | load _ => rw [hn] at ih; simp [evalExpr, ih]
      | reduceSum _ => rw [hn] at ih; simp [evalExpr, ih]
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals (have := List.sizeOf_lt_of_mem (by assumption); omega)

-- ══════════════════════════════════════════════════════════════════════════════
-- Section 3: concreteMem helpers
-- ══════════════════════════════════════════════════════════════════════════════

def concreteMem (a b : List Int) : Nat → Int := layoutMemory a b

-- layoutMemory a b addr:
--   addr < n       => a.getD addr 0
--   n ≤ addr < 2n  => b.getD (addr-n) 0
--   2n ≤ addr      => 0
-- After simp [layoutMemory] with ha : k < a.length and the four show-facts,
-- the goal reduces to:
--   a.getD k 0 + b.getD k 0 = a.getD k 0 + b.getD k 0  (rfl)

theorem vectorAddSpecExpr_correct (a b : List Int) (pid bs i n : Nat)
    (hla : a.length = n) (hlb : b.length = n) (hi : pid * bs + i < n) :
    evalExpr (vectorAddSpecExpr pid bs i n) (concreteMem a b) =
    a.getD (pid * bs + i) 0 + b.getD (pid * bs + i) 0 := by
  simp only [vectorAddSpecExpr, evalExpr, concreteMem, layoutMemory]
  have ha : pid * bs + i < a.length := by omega
  have h1 : ¬ (n + pid * bs + i < a.length) := by omega
  have h2 : n + pid * bs + i < 2 * a.length := by omega
  have h3 : n + pid * bs + i - a.length = pid * bs + i := by omega
  rw [if_pos ha, if_neg h1, if_pos h2, h3]

theorem normalizeWithMem_correct (e : Expr) (a b : List Int) (n : Nat)
    (hla : a.length = n) (hlb : b.length = n) :
    evalExpr (normalizeWithMem e n) (concreteMem a b) =
    evalExpr e (concreteMem a b) := by
  unfold normalizeWithMem
  apply normalizeExpr_correct
  intro addr
  simp only [concreteMem, layoutMemory]
  by_cases h1 : addr < n <;> by_cases h2 : addr < 2 * n
  · simp only [if_pos h1, evalExpr]; simp [concreteMem, layoutMemory, ← hla, h1]
  · simp only [if_pos h1, evalExpr]; simp [concreteMem, layoutMemory, ← hla, h1]
  · simp only [if_neg h1, if_pos h2, evalExpr]
    simp [concreteMem, layoutMemory, ← hla, ← hlb, h1, h2]
  · simp only [if_neg h1, if_neg h2, evalExpr]
    have ha : ¬ addr < a.length := by omega
    have ha2 : ¬ addr < 2 * a.length := by omega
    rw [if_neg ha, if_neg ha2]


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 4: symCheck_sound (sorry)
-- ══════════════════════════════════════════════════════════════════════════════

-- vectorAddInitState faithful: maps a_base/b_base/c_base/bsize same as symVectorAddInitState
theorem initStates_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (vectorAddInitState a b pid bs gs)
      (symVectorAddInitState pid bs gs a.length)
      (concreteMem a b) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- hmem
    intro addr
    simp only [symVectorAddInitState, parsedInitState, evalExpr, concreteMem, layoutMemory,
               vectorAddInitState]
    by_cases h1 : addr < a.length <;> by_cases h2 : addr < 2 * a.length <;>
      simp [h1, h2, evalExpr, layoutMemory]
  · -- hsc: a_base/b_base/c_base/bsize all match
    intro v val hv
    simp only [vectorAddInitState] at hv
    split at hv <;> simp_all [TritonValue.scalar, symVectorAddInitState, evalExpr]
  · -- hten: no tensors
    intro v sh vals hv
    simp only [vectorAddInitState] at hv
    split at hv <;> simp_all
  · -- hnone
    intro v hv
    simp only [vectorAddInitState] at hv
    simp only [symVectorAddInitState]
    split at hv <;> simp_all

theorem symCheck_sound (K : TritonKernel) (pid bs gs n i : Nat)
    (hcheck : symCheckVectorAdd K pid bs gs n i = true) :
    ∀ (a b : List Int), a.length = n → b.length = n → pid * bs + i < n →
      MachineState.readMem (evalKernel K (vectorAddInitState a b pid bs gs))
        (2 * n + pid * bs + i) =
      a.getD (pid * bs + i) 0 + b.getD (pid * bs + i) 0 := by
  intro a b hla hlb hi
  simp only [symCheckVectorAdd] at hcheck
  have heval_eq : evalExpr
      (normalizeWithMem
        ((symEvalKernel K (symVectorAddInitState pid bs gs n)).memory
          (2 * n + pid * bs + i)) n)
      (concreteMem a b) =
      evalExpr (vectorAddSpecExpr pid bs i n) (concreteMem a b) :=
    beq_evalExpr _ _ _ hcheck
  rw [normalizeWithMem_correct _ a b n hla hlb] at heval_eq
  rw [vectorAddSpecExpr_correct a b pid bs i n hla hlb hi] at heval_eq
  have hfaithful := initStates_faithful a b pid bs gs
  have hsound := symEval_sound K
    (vectorAddInitState a b pid bs gs)
    (symVectorAddInitState pid bs gs n)
    (concreteMem a b)
    (by rwa [hla] at hfaithful)
    (2 * n + pid * bs + i)
  exact hsound.symm.trans heval_eq

-- ══════════════════════════════════════════════════════════════════════════════
-- Section 5: Expr.beq_false_ne
-- ══════════════════════════════════════════════════════════════════════════════

mutual
  def exprBeqRefl : (e : Expr) → Expr.beq e e = true
    | .lit _ => by simp [Expr.beq]
    | .var _ _ => by simp [Expr.beq]
    | .add e1 e2 => by simp [Expr.beq, exprBeqRefl e1, exprBeqRefl e2]
    | .mul e1 e2 => by simp [Expr.beq, exprBeqRefl e1, exprBeqRefl e2]
    | .max e1 e2 => by simp [Expr.beq, exprBeqRefl e1, exprBeqRefl e2]
    | .load e => by simp [Expr.beq, exprBeqRefl e]
    | .reduceSum es => by simp [Expr.beq, exprListBeqRefl es]
  def exprListBeqRefl : (es : List Expr) → ExprList.beq es es = true
    | [] => by simp [ExprList.beq]
    | e::es => by simp [ExprList.beq, exprBeqRefl e, exprListBeqRefl es]
end

theorem Expr.beq_false_ne (e1 e2 : Expr) (h : Expr.beq e1 e2 = false) : e1 ≠ e2 := by
  intro heq; subst heq; simp [exprBeqRefl e1] at h

-- ══════════════════════════════════════════════════════════════════════════════
-- Section 6: initStatesTutorial_faithful (sorry)
-- ══════════════════════════════════════════════════════════════════════════════

theorem initStatesTutorial_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (parsedInitState a b pid bs gs)
      (symVectorAddTutorialInitState pid bs gs a.length)
      (concreteMem a b) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- hmem
    intro addr
    simp only [symVectorAddTutorialInitState, parsedInitState, evalExpr, concreteMem, layoutMemory]
    by_cases h1 : addr < a.length <;> by_cases h2 : addr < 2 * a.length <;>
      simp [h1, h2, evalExpr, layoutMemory]
  · -- hsc: now symVectorAddTutorialInitState maps all 11 vars from parsedInitState
    intro v val hv
    simp only [parsedInitState] at hv
    -- after split: hv : some (scalar X) = some (scalar val) for matching vars
    -- simp_all [TritonValue.scalar] extracts val = X
    -- then simp [symVectorAddTutorialInitState, evalExpr] provides the witness
    split at hv <;> simp_all [TritonValue.scalar, symVectorAddTutorialInitState, evalExpr]
  · -- hten: no tensors in parsedInitState
    intro v sh vals hv
    simp only [parsedInitState] at hv
    split at hv <;> simp_all
  · -- hnone
    intro v hv
    simp only [parsedInitState] at hv
    simp only [symVectorAddTutorialInitState]
    split at hv <;> simp_all



-- ══════════════════════════════════════════════════════════════════════════════
-- Section 7: symCheckTutorial_sound
-- ══════════════════════════════════════════════════════════════════════════════

theorem symCheckTutorial_sound (K : TritonKernel) (pid bs gs n i : Nat)
    (hcheck : symCheckVectorAddTutorial K pid bs gs n i = true) :
    ∀ (a b : List Int), a.length = n → b.length = n → pid * bs + i < n →
      MachineState.readMem (evalKernel K (parsedInitState a b pid bs gs))
        (2 * n + pid * bs + i) =
      a.getD (pid * bs + i) 0 + b.getD (pid * bs + i) 0 := by
  intro a b hla hlb hi
  simp only [symCheckVectorAddTutorial] at hcheck
  have heval_eq : evalExpr
      (normalizeWithMem
        ((symEvalKernel K (symVectorAddTutorialInitState pid bs gs n)).memory
          (2 * n + pid * bs + i)) n)
      (concreteMem a b) =
      evalExpr (vectorAddSpecExpr pid bs i n) (concreteMem a b) :=
    beq_evalExpr _ _ _ hcheck
  rw [normalizeWithMem_correct _ a b n hla hlb] at heval_eq
  rw [vectorAddSpecExpr_correct a b pid bs i n hla hlb hi] at heval_eq
  have hfaithful := initStatesTutorial_faithful a b pid bs gs
  have hsound := symEval_sound K
    (parsedInitState a b pid bs gs)
    (symVectorAddTutorialInitState pid bs gs n)
    (concreteMem a b)
    (by rwa [hla] at hfaithful)
    (2 * n + pid * bs + i)
  exact hsound.symm.trans heval_eq

#check @symCheck_sound
#check @symCheckTutorial_sound

end Trident
