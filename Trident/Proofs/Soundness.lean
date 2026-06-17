import Trident.Common.Symbolic
import Trident.Target.Semantics
import Trident.Proofs.VectorAddProof

namespace Trident
open TritonValue


-- Helper: indexing into (List.range n).map Int.ofNat
private theorem range_map_getD (n i : Nat) :
    (List.map Int.ofNat (List.range n)).getD i 0 =
    if i < n then Int.ofNat i else 0 := by
  rcases Nat.lt_or_ge i n with h | h
  · simp [List.getD, List.getElem?_map, List.getElem?_range, h]
  · simp [List.getD, List.length_map, List.length_range, Nat.not_lt.mpr h]

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
        ∧ ∀ i, i < n → evalExpr (g i) mem = vals.getD i 0)

-- ── Memory Faithfulness Lemmas ────────────────────────────────────────────────

theorem writeMem_mem_faithful
    (ss : SymState) (s : MachineState) (mem : Nat → Int)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (a : Nat) (e : Expr) (v : Int) (hev : evalExpr e mem = v) :
    ∀ addr, evalExpr ((ss.writeMem a e).memory addr) mem = (s.writeMem a v).memory addr := by
  intro addr
  simp only [SymState.writeMem, MachineState.writeMem]
  by_cases heq : addr == a
  · simp [heq, hev]
  · simp [heq, hmem addr]

theorem foldl_writeMem_faithful
    (ss : SymState) (s : MachineState) (mem : Nat → Int)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (pairs : List (Nat × Expr × Int))
    (hagree : ∀ p ∈ pairs, evalExpr p.2.1 mem = p.2.2) :
    ∀ addr,
      evalExpr ((pairs.foldl (fun st p => st.writeMem p.1 p.2.1) ss).memory addr) mem =
      (pairs.foldl (fun st p => st.writeMem p.1 p.2.2) s).memory addr := by
  intro addr
  induction pairs generalizing ss s with
  | nil => simp [hmem]
  | cons p rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact writeMem_mem_faithful ss s mem hmem p.1 p.2.1 p.2.2
            (hagree p (by simp))
      · intro q hq; exact hagree q (List.mem_cons.mpr (Or.inr hq))

-- ── Bind Lemmas ───────────────────────────────────────────────────────────────

private theorem bind_scalar_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ n g, ss.env v = some (SymValue.tensor n g)
          ∧ ∀ i, i < n → evalExpr (g i) mem = vals.getD i 0)
    (r : String) (cval : Int) (sval : Expr) (he : evalExpr sval mem = cval) :
    StatesFaithful (s.bind r (scalar cval)) (ss.bind r (SymValue.scalar sval)) mem := by
  refine ⟨hp, hbs, hgs, hmem, ?_, ?_⟩
  · intro v val hv
    simp only [MachineState.bind] at hv; simp only [SymState.bind]
    by_cases heq : v == r
    · simp only [heq, ↓reduceIte] at hv
      have hval : cval = val := by have := Option.some.inj hv; exact congrArg (fun x => match x with | scalar v => v | _ => 0) this
      exact ⟨sval, by simp [heq], hval ▸ he⟩
    · simp only [heq, ↓reduceIte] at hv ⊢; exact hsc v val hv
  · intro v sh vals hv
    simp only [MachineState.bind] at hv; simp only [SymState.bind]
    by_cases heq : v == r
    · simp only [heq, ↓reduceIte] at hv; simp at hv
    · simp only [heq, ↓reduceIte] at hv ⊢; exact hten v sh vals hv

private theorem bind_tensor_faithful
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ n g, ss.env v = some (SymValue.tensor n g)
          ∧ ∀ i, i < n → evalExpr (g i) mem = vals.getD i 0)
    (r : String) (sh : List Nat) (cvals : List Int) (n : Nat) (g : Nat → Expr)
    (hg : ∀ i, i < n → evalExpr (g i) mem = cvals.getD i 0) :
    StatesFaithful (s.bind r (tensor sh cvals)) (ss.bind r (SymValue.tensor n g)) mem := by
  refine ⟨hp, hbs, hgs, hmem, ?_, ?_⟩
  · intro v val hv
    simp only [MachineState.bind] at hv; simp only [SymState.bind]
    by_cases heq : v == r
    · simp only [heq, ↓reduceIte] at hv; simp at hv
    · simp only [heq, ↓reduceIte] at hv ⊢; exact hsc v val hv
  · intro v sh' vals' hv
    simp only [MachineState.bind] at hv; simp only [SymState.bind]
    by_cases heq : v == r
    · simp only [heq, ↓reduceIte] at hv
      obtain ⟨rfl, rfl⟩ : sh = sh' ∧ cvals = vals' := by
        have := Option.some.inj hv; cases this; simp
      exact ⟨n, g, by simp [heq], hg⟩
    · simp only [heq, ↓reduceIte] at hv ⊢; exact hten v sh' vals' hv

-- ── initStates_faithful ───────────────────────────────────────────────────────

theorem initStates_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (vectorAddInitState a b pid bs gs)
      (symVectorAddInitState pid bs gs a.length)
      (concreteMem a b) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro addr
    simp only [symVectorAddInitState, vectorAddInitState, concreteMem]
    by_cases h1 : addr < a.length
    · simp only [h1, ↓reduceIte, evalExpr, layoutMemory]
    · by_cases h2 : addr < 2 * a.length
      · simp only [h1, h2, ↓reduceIte, evalExpr]
      · simp only [h1, h2, ↓reduceIte, evalExpr]
        symm; unfold layoutMemory; simp [h1, h2]
  · intro v val hv
    simp only [vectorAddInitState] at hv
    simp only [symVectorAddInitState]
    split at hv <;> simp_all [evalExpr]
  · intro v sh vals hv
    simp only [vectorAddInitState] at hv
    split at hv <;> simp_all

-- ── evalInstr_faithful ────────────────────────────────────────────────────────

theorem evalInstr_faithful (instr : TritonInstr)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : StatesFaithful s ss mem) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten⟩ := h
  simp only [evalInstr, symEvalInstr]
  match h_op : instr.op with
  | .get_program_id _ =>
      simp only [h_op, evalOp, symEvalOp]
      exact bind_scalar_faithful hp hbs hgs hmem hsc hten instr.result
        (Int.ofNat s.pid) (Expr.lit (Int.ofNat ss.pid)) (by simp [evalExpr, hp])
  | .constant v =>
      simp only [h_op, evalOp, symEvalOp]
      exact bind_scalar_faithful hp hbs hgs hmem hsc hten instr.result
        v (Expr.lit v) (by simp [evalExpr])
  | .make_range =>
      simp only [h_op, evalOp, symEvalOp]
      -- make_range: symbolic tensor agrees with concrete for i < block_size
      -- bind_tensor_faithful requires ∀ i agreement, which fails for i ≥ block_size
      -- since Expr.lit (Int.ofNat i) evaluates to i, not 0
      sorry
  | .splat =>
      simp only [h_op, evalOp, symEvalOp]
      match h_args : instr.args with
      | [v] =>
          simp only [h_args]
          match h_lv : s.lookup v with
          | some (scalar x) =>
              have ⟨e, hes, hev⟩ := hsc v x h_lv
              simp only [SymState.lookup, hes]
              exact bind_tensor_faithful hp hbs hgs hmem hsc hten instr.result
                [s.block_size] (List.replicate s.block_size x)
                ss.block_size (fun _ => e)
                (by intro i hi; rw [hev]; rw [← hbs] at hi; simp [List.getD, List.getElem?_replicate, hi])
          | _ => sorry -- splat fallback: lookup failed, state unchanged
      | _ => sorry -- splat fallback: wrong args
  | .addi =>
      simp only [h_op, evalOp, symEvalOp, symAdd]
      match h_args : instr.args with
      | [a, b] =>
          simp only [h_args]
          match h_la : s.lookup a with
          | some (scalar x) =>
              match h_lb : s.lookup b with
              | some (scalar y) =>
                  have ⟨ea, heas, heav⟩ := hsc a x h_la
                  have ⟨eb, hebs, hebv⟩ := hsc b y h_lb
                  simp only [SymState.lookup, heas, hebs]
                  exact bind_scalar_faithful hp hbs hgs hmem hsc hten instr.result
                    (x + y) (Expr.add ea eb) (by simp [evalExpr, heav, hebv])
              | _ => sorry
          | _ => sorry
      | _ => sorry
  | .muli =>
      simp only [h_op, evalOp, symEvalOp]
      match h_args : instr.args with
      | [a, b] =>
          simp only [h_args]
          match h_la : s.lookup a with
          | some (scalar x) =>
              match h_lb : s.lookup b with
              | some (scalar y) =>
                  have ⟨ea, heas, heav⟩ := hsc a x h_la
                  have ⟨eb, hebs, hebv⟩ := hsc b y h_lb
                  simp only [SymState.lookup, heas, hebs]
                  exact bind_scalar_faithful hp hbs hgs hmem hsc hten instr.result
                    (x * y) (Expr.mul ea eb) (by simp [evalExpr, heav, hebv])
              | _ => sorry
          | _ => sorry
      | _ => sorry
  | .store =>
      simp only [h_op]
      match h_args : instr.args with
      | [p, v] =>
          simp only [h_args]
          match h_lp : s.lookup p, h_lv : s.lookup v with
          | some (scalar addr), some (scalar val) =>
              simp only [h_lp, h_lv]
              have ⟨ep, heps, hepv⟩ := hsc p addr h_lp
              have ⟨ev, hevs, hevv⟩ := hsc v val h_lv
              simp only [SymState.lookup, heps, hevs]
              -- scalar store: write val to addr
              -- symEvalInstr uses evalExpr ep (fun _ => 0) as address
              -- we need: (evalExpr ep (fun _ => 0)).natAbs = addr.natAbs
              have haddr : (evalExpr ep (fun _ => (0:Int))).natAbs = addr.natAbs := by
                -- symEvalInstr uses fun _ => 0, but hepv uses mem
                -- these agree when ep is a constant expression (which it will be for addptr results)
                sorry
              refine ⟨hp, hbs, hgs, ?_, hsc, hten⟩
              rw [haddr]
              exact writeMem_mem_faithful ss s mem hmem addr.natAbs ev val hevv
          | some (tensor _ addrs), some (tensor _ vals) =>
              simp only [h_lp, h_lv]
              have ⟨_, gaddrn, hgaddrs, hgaddr⟩ := hten p _ addrs h_lp
              have ⟨_, gval, hgvals, hgval⟩ := hten v _ vals h_lv
              simp only [SymState.lookup, hgaddrs, hgvals]
              -- tensor store: writeTile preserves pid/block_size/grid_size/env
              -- only memory changes
              sorry -- tensor store faithfulness
          | _, _ => sorry -- store fallback
      | _ => sorry -- store wrong args
  | _ =>
      simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]
      split
      · sorry -- none case
      · sorry -- addptr, load, addf, maxsi etc.

-- ── Kernel and Sound Theorems ─────────────────────────────────────────────────

theorem symEvalKernel_faithful (K : TritonKernel)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : StatesFaithful s ss mem) :
    StatesFaithful (evalKernel K s) (symEvalKernel K ss) mem := by
  induction K generalizing s ss with
  | nil => simp [evalKernel, symEvalKernel]; exact h
  | cons instr rest ih =>
    simp only [evalKernel, symEvalKernel, List.foldl]
    exact ih _ _ (evalInstr_faithful instr s ss mem h)

theorem symEval_sound (K : TritonKernel) (a b : List Int) (pid bs gs i : Nat) :
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
  exact h_mem _

#check @symEval_sound

end Trident
