import Trident.Common.Symbolic
import Trident.Target.Semantics
import Trident.Proofs.VectorAddProof

namespace Trident
open TritonValue

private theorem range_map_getD (n i : Nat) :
    (List.map Int.ofNat (List.range n)).getD i 0 =
    if i < n then Int.ofNat i else 0 := by
  rcases Nat.lt_or_ge i n with h | h
  · simp [List.getD, List.getElem?_map, List.getElem?_range, h]
  · simp [List.getD, List.length_map, List.length_range, Nat.not_lt.mpr h]

private theorem map_add_getD (ys : List Int) (x : Int) (i : Nat) (h : i < ys.length) :
    (ys.map (· + x)).getD i 0 = ys.getD i 0 + x := by
  simp [List.getD, List.getElem?_map, h]

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
  ∧ (∀ v, s.env v = none → ss.env v = none)

def Expr.isConcrete : Expr → Bool
  | .lit _      => true
  | .var _ _    => false
  | .load _     => false
  | .add e1 e2  => e1.isConcrete && e2.isConcrete
  | .mul e1 e2  => e1.isConcrete && e2.isConcrete
  | .max e1 e2  => e1.isConcrete && e2.isConcrete
  | .reduceSum _ => false

theorem evalExpr_concrete (e : Expr) (mem1 mem2 : Nat → Int)
    (h : e.isConcrete = true) :
    evalExpr e mem1 = evalExpr e mem2 := by
  match e with
  | .lit n => simp [evalExpr]
  | .var _ _ => simp [Expr.isConcrete] at h
  | .load _ => simp [Expr.isConcrete] at h
  | .add e1 e2 =>
      simp [Expr.isConcrete, Bool.and_eq_true] at h
      simp [evalExpr, evalExpr_concrete e1 mem1 mem2 h.1,
                      evalExpr_concrete e2 mem1 mem2 h.2]
  | .mul e1 e2 =>
      simp [Expr.isConcrete, Bool.and_eq_true] at h
      simp [evalExpr, evalExpr_concrete e1 mem1 mem2 h.1,
                      evalExpr_concrete e2 mem1 mem2 h.2]
  | .max e1 e2 =>
      simp [Expr.isConcrete, Bool.and_eq_true] at h
      simp [evalExpr, evalExpr_concrete e1 mem1 mem2 h.1,
                      evalExpr_concrete e2 mem1 mem2 h.2]
  | .reduceSum _ => simp [Expr.isConcrete] at h

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
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (r : String) (cval : Int) (sval : Expr) (he : evalExpr sval mem = cval) :
    StatesFaithful (s.bind r (scalar cval)) (ss.bind r (SymValue.scalar sval)) mem := by
  refine ⟨hp, hbs, hgs, hmem, ?_, ?_, ?_⟩
  · intro v val hv
    simp only [MachineState.bind] at hv; simp only [SymState.bind]
    by_cases heq : v == r
    · simp only [heq, ↓reduceIte] at hv
      have hval : cval = val := by
        have := Option.some.inj hv
        exact congrArg (fun x => match x with | scalar v => v | _ => 0) this
      exact ⟨sval, by simp [heq], hval ▸ he⟩
    · simp only [heq, ↓reduceIte] at hv ⊢; exact hsc v val hv
  · intro v sh vals hv
    simp only [MachineState.bind] at hv; simp only [SymState.bind]
    by_cases heq : v == r
    · simp only [heq, ↓reduceIte] at hv; simp at hv
    · simp only [heq, ↓reduceIte] at hv ⊢; exact hten v sh vals hv
  · intro v hv
    simp only [MachineState.bind] at hv; simp only [SymState.bind]
    by_cases heq : v == r
    · simp only [heq, ↓reduceIte] at hv; simp at hv
    · simp only [heq, ↓reduceIte] at hv ⊢; exact hnone v hv

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
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (r : String) (sh : List Nat) (cvals : List Int) (n : Nat) (g : Nat → Expr)
    (hg : ∀ i, i < n → evalExpr (g i) mem = cvals.getD i 0) :
    StatesFaithful (s.bind r (tensor sh cvals)) (ss.bind r (SymValue.tensor n g)) mem := by
  refine ⟨hp, hbs, hgs, hmem, ?_, ?_, ?_⟩
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
  · intro v hv
    simp only [MachineState.bind] at hv; simp only [SymState.bind]
    by_cases heq : v == r
    · simp only [heq, ↓reduceIte] at hv; simp at hv
    · simp only [heq, ↓reduceIte] at hv ⊢; exact hnone v hv

theorem initStates_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (vectorAddInitState a b pid bs gs)
      (symVectorAddInitState pid bs gs a.length)
      (concreteMem a b) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
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
  · intro v hv
    simp only [vectorAddInitState] at hv
    simp only [symVectorAddInitState]
    split <;> simp_all

-- Derive ss.lookup v = none from s.lookup v = none using hnone
private theorem ss_none_of_none {s : MachineState} {ss : SymState}
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (v : String) (hv : s.lookup v = none) : ss.env v = none :=
  hnone v hv

theorem evalInstr_faithful (instr : TritonInstr)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : StatesFaithful s ss mem) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := h
  have hf : StatesFaithful s ss mem := ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩
  match h_op : instr.op with
  | .get_program_id _ =>
      simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]
      exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone instr.result
        (Int.ofNat s.pid) (Expr.lit (Int.ofNat ss.pid)) (by simp [evalExpr, hp])
  | .constant v =>
      simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]
      exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone instr.result
        v (Expr.lit v) (by simp [evalExpr])
  | .make_range =>
      simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]
      refine bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result
        [s.block_size] ((List.range s.block_size).map Int.ofNat)
        ss.block_size (fun i => Expr.lit (Int.ofNat i)) ?_
      intro i hi
      simp only [evalExpr]
      rw [range_map_getD]
      simp only [← hbs] at hi
      simp [hi]
  | .splat =>
      match h_args : instr.args with
      | [] =>
          simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp]; exact hf
      | [v] =>
          cases h_lv : s.lookup v with
          | none =>
              have h_env_none : s.env v = none := h_lv
              have hss : ss.env v = none := hnone v h_lv
              simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp,
                         MachineState.lookup, h_env_none, SymState.lookup, hss]
              exact hf
          | some val => cases val with
            | scalar x =>
                have h_env_sc : s.env v = some (scalar x) := h_lv
                have ⟨e, hes, hev⟩ := hsc v x h_lv
                simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp,
                           MachineState.lookup, h_env_sc, SymState.lookup, hes]
                exact bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result
                  [s.block_size] (List.replicate s.block_size x)
                  ss.block_size (fun _ => e)
                  (by intro i hi; rw [hev]; rw [← hbs] at hi
                      simp [List.getD, List.getElem?_replicate, hi])
            | tensor sh vals =>
                have h_env_ten : s.env v = some (tensor sh vals) := h_lv
                have ⟨n, g, hng, _⟩ := hten v sh vals h_lv
                simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp,
                           MachineState.lookup, h_env_ten, SymState.lookup, hng]
                exact hf
      | _ :: _ :: _ =>
          simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp]; exact hf
  | .addi =>
      simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, symAdd]
      match h_args : instr.args with
      | [a, b] =>
          simp only [h_args]
          cases h_la : s.lookup a with
          | none =>
              simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp, symAdd,
                         MachineState.lookup, h_la]
              have hss : ss.env a = none := ss_none_of_none hnone a h_la
              simp only [SymState.lookup, hss]; exact hf
          | some va => cases va with
            | scalar x =>
                cases h_lb : s.lookup b with
                | none =>
                    have ⟨ea, heas, _⟩ := hsc a x h_la
                    simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp, symAdd,
                               MachineState.lookup, h_la, h_lb, SymState.lookup, heas]
                    have hss : ss.env b = none := ss_none_of_none hnone b h_lb
                    simp only [hss]; exact hf
                | some vb => cases vb with
                  | scalar y =>
                      have ⟨ea, heas, heav⟩ := hsc a x h_la
                      have ⟨eb, hebs, hebv⟩ := hsc b y h_lb
                      simp only [MachineState.lookup, h_la, h_lb, SymState.lookup, heas, hebs]
                      exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone instr.result
                        (x + y) (Expr.add ea eb) (by simp [evalExpr, heav, hebv])
                  | tensor sh vals =>
                      have h_env_a : s.env a = some (scalar x) := h_la
                      have h_env_b : s.env b = some (tensor sh vals) := h_lb
                      have ⟨ea, heas, _⟩ := hsc a x h_la
                      have ⟨nb, gb, hgb, _⟩ := hten b sh vals h_lb
                      simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp, symAdd,
                                 MachineState.lookup, h_env_a, h_env_b, SymState.lookup, heas, hgb]
                      sorry -- addi scalar×tensor: needs nb = vals.length in StatesFaithful
            | tensor sh_a vals_a =>
                have h_env_a : s.env a = some (tensor sh_a vals_a) := h_la
                have ⟨na, ga, hga, _⟩ := hten a sh_a vals_a h_la
                simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp, symAdd,
                           MachineState.lookup, h_env_a, SymState.lookup, hga]
                sorry -- fallback: needs bind_tensor_faithful
      | [] =>
          simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, symAdd]; exact hf
      | [_] =>
          simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, symAdd]; exact hf
      | _ :: _ :: _ :: _ =>
          simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, symAdd]; exact hf
  | .muli =>
      simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]
      match h_args : instr.args with
      | [a, b] =>
          simp only [h_args]
          cases h_la : s.lookup a with
          | none =>
              simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp,
                         MachineState.lookup, h_la]
              have hss : ss.env a = none := ss_none_of_none hnone a h_la
              simp only [SymState.lookup, hss]; exact hf
          | some va => cases va with
            | scalar x =>
                cases h_lb : s.lookup b with
                | none =>
                    have ⟨ea, heas, _⟩ := hsc a x h_la
                    simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp,
                               MachineState.lookup, h_la, h_lb, SymState.lookup, heas]
                    have hss : ss.env b = none := ss_none_of_none hnone b h_lb
                    simp only [hss]; exact hf
                | some vb => cases vb with
                  | scalar y =>
                      have ⟨ea, heas, heav⟩ := hsc a x h_la
                      have ⟨eb, hebs, hebv⟩ := hsc b y h_lb
                      simp only [MachineState.lookup, h_la, h_lb, SymState.lookup, heas, hebs]
                      exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone instr.result
                        (x * y) (Expr.mul ea eb) (by simp [evalExpr, heav, hebv])
                  | tensor _ _ =>
                      have ⟨ea, heas, _⟩ := hsc a x h_la
                      simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp,
                                 MachineState.lookup, h_la, h_lb, SymState.lookup, heas]
                      sorry -- fallback: needs bind_tensor_faithful
            | tensor sh_a vals_a =>
                have h_env_a : s.env a = some (tensor sh_a vals_a) := h_la
                have ⟨na, ga, hga, _⟩ := hten a sh_a vals_a h_la
                simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp,
                           MachineState.lookup, h_env_a, SymState.lookup, hga]
                sorry -- muli a-tensor: needs bind_tensor_faithful
      | [] =>
          simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]; exact hf
      | [_] =>
          simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]; exact hf
      | _ :: _ :: _ :: _ =>
          simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]; exact hf
  | .store =>
      match h_args : instr.args with
      | [p, v] =>
          cases h_lp : s.lookup p with
          | none =>
              have h_env_p_none : s.env p = none := h_lp
              have hss_p : ss.env p = none := hnone p h_lp
              simp only [evalInstr, symEvalInstr, h_op, h_args, MachineState.lookup,
                         h_env_p_none, SymState.lookup, hss_p]
              exact hf
          | some vp => cases vp with
            | scalar addr =>
                cases h_lv : s.lookup v with
                | none =>
                    have h_env_v_none : s.env v = none := h_lv
                    have ⟨ep, heps, _⟩ := hsc p addr h_lp
                    have h_env_p_sc : s.env p = some (scalar addr) := h_lp
                    simp only [evalInstr, symEvalInstr, h_op, h_args, MachineState.lookup,
                               h_env_p_sc, h_env_v_none, SymState.lookup, heps]
                    have hss_v : ss.env v = none := hnone v h_lv
                    simp only [hss_v]; exact hf
                | some vv => cases vv with
                  | scalar val =>
                      have h_env_p_sc : s.env p = some (scalar addr) := h_lp
                      have h_env_v_sc : s.env v = some (scalar val) := h_lv
                      have ⟨ep, heps, hepv⟩ := hsc p addr h_lp
                      have ⟨ev, hevs, hevv⟩ := hsc v val h_lv
                      simp only [evalInstr, symEvalInstr, h_op, h_args, MachineState.lookup,
                                 h_env_p_sc, h_env_v_sc, SymState.lookup, heps, hevs]
                      refine ⟨hp, hbs, hgs, ?_, hsc, hten, hnone⟩
                      sorry -- store address: evalExpr ep (fun _ => 0) = addr
                  | tensor _ _ =>
                      have h_env_p_sc : s.env p = some (scalar addr) := h_lp
                      have ⟨ep, heps, _⟩ := hsc p addr h_lp
                      have h_env_v_ten : s.env v = some (tensor _ _) := h_lv
                      simp only [evalInstr, symEvalInstr, h_op, h_args, MachineState.lookup,
                                 h_env_p_sc, h_lv, SymState.lookup, heps]
                      sorry -- store v-tensor fallback
            | tensor sh_p vals_p =>
                have h_env_p_ten : s.env p = some (tensor sh_p vals_p) := h_lp
                have ⟨np, gp, hgp, _⟩ := hten p sh_p vals_p h_lp
                simp only [evalInstr, symEvalInstr, h_op, h_args, MachineState.lookup,
                           h_env_p_ten, SymState.lookup, hgp]
                sorry -- store p-tensor: symEvalInstr produces writeTile
      | _ =>
          sorry -- store wrong args
  | _ =>
      simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]
      split
      · sorry -- catch-all none case
      · sorry -- remaining ops: addptr, load, addf, maxsi etc.

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
