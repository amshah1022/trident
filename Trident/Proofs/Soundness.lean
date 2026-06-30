import Trident.Common.Symbolic
import Trident.Target.Semantics
import Trident.Proofs.VectorAddProof
import Trident.Common.Equiv


set_option linter.unusedSimpArgs false


namespace Trident
open TritonValue


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 1: Core definitions
-- ══════════════════════════════════════════════════════════════════════════════


-- The central invariant: machine state and symbolic state agree on memory and
-- every bound variable, under interpretation by `mem`.
def StatesFaithful (s : MachineState) (ss : SymState) (mem : Nat → Int) : Prop :=
 s.pid = ss.pid
 ∧ s.block_size = ss.block_size
 ∧ s.grid_size = ss.grid_size
 ∧ (∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
 ∧ (∀ v val, s.env v = some (scalar val) →
     ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
 ∧ (∀ v sh vals, s.env v = some (tensor sh vals) →
     ∃ g, ss.env v = some (SymValue.tensor vals.length g)
       ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
 ∧ (∀ v, s.env v = none → ss.env v = none)


-- Concreteness predicate: expression does not read from symbolic memory
def Expr.isConcrete : Expr → Bool
 | .lit _       => true
 | .var _ _     => false
 | .load _      => false
 | .add e1 e2   => e1.isConcrete && e2.isConcrete
 | .mul e1 e2   => e1.isConcrete && e2.isConcrete
 | .max e1 e2   => e1.isConcrete && e2.isConcrete
 | .reduceSum _ => false


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 2: Expression and list lemmas
-- ══════════════════════════════════════════════════════════════════════════════


-- Concrete expressions are memory-independent
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


-- (List.range n).map ofNat getD
private theorem range_map_getD (n i : Nat) :
   (List.map Int.ofNat (List.range n)).getD i 0 =
   if i < n then Int.ofNat i else 0 := by
 rcases Nat.lt_or_ge i n with h | h
 · simp [List.getD, List.getElem?_map, List.getElem?_range, h]
 · simp [List.getD, List.length_map, List.length_range, Nat.not_lt.mpr h]


-- map (· + x) getD
private theorem map_add_getD (ys : List Int) (x : Int) (i : Nat)
   (h : i < ys.length) :
   (ys.map (· + x)).getD i 0 = ys.getD i 0 + x := by
 simp [List.getD, List.getElem?_map, h]


-- (xs.zip ys).map (fst + snd) getD, index in bounds for both
-- ── DESIGN DECISION (recorded 2026-06-29) ────────────────────────────────────
-- Elementwise tensor ops (addi/muli/addf/... tensor+tensor) currently MISMATCH
-- between concrete and symbolic evaluators:
--   concrete (Semantics.lean) guards on SHAPE equality  (sh == sh2)
--   symbolic (Symbolic.lean symAdd/symMul) has NO guard; binds with first length
-- This is a genuine faithfulness gap for shape-mismatched operands.
-- RESOLUTION (queued, do FIRST next session — edits trusted models):
--   Length-guard BOTH evaluators (elementwise faithfulness depends on element
--   count, not shape). Sound for well-typed TTIR where shape-match <=> length-match.
--   Add shape/length-compatibility validation to the PARSER as an ingest gate, so
--   the soundness theorem assumes well-typed input. Then prove addi/muli
--   tensor+tensor faithful uniformly (no per-kernel obligation).
-- The list helper below (zip_add_getD) is guard-independent and already validated.
-- ──────────────────────────────────────────────────────────────────────────────

-- (xs.zip ys).map (fst+snd) indexed = xs[i] + ys[i], by structural induction.
-- Guard-independent; used by the addi/addf tensor+tensor faithfulness proofs.
theorem zip_add_getD (a b : List Int) (i : Nat)
    (hi : i < a.length) (hab : a.length = b.length) :
    ((a.zip b).map (fun p => p.fst + p.snd)).getD i 0 = a.getD i 0 + b.getD i 0 := by
  induction a generalizing b i with
  | nil => simp at hi
  | cons x xs ih =>
    cases b with
    | nil => simp at hab
    | cons y ys =>
      cases i with
      | zero => simp [List.zip_cons_cons]
      | succ j =>
        simp only [List.zip_cons_cons, List.map_cons, List.getD_cons_succ]
        exact ih ys j (by simpa using hi) (by simpa using hab)

private theorem zipWith_add_getD' (a b : List Int) (i : Nat)
   (ha : i < a.length) (hb : i < b.length) :
   ((a.zip b).map (fun p => p.fst + p.snd)).getD i 0 =
   a.getD i 0 + b.getD i 0 := by
 have hzip : i < (a.zip b).length := by simp [List.length_zip]; omega
 have hmap : i < ((a.zip b).map (fun p : Int × Int => p.fst + p.snd)).length := by simp [List.length_zip]; omega
 rw [show ((a.zip b).map (fun p => p.fst + p.snd)).getD i 0 =
     ((a.zip b).map (fun p => p.fst + p.snd))[i] from by
   simp [List.getD, List.getElem?_eq_getElem hmap]]
 rw [show a.getD i 0 = a[i] from by simp [List.getD, List.getElem?_eq_getElem ha]]
 rw [show b.getD i 0 = b[i] from by simp [List.getD, List.getElem?_eq_getElem hb]]
 simp [List.getElem_map, List.getElem_zip]


-- filterMap that keeps all elements (all masks nonzero) collapses to zip
theorem filterMap_kept_eq_zip
   (addrs vals masks : List Int) (hlen_av : addrs.length = vals.length)
   (hlen_am : addrs.length = masks.length)
   (hall : ∀ i, i < masks.length → masks.getD i 0 ≠ 0) :
   ((addrs.zip vals).zip masks).filterMap (fun (p : (Int × Int) × Int) =>
     if p.2 != 0 then some p.1 else none) = addrs.zip vals := by
 induction addrs generalizing vals masks with
 | nil => simp
 | cons a as ih =>
     cases vals with
     | nil => simp at hlen_av
     | cons v vs =>
         cases masks with
         | nil => simp at hlen_am
         | cons mk mks =>
             simp only [List.zip_cons_cons, List.filterMap_cons]
             have hne : mk ≠ 0 := by
               have := hall 0 (by simp); simpa using this
             have hbne : (mk != 0) = true := by
               simp only [bne_iff_ne, ne_eq]; exact hne
             simp only [hbne, ↓reduceIte]
             simp only [List.length_cons] at hlen_av hlen_am
             congr 1
             exact ih vs mks (by omega) (by omega) (fun i hi => by
               have := hall (i + 1) (by simp; omega)
               simpa using this)


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 3: Memory faithfulness lemmas
-- ══════════════════════════════════════════════════════════════════════════════


-- env is unaffected by writeTile
private theorem writeTile_env
   (s : MachineState) (addrs : List Nat) (vals : List Int) (var : String) :
   (s.writeTile addrs vals).env var = s.env var := by
 simp only [MachineState.writeTile]
 induction addrs.zip vals generalizing s with
 | nil => simp
 | cons hd tl ih =>
     simp only [List.foldl]
     exact ih (s.writeMem hd.fst hd.snd)


-- env is unaffected by symbolic foldl writeMem
private theorem symFoldl_writeMem_env
   (n : Nat) (gAddr : Nat → Nat) (gVal : Nat → Expr) (ss : SymState) (var : String) :
   (List.foldl (fun st i => st.writeMem (gAddr i) (gVal i)) ss (List.range n)).env var
   = ss.env var := by
 induction List.range n generalizing ss with
 | nil => simp
 | cons hd tl ih =>
     simp only [List.foldl]
     exact ih (ss.writeMem (gAddr hd) (gVal hd))


-- Symbolic foldl writeMem leaves an unwritten address unchanged
theorem sym_foldl_writeMem_not_mem
   (n : Nat) (gAddrs gVals : Nat → Expr) (ss : SymState) (addr : Nat)
   (h : ∀ i, i < n → (evalExpr (gAddrs i) (fun _ => 0)).natAbs ≠ addr) :
   (List.foldl (fun st i =>
       st.writeMem (evalExpr (gAddrs i) (fun _ => 0)).natAbs (gVals i))
     ss (List.range n)).memory addr = ss.memory addr := by
 suffices ∀ (idxs : List Nat) (st : SymState),
     (∀ i, i ∈ idxs → (evalExpr (gAddrs i) (fun _ => 0)).natAbs ≠ addr) →
     (List.foldl (fun st i =>
         st.writeMem (evalExpr (gAddrs i) (fun _ => 0)).natAbs (gVals i))
       st idxs).memory addr = st.memory addr by
   exact this (List.range n) ss (fun i hi => h i (List.mem_range.mp hi))
 intro idxs
 induction idxs with
 | nil => simp
 | cons idx rest ih =>
     intro st hne
     simp only [List.foldl_cons]
     rw [ih _ (fun i hi => hne i (List.mem_cons_of_mem _ hi))]
     simp only [SymState.writeMem]
     have hne_idx := hne idx (List.Mem.head _)
     simp [show (addr == (evalExpr (gAddrs idx) (fun _ => 0)).natAbs) = false from by
       simp [BEq.beq, Nat.beq_eq, hne_idx.symm]]


-- Core induction: symbolic and concrete foldl writeMem stay in sync
-- when addresses are concrete (memory-independent)
private theorem fold_mem_faithful_aux
   (idxs : List Nat)
   (gAddrs gVals : Nat → Expr) (cAddrs cVals : Nat → Int) (mem : Nat → Int)
   (hconcrete : ∀ i, i ∈ idxs → (gAddrs i).isConcrete = true)
   (haddr : ∀ i, i ∈ idxs → evalExpr (gAddrs i) mem = cAddrs i)
   (hval  : ∀ i, i ∈ idxs → evalExpr (gVals i) mem = cVals i)
   (s : MachineState) (ss : SymState)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr) :
   ∀ addr, evalExpr
     ((List.foldl (fun st i =>
         st.writeMem (evalExpr (gAddrs i) (fun _ => 0)).natAbs (gVals i))
       ss idxs).memory addr) mem
     = (List.foldl (fun st i =>
         st.writeMem (cAddrs i).natAbs (cVals i))
       s idxs).memory addr := by
 induction idxs generalizing s ss with
 | nil => simpa
 | cons idx rest ih =>
     simp only [List.foldl_cons]
     have hconc     := hconcrete idx (List.Mem.head _)
     have haddr_idx := haddr idx (List.Mem.head _)
     have hval_idx  := hval  idx (List.Mem.head _)
     have haddr_zero : evalExpr (gAddrs idx) (fun _ => 0) = cAddrs idx := by
       rw [← haddr_idx]
       exact evalExpr_concrete (gAddrs idx) (fun _ => 0) mem hconc
     rw [haddr_zero]
     apply ih
     · intro i hi; exact hconcrete i (List.mem_cons_of_mem _ hi)
     · intro i hi; exact haddr     i (List.mem_cons_of_mem _ hi)
     · intro i hi; exact hval      i (List.mem_cons_of_mem _ hi)
     intro a
     simp only [SymState.writeMem, MachineState.writeMem]
     by_cases heq : a == (cAddrs idx).natAbs
     · simp [heq, hval_idx]
     · simp [heq, hmem a]


-- Public version ranging over List.range n
theorem range_fold_mem_faithful
   (n : Nat) (gAddrs gVals : Nat → Expr) (cAddrs cVals : Nat → Int) (mem : Nat → Int)
   (hconcrete : ∀ i, i < n → (gAddrs i).isConcrete = true)
   (haddr : ∀ i, i < n → evalExpr (gAddrs i) mem = cAddrs i)
   (hval  : ∀ i, i < n → evalExpr (gVals i) mem = cVals i) :
   ∀ (s : MachineState) (ss : SymState),
     (∀ addr, evalExpr (ss.memory addr) mem = s.memory addr) →
     ∀ addr, evalExpr
       ((List.foldl (fun st i =>
           st.writeMem (evalExpr (gAddrs i) (fun _ => 0)).natAbs (gVals i))
         ss (List.range n)).memory addr) mem
       = (List.foldl (fun st i =>
           st.writeMem (cAddrs i).natAbs (cVals i))
         s (List.range n)).memory addr := by
 intro s ss hmem addr
 apply fold_mem_faithful_aux (List.range n) gAddrs gVals cAddrs cVals mem
 · intro i hi; exact hconcrete i (List.mem_range.mp hi)
 · intro i hi; exact haddr     i (List.mem_range.mp hi)
 · intro i hi; exact hval      i (List.mem_range.mp hi)
 · exact hmem


-- ── Store bridging + projection helpers ──────────────────────────────────────

theorem zip_foldl_eq_range (s : MachineState) (addrs vals : List Int)
    (hlen : addrs.length = vals.length) :
    List.foldl (fun st (x : Nat × Int) => st.writeMem x.1 x.2) s
      ((addrs.map Int.natAbs).zip vals) =
    List.foldl (fun st i => st.writeMem (addrs.getD i 0).natAbs (vals.getD i 0))
      s (List.range addrs.length) := by
  induction addrs generalizing s vals with
  | nil => simp
  | cons a as ih =>
      cases vals with
      | nil => simp at hlen
      | cons val vs =>
          simp only [List.length_cons, List.map_cons, List.zip_cons_cons,
                     List.foldl_cons, List.getD_cons_zero, List.range_succ_eq_map,
                     List.foldl_map, List.getD_cons_succ]
          rw [ih (s.writeMem a.natAbs val) vs (by simpa using hlen)]

theorem con_foldl_pid (idxs : List Nat) (f : Nat → Nat) (g : Nat → Int) (s : MachineState) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) s idxs).pid = s.pid := by
  induction idxs generalizing s with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem con_foldl_bs (idxs : List Nat) (f : Nat → Nat) (g : Nat → Int) (s : MachineState) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) s idxs).block_size = s.block_size := by
  induction idxs generalizing s with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem con_foldl_gs (idxs : List Nat) (f : Nat → Nat) (g : Nat → Int) (s : MachineState) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) s idxs).grid_size = s.grid_size := by
  induction idxs generalizing s with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem con_foldl_env (idxs : List Nat) (f : Nat → Nat) (g : Nat → Int) (s : MachineState) (var : String) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) s idxs).env var = s.env var := by
  induction idxs generalizing s with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem sym_foldl_pid (idxs : List Nat) (f : Nat → Nat) (g : Nat → Expr) (ss : SymState) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) ss idxs).pid = ss.pid := by
  induction idxs generalizing ss with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem sym_foldl_bs (idxs : List Nat) (f : Nat → Nat) (g : Nat → Expr) (ss : SymState) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) ss idxs).block_size = ss.block_size := by
  induction idxs generalizing ss with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem sym_foldl_gs (idxs : List Nat) (f : Nat → Nat) (g : Nat → Expr) (ss : SymState) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) ss idxs).grid_size = ss.grid_size := by
  induction idxs generalizing ss with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl
theorem sym_foldl_env (idxs : List Nat) (f : Nat → Nat) (g : Nat → Expr) (ss : SymState) (var : String) :
    (List.foldl (fun st i => st.writeMem (f i) (g i)) ss idxs).env var = ss.env var := by
  induction idxs generalizing ss with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; rfl


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 4: StatesFaithful binding lemmas
-- ══════════════════════════════════════════════════════════════════════════════


private theorem bind_scalar_faithful
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor vals.length g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
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
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor vals.length g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone : ∀ v, s.env v = none → ss.env v = none)
   (r : String) (sh : List Nat) (cvals : List Int) (g : Nat → Expr)
   (hg : ∀ i, i < cvals.length → evalExpr (g i) mem = cvals.getD i 0) :
   StatesFaithful (s.bind r (tensor sh cvals))
                  (ss.bind r (SymValue.tensor cvals.length g)) mem := by
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
     exact ⟨g, by simp [heq], hg⟩
   · simp only [heq, ↓reduceIte] at hv ⊢; exact hten v sh' vals' hv
 · intro v hv
   simp only [MachineState.bind] at hv; simp only [SymState.bind]
   by_cases heq : v == r
   · simp only [heq, ↓reduceIte] at hv; simp at hv
   · simp only [heq, ↓reduceIte] at hv ⊢; exact hnone v hv


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 5: Per-opcode faithfulness helpers
--
-- load/store/cmpi_slt require side conditions that can't be established
-- generically in evalInstr_faithful (e.g. s.memory = mem, concrete addresses,
-- all masks nonzero). These helpers take those conditions as hypotheses and
-- are called directly from per-kernel step theorems.
-- ══════════════════════════════════════════════════════════════════════════════


-- load [ptr]: s.memory = mem
theorem load_tensor_faithful_when_memory_unchanged
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor vals.length g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone    : ∀ v, s.env v = none → ss.env v = none)
   (hmem_raw : s.memory = mem)
   (instr : TritonInstr) (p : String)
   (h_op : instr.op = .load) (h_args : instr.args = [p])
   (sh : List Nat) (addrs : List Int)
   (h_lp : s.lookup p = some (tensor sh addrs)) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  have h_envp : s.env p = some (tensor sh addrs) := h_lp
  obtain ⟨gp, hsp, hgp⟩ := hten p sh addrs h_envp
  simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, h_args,
             MachineState.lookup, SymState.lookup, h_envp, hsp,
             List.head?, Option.getD]
  have hlen : (addrs.map fun a => s.readMem a.natAbs).length = addrs.length := by simp
  rw [show addrs.length = (addrs.map fun a => s.readMem a.natAbs).length from hlen.symm]
  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
  intro i hi
  rw [hlen] at hi
  simp only [evalExpr]
  rw [hgp i hi, ← hmem_raw]
  simp only [MachineState.readMem]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  simp [hi]

theorem load_tensor_masked_faithful_when_all_true
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor vals.length g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone    : ∀ v, s.env v = none → ss.env v = none)
   (hmem_raw : s.memory = mem)
   (instr : TritonInstr) (p m : String)
   (h_op  : instr.op   = .load) (h_args : instr.args = [p, m])
   (sh : List Nat) (addrs masks : List Int)
   (h_lp  : s.lookup p = some (tensor sh addrs))
   (h_lm  : s.lookup m = some (tensor sh masks))
   (hlen  : addrs.length = masks.length)
   (hall  : ∀ i, i < masks.length → masks.getD i 0 ≠ 0) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  sorry

theorem store_tensor_faithful_when_memory_unchanged
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor vals.length g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone : ∀ v, s.env v = none → ss.env v = none)
   (instr : TritonInstr) (p v : String)
   (h_op  : instr.op   = .store) (h_args : instr.args = [p, v])
   (sh : List Nat) (addrs vals : List Int)
   (h_lp  : s.lookup p = some (tensor sh addrs))
   (h_lv  : s.lookup v = some (tensor sh vals))
   (hlen  : addrs.length = vals.length)
   (gp gv : Nat → Expr)
   (hgp       : ss.env p = some (SymValue.tensor addrs.length gp))
   (hgv_corr  : ss.env v = some (SymValue.tensor vals.length gv))
   (hconcrete : ∀ i, i < addrs.length → (gp i).isConcrete = true)
   (haddr     : ∀ i, i < addrs.length → evalExpr (gp i) mem = addrs.getD i 0)
   (hval      : ∀ i, i < addrs.length → evalExpr (gv i) mem = vals.getD i 0) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  have h_envp : s.env p = some (tensor sh addrs) := h_lp
  have h_envv : s.env v = some (tensor sh vals) := h_lv
  simp only [evalInstr, symEvalInstr, h_op, h_args,
             MachineState.lookup, SymState.lookup,
             h_envp, h_envv, hgp, hgv_corr]
  rw [MachineState.writeTile, zip_foldl_eq_range s addrs vals hlen]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sym_foldl_pid, con_foldl_pid]; exact hp
  · rw [sym_foldl_bs, con_foldl_bs]; exact hbs
  · rw [sym_foldl_gs, con_foldl_gs]; exact hgs
  · intro addr
    exact range_fold_mem_faithful addrs.length gp gv
      (fun i => addrs.getD i 0) (fun i => vals.getD i 0) mem
      hconcrete haddr hval s ss hmem addr
  · intro w val hw
    rw [con_foldl_env] at hw; rw [sym_foldl_env]; exact hsc w val hw
  · intro w sh' vals' hw
    rw [con_foldl_env] at hw; rw [sym_foldl_env]; exact hten w sh' vals' hw
  · intro w hw
    rw [con_foldl_env] at hw; rw [sym_foldl_env]; exact hnone w hw

theorem store_tensor_masked_faithful_when_all_true
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor vals.length g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone : ∀ v, s.env v = none → ss.env v = none)
   (instr : TritonInstr) (p v m : String)
   (h_op  : instr.op   = .store) (h_args : instr.args = [p, v, m])
   (sh : List Nat) (addrs vals masks : List Int)
   (h_lp    : s.lookup p = some (tensor sh addrs))
   (h_lv    : s.lookup v = some (tensor sh vals))
   (h_lm    : s.lookup m = some (tensor sh masks))
   (hlen_av : addrs.length = vals.length)
   (hlen_am : addrs.length = masks.length)
   (hall    : ∀ i, i < masks.length → masks.getD i 0 ≠ 0)
   (gp gv : Nat → Expr)
   (hgp       : ss.env p = some (SymValue.tensor addrs.length gp))
   (hgv_corr  : ss.env v = some (SymValue.tensor vals.length gv))
   (hconcrete : ∀ i, i < addrs.length → (gp i).isConcrete = true)
   (haddr     : ∀ i, i < addrs.length → evalExpr (gp i) mem = addrs.getD i 0)
   (hval      : ∀ i, i < addrs.length → evalExpr (gv i) mem = vals.getD i 0) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  sorry

theorem cmpi_slt_tensor_faithful_when_all_true
   {s : MachineState} {ss : SymState} {mem : Nat → Int}
   (hp   : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
   (hgs  : s.grid_size = ss.grid_size)
   (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
   (hsc  : ∀ v val, s.env v = some (scalar val) →
       ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
   (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
       ∃ g, ss.env v = some (SymValue.tensor vals.length g)
         ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
   (hnone : ∀ v, s.env v = none → ss.env v = none)
   (instr : TritonInstr) (a b : String)
   (h_op  : instr.op   = .cmpi_slt) (h_args : instr.args = [a, b])
   (sh : List Nat) (xs ys : List Int)
   (h_la  : s.lookup a = some (tensor sh xs))
   (h_lb  : s.lookup b = some (tensor sh ys))
   (hlen  : xs.length = ys.length)
   (hall  : ∀ i, i < xs.length → xs.getD i 0 < ys.getD i 0) :
   StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  sorry

-- ══════════════════════════════════════════════════════════════════════════════
-- Section 6: evalInstr_faithful
-- ══════════════════════════════════════════════════════════════════════════════



set_option maxHeartbeats 4000000 in
theorem evalInstr_faithful (instr : TritonInstr)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : StatesFaithful s ss mem) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := h
  have hid : StatesFaithful s ss mem := ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩
  match h_op : instr.op with

  | .constant v =>
      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, MachineState.lookup]
      exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone
        instr.result v (Expr.lit v) (by simp [evalExpr])

  | .get_program_id axis =>
      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, MachineState.lookup]
      by_cases haxis : axis == 0
      · simp only [haxis, ↓reduceIte]
        exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone _ _ _
          (by simp [evalExpr, hp])
      · simp only [haxis, ↓reduceIte]; sorry

  | .make_range sizeOpt =>
      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op]
      rw [← hbs]
      have hlen : (List.map Int.ofNat (List.range (sizeOpt.getD s.block_size))).length
                  = sizeOpt.getD s.block_size := by simp
      conv in (SymValue.tensor (sizeOpt.getD s.block_size) _) =>
        rw [show sizeOpt.getD s.block_size =
              (List.map Int.ofNat (List.range (sizeOpt.getD s.block_size))).length from hlen.symm]
      apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
      intro i hi
      rw [hlen] at hi
      simp only [evalExpr]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      simp [List.getElem?_range, hi]

  | .splat shape =>
      match h_args : instr.args with
      | [v] =>
          cases h_lv : s.env v with
          | none =>
              simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                MachineState.lookup, h_lv, Option.bind_none, SymState.lookup, hnone v h_lv]
              exact hid
          | some val =>
              cases val with
              | scalar x =>
                  obtain ⟨e, hse, heval⟩ := hsc v x h_lv
                  simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                    MachineState.lookup, h_lv, Option.bind_some, SymState.lookup, hse]
                  -- goal: StatesFaithful (s.bind r (tensor shape (replicate n x)))
                  --                      (ss.bind r (SymValue.tensor n (fun _ => e)))
                  -- Use conv to rewrite only the symbolic tensor n to (replicate n x).length
                  conv in (SymValue.tensor (shape.foldl (· * ·) 1) _) =>
                    rw [show shape.foldl (· * ·) 1 =
                        (List.replicate (shape.foldl (· * ·) 1) x).length from by
                      simp]
                  apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
                  intro i hi
                  simp only [List.length_replicate] at hi
                  -- goal: evalExpr e mem = (List.replicate n x)[i]?.getD 0
                  -- (replicate n x)[i] = x since i < n; evalExpr e mem = x by heval
                  simp only [evalExpr, heval]
                  simp [List.getElem?_replicate, hi]
              | fscalar _ => sorry
              | ftensor _ _ => sorry
              | tensor _ _ => sorry
      | _ => sorry

  | .addi =>
      match h_args : instr.args with
      | [a, b] =>
          cases h_la : s.env a with
          | none =>
              simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                MachineState.lookup, h_la, Option.bind_none, SymState.lookup,
                hnone a h_la, symAdd]; exact hid
          | some va =>
              cases h_lb : s.env b with
              | none =>
                  cases va with
                  | scalar x =>
                      obtain ⟨ea, hsa, _⟩ := hsc a x h_la
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_la, h_lb, Option.bind_some, Option.bind_none,
                        SymState.lookup, hsa, hnone b h_lb, symAdd]; exact hid
                  | tensor sh xs =>
                      obtain ⟨g, hsg, _⟩ := hten a sh xs h_la
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_la, h_lb, Option.bind_some, Option.bind_none,
                        SymState.lookup, hsg, hnone b h_lb, symAdd]; exact hid
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
              | some vb =>
                  cases va with
                  | scalar x =>
                      cases vb with
                      | scalar y =>
                          obtain ⟨ea, hsa, hea⟩ := hsc a x h_la
                          obtain ⟨eb, hsb, heb⟩ := hsc b y h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            SymState.lookup, hsa, hsb, symAdd]
                          exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone _ _ _
                            (by simp [evalExpr, hea, heb])
                      | tensor sh ys =>
                          obtain ⟨ea, hsa, hea⟩ := hsc a x h_la
                          obtain ⟨g, hsg, heg⟩ := hten b sh ys h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            SymState.lookup, hsa, hsg, symAdd]
                          simp only [show ys.length = (ys.map (fun z => z + x)).length from by simp]
                          apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
                          intro i hi; simp only [List.length_map] at hi
                          simp only [evalExpr]; rw [hea, heg i hi, map_add_getD ys x i hi]; omega
                      | fscalar _ => sorry
                      | ftensor _ _ => sorry
                  | tensor sh xs =>
                      cases vb with
                      | scalar y =>
                          obtain ⟨g, hsg, heg⟩ := hten a sh xs h_la
                          obtain ⟨eb, hsb, heb⟩ := hsc b y h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            SymState.lookup, hsg, hsb, symAdd]
                          simp only [show xs.length = (xs.map (fun z => z + y)).length from by simp]
                          apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
                          intro i hi; simp only [List.length_map] at hi
                          simp only [evalExpr]; rw [heg i hi, heb, map_add_getD xs y i hi]
                      | tensor _ _ => sorry
                      | fscalar _ => sorry
                      | ftensor _ _ => sorry
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
      | _ => sorry

  | .addf =>
      match h_args : instr.args with
      | [a, b] =>
          cases h_la : s.env a with
          | none =>
              simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                MachineState.lookup, h_la, Option.bind_none, SymState.lookup,
                hnone a h_la, symAdd]; exact hid
          | some va =>
              cases h_lb : s.env b with
              | none =>
                  cases va with
                  | scalar x =>
                      obtain ⟨ea, hsa, _⟩ := hsc a x h_la
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_la, h_lb, Option.bind_some, Option.bind_none,
                        SymState.lookup, hsa, hnone b h_lb, symAdd]; exact hid
                  | tensor sh xs =>
                      obtain ⟨g, hsg, _⟩ := hten a sh xs h_la
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_la, h_lb, Option.bind_some, Option.bind_none,
                        SymState.lookup, hsg, hnone b h_lb, symAdd]; exact hid
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
              | some vb =>
                  cases va with
                  | scalar x =>
                      cases vb with
                      | scalar y =>
                          obtain ⟨ea, hsa, hea⟩ := hsc a x h_la
                          obtain ⟨eb, hsb, heb⟩ := hsc b y h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            SymState.lookup, hsa, hsb, symAdd]
                          exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone _ _ _
                            (by simp [evalExpr, hea, heb])
                      | tensor sh ys =>
                          obtain ⟨ea, hsa, hea⟩ := hsc a x h_la
                          obtain ⟨g, hsg, heg⟩ := hten b sh ys h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            SymState.lookup, hsa, hsg, symAdd]
                          simp only [show ys.length = (ys.map (fun z => z + x)).length from by simp]
                          apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
                          intro i hi; simp only [List.length_map] at hi
                          simp only [evalExpr]; rw [hea, heg i hi, map_add_getD ys x i hi]; omega
                      | fscalar _ => sorry
                      | ftensor _ _ => sorry
                  | tensor sh xs =>
                      cases vb with
                      | scalar y =>
                          obtain ⟨g, hsg, heg⟩ := hten a sh xs h_la
                          obtain ⟨eb, hsb, heb⟩ := hsc b y h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            SymState.lookup, hsg, hsb, symAdd]
                          simp only [show xs.length = (xs.map (fun z => z + y)).length from by simp]
                          apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
                          intro i hi; simp only [List.length_map] at hi
                          simp only [evalExpr]; rw [heg i hi, heb, map_add_getD xs y i hi]
                      | tensor _ _ => sorry
                      | fscalar _ => sorry
                      | ftensor _ _ => sorry
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
      | _ => sorry

  | .muli =>
      match h_args : instr.args with
      | [a, b] =>
          cases h_la : s.env a with
          | none =>
              simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                MachineState.lookup, h_la, Option.bind_none, TritonValue.zipWith,
                SymState.lookup, hnone a h_la]; exact hid
          | some va =>
              cases h_lb : s.env b with
              | none =>
                  cases va with
                  | scalar x =>
                      obtain ⟨ea, hsa, _⟩ := hsc a x h_la
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_la, h_lb, Option.bind_some, Option.bind_none,
                        TritonValue.zipWith, SymState.lookup, hsa, hnone b h_lb]; exact hid
                  | tensor sh xs =>
                      obtain ⟨g, hsg, _⟩ := hten a sh xs h_la
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_la, h_lb, Option.bind_some, Option.bind_none,
                        TritonValue.zipWith, SymState.lookup, hsg, hnone b h_lb]; exact hid
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
              | some vb =>
                  cases va with
                  | scalar x =>
                      cases vb with
                      | scalar y =>
                          obtain ⟨ea, hsa, hea⟩ := hsc a x h_la
                          obtain ⟨eb, hsb, heb⟩ := hsc b y h_lb
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_la, h_lb, Option.bind_some,
                            TritonValue.zipWith, SymState.lookup, hsa, hsb]
                          exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone _ _ _
                            (by simp [evalExpr, hea, heb])
                      | tensor _ _ => sorry
                      | fscalar _ => sorry
                      | ftensor _ _ => sorry
                  | tensor _ _ => sorry
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
      | _ => sorry

  | .addptr =>
      match h_args : instr.args with
      | [p, o] =>
          cases h_lp : s.env p with
          | none =>
              simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                MachineState.lookup, h_lp, Option.bind_none, SymState.lookup, hnone p h_lp]
              exact hid
          | some vp =>
              cases h_lo : s.env o with
              | none =>
                  cases vp with
                  | scalar base =>
                      obtain ⟨ep, hsp, _⟩ := hsc p base h_lp
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_lp, h_lo, Option.bind_some, Option.bind_none,
                        SymState.lookup, hsp, hnone o h_lo]; exact hid
                  | tensor sh1 bases =>
                      obtain ⟨g, hsg, _⟩ := hten p sh1 bases h_lp
                      simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                        MachineState.lookup, h_lp, h_lo, Option.bind_some, Option.bind_none,
                        SymState.lookup, hsg, hnone o h_lo]; exact hid
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
              | some vo =>
                  cases vp with
                  | scalar base =>
                      cases vo with
                      | scalar off =>
                          obtain ⟨ep, hsp, hep⟩ := hsc p base h_lp
                          obtain ⟨eo, hso, heo⟩ := hsc o off h_lo
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_lp, h_lo, Option.bind_some,
                            SymState.lookup, hsp, hso]
                          exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone _ _ _
                            (by simp [evalExpr, hep, heo])
                      | tensor sh offs =>
                          obtain ⟨ep, hsp, hep⟩ := hsc p base h_lp
                          obtain ⟨g, hsg, heg⟩ := hten o sh offs h_lo
                          simp only [evalInstr, symEvalInstr, symEvalOp, evalOp, h_op, h_args,
                            MachineState.lookup, h_lp, h_lo, Option.bind_some,
                            SymState.lookup, hsp, hsg]
                          simp only [show offs.length = (offs.map (fun z => z + base)).length from by simp]
                          apply bind_tensor_faithful hp hbs hgs hmem hsc hten hnone
                          intro i hi; simp only [List.length_map] at hi
                          simp only [evalExpr]; rw [hep, heg i hi, map_add_getD offs base i hi]; omega
                      | fscalar _ => sorry
                      | ftensor _ _ => sorry
                  | tensor _ _ => sorry
                  | fscalar _ => sorry
                  | ftensor _ _ => sorry
      | _ => sorry

  | .load          => sorry
  | .load_masked   => sorry
  | .store         => sorry
  | .store_masked  => sorry
  | .storef        => sorry
  | .cmpi_slt      => sorry
  | .cmpi_sge      => sorry
  | .cmpi_sgt      => sorry
  | .cmpi_sle      => sorry
  | .cmpi_ne       => sorry
  | .cmpi_eq       => sorry
  | .cmpf_ole      => sorry
  | .cmpf_olt      => sorry
  | .get_num_programs _ => sorry
  | .constantf _   => sorry
  | .loadf         => sorry
  | .andi          => sorry
  | .subf          => sorry
  | .divf          => sorry
  | .mulf          => sorry
  | .maxsi         => sorry
  | .minsi         => sorry
  | .remsi         => sorry
  | .remui         => sorry
  | .divsi         => sorry
  | .divui         => sorry
  | .subi          => sorry
  | .shli          => sorry
  | .shrsi         => sorry
  | .shrui         => sorry
  | .xori          => sorry
  | .ori           => sorry
  | .truncf        => sorry
  | .extf          => sorry
  | .sqrtf         => sorry
  | .absf          => sorry
  | .negf          => sorry
  | .select        => sorry
  | .dot           => sorry
  | .reduce_sum _  => sorry
  | .reduce_max _  => sorry
  | .reduce_min _  => sorry
  | .broadcast _   => sorry
  | .expand_dims _ => sorry
  | .expf          => sorry
  | .constant_tensor _ _ => sorry
  | .constant_tensorf _ _ => sorry
  | .trans         => sorry
  | .reshape       => sorry


set_option maxHeartbeats 2000000 in
theorem symEvalKernel_faithful (K : TritonKernel)
   (s : MachineState) (ss : SymState) (mem : Nat → Int)
   (h : StatesFaithful s ss mem) :
   StatesFaithful (evalKernel K s) (symEvalKernel K ss) mem := by
 induction K generalizing s ss with
 | nil => simp [evalKernel, symEvalKernel]; exact h
 | cons instr rest ih =>
     simp only [evalKernel, symEvalKernel, List.foldl]
     exact ih _ _ (evalInstr_faithful instr s ss mem h)


-- Generic soundness bridge: for any kernel K, any init states satisfying
-- StatesFaithful, the symbolic memory at any address evaluates to the
-- concrete memory value under the interpretation mem.
theorem symEval_sound (K : TritonKernel)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : StatesFaithful s ss mem) (addr : Nat) :
    evalExpr ((symEvalKernel K ss).memory addr) mem =
    (evalKernel K s).memory addr :=
  (symEvalKernel_faithful K s ss mem h).2.2.2.1 addr


-- ══════════════════════════════════════════════════════════════════════════════
-- Section 7: StatesFaithfulMem driver (sound load/store via strengthened invariant)
-- ══════════════════════════════════════════════════════════════════════════════

-- Strengthened invariant: faithful AND concrete memory still equals the symbolic
-- interpretation base `mem`. Holds from init through any non-store instruction.
-- A store exits this regime (memory diverges) — handled as a terminal transition.
def StatesFaithfulMem (s : MachineState) (ss : SymState) (mem : Nat → Int) : Prop :=
  StatesFaithful s ss mem ∧ s.memory = mem

theorem evalInstr_preserves_memory_of_ne_store
    (instr : TritonInstr) (s : MachineState)
    (hns : instr.op ≠ .store) (hnsf : instr.op ≠ .storef) :
    (evalInstr instr s).memory = s.memory := by
  unfold evalInstr
  split
  · exact absurd (by assumption) hns
  · exact absurd (by assumption) hnsf
  · cases evalOp instr.op instr.args s with
    | none => rfl
    | some val => rfl

theorem evalInstr_faithful_mem
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (instr : TritonInstr)
    (hns : instr.op ≠ .store) (hnsf : instr.op ≠ .storef)
    (hstep_or_load :
       (instr.op = .load → ∃ p sh addrs, instr.args = [p] ∧ s.lookup p = some (tensor sh addrs))
       ∧ (instr.op ≠ .load →
            (StatesFaithful s ss mem →
             StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem)))
    (h : StatesFaithfulMem s ss mem) :
    StatesFaithfulMem (evalInstr instr s) (symEvalInstr instr ss) mem := by
  obtain ⟨hsf, hraw⟩ := h
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := hsf
  by_cases hld : instr.op = .load
  · obtain ⟨p, sh, addrs, h_args, h_lp⟩ := hstep_or_load.1 hld
    refine ⟨load_tensor_faithful_when_memory_unchanged hp hbs hgs hmem hsc hten hnone
      hraw instr p hld h_args sh addrs h_lp, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s hns hnsf]; exact hraw
  · refine ⟨hstep_or_load.2 hld ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩, ?_⟩
    rw [evalInstr_preserves_memory_of_ne_store instr s hns hnsf]; exact hraw

theorem prefix_faithful_mem (K : TritonKernel)
    (hstep : ∀ (instr : TritonInstr), instr ∈ K →
              ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                StatesFaithfulMem s ss mem →
                StatesFaithfulMem (evalInstr instr s) (symEvalInstr instr ss) mem)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : StatesFaithfulMem s ss mem) :
    StatesFaithfulMem (evalKernel K s) (symEvalKernel K ss) mem := by
  induction K generalizing s ss with
  | nil => simpa [evalKernel, symEvalKernel] using h
  | cons instr rest ih =>
      simp only [evalKernel, symEvalKernel, List.foldl]
      exact ih (fun i hi => hstep i (List.mem_cons_of_mem _ hi)) _ _
        (hstep instr (List.mem_cons_self ..) s ss mem h)

theorem evalKernel_append (xs ys : TritonKernel) (s : MachineState) :
    evalKernel (xs ++ ys) s = evalKernel ys (evalKernel xs s) := by
  simp only [evalKernel, List.foldl_append]

theorem symEvalKernel_append (xs ys : TritonKernel) (ss : SymState) :
    symEvalKernel (xs ++ ys) ss = symEvalKernel ys (symEvalKernel xs ss) := by
  simp only [symEvalKernel, List.foldl_append]

theorem kernel_faithful_terminal_store
    (pre : TritonKernel) (storeInstr : TritonInstr)
    (hpre_step : ∀ (instr : TritonInstr), instr ∈ pre →
              ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                StatesFaithfulMem s ss mem →
                StatesFaithfulMem (evalInstr instr s) (symEvalInstr instr ss) mem)
    (hstore : ∀ (s : MachineState) (ss : SymState) (mem : Nat → Int),
                StatesFaithfulMem s ss mem →
                StatesFaithful (evalInstr storeInstr s) (symEvalInstr storeInstr ss) mem)
    (s : MachineState) (ss : SymState) (mem : Nat → Int)
    (h : StatesFaithfulMem s ss mem) :
    StatesFaithful (evalKernel (pre ++ [storeInstr]) s)
                   (symEvalKernel (pre ++ [storeInstr]) ss) mem := by
  rw [evalKernel_append, symEvalKernel_append]
  have hpre := prefix_faithful_mem pre hpre_step s ss mem h
  simp only [evalKernel, symEvalKernel, List.foldl_cons, List.foldl_nil]
  exact hstore _ _ _ hpre


#check @symEval_sound

end Trident
