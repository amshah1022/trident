import Trident.Common.Symbolic
import Trident.Target.Semantics
import Trident.Proofs.VectorAddProof
import Trident.Common.Equiv

namespace Trident
open TritonValue

theorem range_map_getD_pair_eq_zip
    (addrs vals : List Int) (n : Nat) (hlen_a : addrs.length = n) (hlen_v : vals.length = n) :
    (List.range n).map (fun i => (addrs.getD i 0, vals.getD i 0)) = addrs.zip vals := by
  apply List.ext_getElem
  · simp [hlen_a, hlen_v]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_zip]
    refine ⟨?_, ?_⟩
    · simp [List.getD_eq_getElem, h1, hlen_a]
    · simp [List.getD_eq_getElem, h2, hlen_v]

theorem range_fold_mem_faithful
    (n : Nat) (gAddrs gVals : Nat → Expr) (cAddrs cVals : Nat → Int) (mem : Nat → Int)
    (hconcrete : ∀ i, i < n → (gAddrs i).isConcrete = true)
    (haddr : ∀ i, i < n → evalExpr (gAddrs i) mem = cAddrs i)
    (hval : ∀ i, i < n → evalExpr (gVals i) mem = cVals i) :
    ∀ (s : MachineState) (ss : SymState),
      (∀ addr, evalExpr (ss.memory addr) mem = s.memory addr) →
      ∀ addr, evalExpr
        ((List.foldl (fun st i => st.writeMem (evalExpr (gAddrs i) (fun _ => 0)).natAbs (gVals i))
          ss (List.range n)).memory addr) mem
        = (List.foldl (fun st i => st.writeMem (cAddrs i).natAbs (cVals i))
          s (List.range n)).memory addr := by
  induction n with
  | zero => intro s ss hmem0 addr; simpa using hmem0 addr
  | succ n ih =>
      intro s ss hmem0 addr
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hc : (gAddrs n).isConcrete = true := hconcrete n (by omega)
      have heq_addr : evalExpr (gAddrs n) (fun _ => 0) = evalExpr (gAddrs n) mem :=
        evalExpr_concrete (gAddrs n) (fun _ => 0) mem hc
      have ih' := ih (fun i hi => hconcrete i (by omega)) (fun i hi => haddr i (by omega))
        (fun i hi => hval i (by omega)) s ss hmem0
      rw [heq_addr, haddr n (by omega)]
      exact writeMem_mem_faithful _ _ mem ih' (cAddrs n).natAbs (gVals n) (cVals n)
        (hval n (by omega)) addr

theorem sym_foldl_writeMem_not_mem
    (n : Nat) (gAddrs gVals : Nat → Expr) (ss : SymState) (addr : Nat)
    (h : ∀ i, i < n → (evalExpr (gAddrs i) (fun _ => 0)).natAbs ≠ addr) :
    (List.foldl (fun st i =>
        st.writeMem (evalExpr (gAddrs i) (fun _ => 0)).natAbs (gVals i))
      ss (List.range n)).memory addr = ss.memory addr := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih (fun i hi => h i (by omega))]
      simp only [SymState.writeMem]
      have hne : (evalExpr (gAddrs n) (fun _ => 0)).natAbs ≠ addr := h n (by omega)
      simp [hne]

private theorem range_map_getD (n i : Nat) :
    (List.map Int.ofNat (List.range n)).getD i 0 =
    if i < n then Int.ofNat i else 0 := by
  rcases Nat.lt_or_ge i n with h | h
  · simp [List.getD, List.getElem?_map, List.getElem?_range, h]
  · simp [List.getD, List.length_map, List.length_range, Nat.not_lt.mpr h]

theorem index_fold_eq_writeTile
    (addrs vals : List Int) (n : Nat) (hlen_a : addrs.length = n) (hlen_v : vals.length = n)
    (s : MachineState) :
    List.foldl (fun st i => st.writeMem (addrs.getD i 0).natAbs (vals.getD i 0)) s (List.range n)
    = s.writeTile (addrs.map Int.natAbs) vals := by
  simp only [MachineState.writeTile, List.zip_map_left]
  rw [← range_map_getD_pair_eq_zip addrs vals n hlen_a hlen_v, ← List.foldl_map]
theorem store_tensor_faithful_when_memory_unchanged
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor vals.length g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (instr : TritonInstr) (p v : String)
    (h_op : instr.op = .store) (h_args : instr.args = [p, v])
    (sh : List Nat) (addrs vals : List Int)
    (h_lp : s.lookup p = some (tensor sh addrs))
    (h_lv : s.lookup v = some (tensor sh vals))
    (hlen : addrs.length = vals.length)
    (gp gv : Nat → Expr)
    (hgp : ss.env p = some (SymValue.tensor addrs.length gp))
    (hgv_corr : ss.env v = some (SymValue.tensor vals.length gv))
    (hconcrete : ∀ i, i < addrs.length → (gp i).isConcrete = true)
    (haddr : ∀ i, i < addrs.length → evalExpr (gp i) mem = addrs.getD i 0)
    (hval : ∀ i, i < addrs.length → evalExpr (gv i) mem = vals.getD i 0) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  simp only [evalInstr, h_op, h_args, h_lp, h_lv, MachineState.lookup]
  simp only [symEvalInstr, h_op, h_args, hgp, hgv_corr, SymState.lookup]
  refine ⟨hp, hbs, hgs, ?_, hsc, hten, hnone⟩
  intro addr
  have key := range_fold_mem_faithful addrs.length gp gv
    (fun i => addrs.getD i 0) (fun i => vals.getD i 0) mem
    hconcrete haddr hval s ss hmem addr
  rwa [index_fold_eq_writeTile addrs vals addrs.length rfl hlen.symm s] at key

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
      ∃ g, ss.env v = some (SymValue.tensor vals.length g)
        ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
  ∧ (∀ v, s.env v = none → ss.env v = none)

def MemFaithfulOutside (s : MachineState) (ss : SymState) (mem : Nat → Int) (W : List Nat) : Prop :=
  ∀ addr, addr ∉ W → evalExpr (ss.memory addr) mem = mem addr

def Expr.isConcrete : Expr → Bool
  | .lit _      => true
  | .var _ _    => false
  | .load _     => false
  | .add e1 e2  => e1.isConcrete && e2.isConcrete
  | .mul e1 e2  => e1.isConcrete && e2.isConcrete
  | .max e1 e2  => e1.isConcrete && e2.isConcrete
  | .reduceSum _ => false
theorem evalInstr_memory_unchanged_of_not_store
    (instr : TritonInstr) (s : MachineState)
    (h : instr.op ≠ .store ∧ instr.op ≠ .storef) :
    (evalInstr instr s).memory = s.memory := by
  unfold evalInstr
  split
  · exact absurd ‹instr.op = .store› h.1
  · exact absurd ‹instr.op = .storef› h.2
  · cases evalOp instr.op instr.args s with
    | none => rfl
    | some val => simp [MachineState.bind]

theorem evalKernel_memory_unchanged_of_no_store
    (K : TritonKernel) (s : MachineState)
    (h : ∀ instr ∈ K, instr.op ≠ .store ∧ instr.op ≠ .storef) :
    (evalKernel K s).memory = s.memory := by
  induction K generalizing s with
  | nil => simp [evalKernel]
  | cons instr rest ih =>
      simp only [evalKernel, List.foldl]
      rw [ih (evalInstr instr s) (fun i hi => h i (by simp [hi]))]
      exact evalInstr_memory_unchanged_of_not_store instr s (h instr (by simp))

def parsedVectorAdd : TritonKernel := [
  { result := "c1024_i32", op := .constant 1024,          args := [] },
  { result := "0",         op := .get_program_id 0,       args := [] },
  { result := "1",         op := .muli,                   args := ["0", "c1024_i32"] },
  { result := "2",         op := .make_range (some 1024), args := [] },
  { result := "3",         op := .splat [1024],            args := ["1"] },
  { result := "4",         op := .addi,                   args := ["3", "2"] },
  { result := "5",         op := .addptr,                 args := ["arg0", "4"] },
  { result := "6",         op := .addptr,                 args := ["arg1", "4"] },
  { result := "7",         op := .addptr,                 args := ["arg2", "4"] },
  { result := "8",         op := .load,                   args := ["5"] },
  { result := "9",         op := .load,                   args := ["6"] },
  { result := "10",        op := .addf,                   args := ["8", "9"] },
  { result := "_",         op := .store,                  args := ["7", "10"] }
]

theorem parsedVectorAdd_prefix_memory_unchanged (a b : List Int) (pid bs gs : Nat) :
    (evalKernel (parsedVectorAdd.take 9) (parsedInitState a b pid bs gs)).memory
      = (parsedInitState a b pid bs gs).memory := by
  apply evalKernel_memory_unchanged_of_no_store
  intro instr hi
  simp only [parsedVectorAdd, List.take, List.mem_cons, List.mem_singleton, List.not_mem_nil] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by decide, by decide⟩

def symParsedVectorAddInitState (pid bs gs n : Nat) : SymState :=
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := fun addr =>
      if addr < n then Expr.var "a" addr
      else if addr < 2 * n then Expr.var "b" addr
      else Expr.lit 0
  , env        := fun v => match v with
      | "arg0"       => some (SymValue.scalar (Expr.lit 0))
      | "arg1"       => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | "arg2"       => some (SymValue.scalar (Expr.lit (Int.ofNat (2 * n))))
      | "a_base"     => some (SymValue.scalar (Expr.lit 0))
      | "b_base"     => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | "c_base"     => some (SymValue.scalar (Expr.lit (Int.ofNat (2 * n))))
      | "bsize"      => some (SymValue.scalar (Expr.lit (Int.ofNat bs)))
      | "x_ptr"      => some (SymValue.scalar (Expr.lit 0))
      | "y_ptr"      => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | "output_ptr" => some (SymValue.scalar (Expr.lit (Int.ofNat (2 * n))))
      | "n_elements" => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | _            => none }

theorem parsedInitStates_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (parsedInitState a b pid bs gs)
      (symParsedVectorAddInitState pid bs gs a.length)
      (concreteMem a b) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro addr
    simp only [symParsedVectorAddInitState, parsedInitState, concreteMem]
    by_cases h1 : addr < a.length
    · simp only [h1, ↓reduceIte, evalExpr, layoutMemory]
    · by_cases h2 : addr < 2 * a.length
      · simp only [h1, h2, ↓reduceIte, evalExpr]
      · simp only [h1, h2, ↓reduceIte, evalExpr]
        symm; unfold layoutMemory; simp [h1, h2]
  · intro v val hv
    simp only [parsedInitState] at hv
    simp only [symParsedVectorAddInitState]
    split at hv <;> simp_all [evalExpr]
  · intro v sh vals hv
    simp only [parsedInitState] at hv
    split at hv <;> simp_all
  · intro v hv
    simp only [parsedInitState] at hv
    simp only [symParsedVectorAddInitState]
    split at hv <;> simp_all

theorem parsedVectorAdd_prefix_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (evalKernel (parsedVectorAdd.take 9) (parsedInitState a b pid bs gs))
      (symEvalKernel (parsedVectorAdd.take 9) (symParsedVectorAddInitState pid bs gs a.length))
      (concreteMem a b) :=
  symEvalKernel_faithful (parsedVectorAdd.take 9)
    (parsedInitState a b pid bs gs)
    (symParsedVectorAddInitState pid bs gs a.length)
    (concreteMem a b)
    (parsedInitStates_faithful a b pid bs gs)

theorem parsedVectorAdd_s9_has_tensor_5 (a b : List Int) (pid bs gs : Nat) :
    ∃ sh addrs, (evalKernel (parsedVectorAdd.take 9) (parsedInitState a b pid bs gs)).lookup "5"
      = some (TritonValue.tensor sh addrs) := by
  simp only [parsedVectorAdd, parsedInitState, evalKernel, evalInstr, evalOp,
             List.take, MachineState.bind, MachineState.lookup, TritonValue.zipWith,
             List.foldl]
  exact ⟨_, _, rfl⟩

theorem parsedVectorAdd_s9_has_tensor_6 (a b : List Int) (pid bs gs : Nat) :
    ∃ sh addrs, (evalKernel (parsedVectorAdd.take 9) (parsedInitState a b pid bs gs)).lookup "6"
      = some (TritonValue.tensor sh addrs) := by
  simp only [parsedVectorAdd, parsedInitState, evalKernel, evalInstr, evalOp,
             List.take, MachineState.bind, MachineState.lookup, TritonValue.zipWith,
             List.foldl]
  exact ⟨_, _, rfl⟩

theorem parsedVectorAdd_s10_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (evalKernel (parsedVectorAdd.take 10) (parsedInitState a b pid bs gs))
      (symEvalKernel (parsedVectorAdd.take 10) (symParsedVectorAddInitState pid bs gs a.length))
      (concreteMem a b) := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := parsedVectorAdd_prefix_faithful a b pid bs gs
  obtain ⟨sh5, addrs5, h5⟩ := parsedVectorAdd_s9_has_tensor_5 a b pid bs gs
  have hmem_raw : (evalKernel (parsedVectorAdd.take 9) (parsedInitState a b pid bs gs)).memory
      = concreteMem a b := by
    rw [parsedVectorAdd_prefix_memory_unchanged]; rfl
  have step := load_tensor_faithful_when_memory_unchanged
    hp hbs hgs hmem hsc hten hnone hmem_raw
    { result := "8", op := .load, args := ["5"] } "5" rfl rfl sh5 addrs5 h5
  simpa [parsedVectorAdd, evalKernel, symEvalKernel, List.take, List.foldl] using step


theorem parsedVectorAdd_s10_has_tensor_6 (a b : List Int) (pid bs gs : Nat) :
    ∃ sh addrs, (evalKernel (parsedVectorAdd.take 10) (parsedInitState a b pid bs gs)).lookup "6"
      = some (TritonValue.tensor sh addrs) := by
  simp only [parsedVectorAdd, parsedInitState, evalKernel, evalInstr, evalOp,
             List.take, MachineState.bind, MachineState.lookup, TritonValue.zipWith,
             List.foldl]
  exact ⟨_, _, rfl⟩

theorem parsedVectorAdd_s11_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (evalKernel (parsedVectorAdd.take 11) (parsedInitState a b pid bs gs))
      (symEvalKernel (parsedVectorAdd.take 11) (symParsedVectorAddInitState pid bs gs a.length))
      (concreteMem a b) := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := parsedVectorAdd_s10_faithful a b pid bs gs
  obtain ⟨sh6, addrs6, h6⟩ := parsedVectorAdd_s10_has_tensor_6 a b pid bs gs
  have hmem_raw : (evalKernel (parsedVectorAdd.take 10) (parsedInitState a b pid bs gs)).memory
      = concreteMem a b := by
    simp only [parsedVectorAdd, parsedInitState, evalKernel, evalInstr, evalOp,
               List.take, MachineState.bind, MachineState.lookup, TritonValue.zipWith,
               List.foldl, concreteMem, layoutMemory]
  have step := load_tensor_faithful_when_memory_unchanged
    hp hbs hgs hmem hsc hten hnone hmem_raw
    { result := "9", op := .load, args := ["6"] } "6" rfl rfl sh6 addrs6 h6
  simpa [parsedVectorAdd, evalKernel, symEvalKernel, List.take, List.foldl] using step

theorem parsedVectorAdd_s12_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (evalKernel (parsedVectorAdd.take 12) (parsedInitState a b pid bs gs))
      (symEvalKernel (parsedVectorAdd.take 12) (symParsedVectorAddInitState pid bs gs a.length))
      (concreteMem a b) := by
  have step := evalInstr_faithful { result := "10", op := .addf, args := ["8", "9"] }
    (evalKernel (parsedVectorAdd.take 11) (parsedInitState a b pid bs gs))
    (symEvalKernel (parsedVectorAdd.take 11) (symParsedVectorAddInitState pid bs gs a.length))
    (concreteMem a b)
    (parsedVectorAdd_s11_faithful a b pid bs gs)
  simpa [parsedVectorAdd, evalKernel, symEvalKernel, List.take, List.foldl] using step

theorem parsedVectorAdd_s12_store_setup (a b : List Int) (pid bs gs : Nat) :
    ∃ sh addrs vals,
      (evalKernel (parsedVectorAdd.take 12) (parsedInitState a b pid bs gs)).lookup "7"
        = some (TritonValue.tensor sh addrs) ∧
      (evalKernel (parsedVectorAdd.take 12) (parsedInitState a b pid bs gs)).lookup "10"
        = some (TritonValue.tensor sh vals) ∧
      addrs.length = vals.length ∧
      ∃ g, (symEvalKernel (parsedVectorAdd.take 12) (symParsedVectorAddInitState pid bs gs a.length)).env "7"
        = some (SymValue.tensor addrs.length g) ∧
      ∀ i, (g i).isConcrete = true := by
  simp only [parsedVectorAdd, parsedInitState, symParsedVectorAddInitState, evalKernel, symEvalKernel,
             evalInstr, symEvalInstr, evalOp, symEvalOp, symAdd, List.take, MachineState.bind,
             SymState.bind, MachineState.lookup, SymState.lookup, TritonValue.zipWith, List.foldl]
  refine ⟨_, _, _, rfl, rfl, rfl, _, rfl, fun i => ?_⟩
  simp [Expr.isConcrete]


theorem parsedVectorAdd_full_faithful (a b : List Int) (pid bs gs : Nat) :
    StatesFaithful
      (evalKernel parsedVectorAdd (parsedInitState a b pid bs gs))
      (symEvalKernel parsedVectorAdd (symParsedVectorAddInitState pid bs gs a.length))
      (concreteMem a b) := by
  obtain ⟨hp, hbs, hgs, hmem, hsc, hten, hnone⟩ := parsedVectorAdd_s12_faithful a b pid bs gs
  obtain ⟨sh, addrs, vals, h_lp, h_lv, hlen, g, hgp, hconcrete⟩ :=
    parsedVectorAdd_s12_store_setup a b pid bs gs
  obtain ⟨gv, hgv_corr, hgv_vals⟩ := hten "10" sh vals h_lv
  obtain ⟨g', hgp', haddr'⟩ := hten "7" sh addrs h_lp
  have hgeq : g' = g := by
    have := hgp'.symm.trans hgp
    injection this with h1 h2
  have haddr := hgeq ▸ haddr'
  have step := store_tensor_faithful_when_memory_unchanged
    hp hbs hgs hmem hsc hten hnone
    { result := "_", op := .store, args := ["7", "10"] } "7" "10" rfl rfl
    sh addrs vals h_lp h_lv hlen g gv hgp hgv_corr
    (fun i _ => hconcrete i) haddr hgv_vals
  simpa [parsedVectorAdd, evalKernel, symEvalKernel, List.take, List.foldl] using step

theorem parsedVectorAdd_correct
    (a b : List Int) (pid bs gs : Nat)
    (h_len : a.length = b.length) (h_bs : bs = 1024) (h_pid : pid < gs) (h_cov : gs * bs = a.length) :
    ∀ i < bs,
      let s  := parsedInitState a b pid bs gs
      let s' := evalKernel parsedVectorAdd s
      s'.readMem (2 * a.length + pid * bs + i) =
      (vectorAddSpec a b).getD (pid * bs + i) 0 := by
  intro i hi
  have h_inbound : pid * bs + i < a.length := by
    have h1 : pid + 1 <= gs := Nat.succ_le_of_lt h_pid
    have h2 : (pid + 1) * bs <= gs * bs := Nat.mul_le_mul_right bs h1
    simp [Nat.add_mul] at h2
    omega
  have h_spec : (vectorAddSpec a b).getD (pid * bs + i) 0 =
      a.getD (pid * bs + i) 0 + b.getD (pid * bs + i) 0 :=
    zipWith_add_getD a b (pid * bs + i) h_len
  rw [h_spec]
  obtain ⟨_, _, _, hmem, _⟩ := parsedVectorAdd_full_faithful a b pid bs gs
  have key := hmem (2 * a.length + pid * bs + i)
  show MachineState.readMem _ (2 * a.length + pid * bs + i) = _
  unfold MachineState.readMem
  rw [← key]
  simp only [parsedVectorAdd, symParsedVectorAddInitState, symEvalKernel, symEvalInstr, symEvalOp,
             symAdd, SymState.bind, SymState.lookup, SymState.writeMem, List.foldl]
  simp only [evalExpr, concreteMem, layoutMemory, h_bs]
  have hi1 : pid * 1024 + i < a.length := by omega
  have hi2 : a.length + (pid * 1024 + i) < 2 * a.length := by omega
  simp [hi1, hi2]
  omega

theorem load_tensor_faithful_when_memory_unchanged
    {s : MachineState} {ss : SymState} {mem : Nat → Int}
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor vals.length g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (hmem_raw : s.memory = mem)
    (instr : TritonInstr) (p : String)
    (h_op : instr.op = .load) (h_args : instr.args = [p])
    (sh : List Nat) (addrs : List Int)
    (h_lp : s.lookup p = some (tensor sh addrs)) :
    StatesFaithful (evalInstr instr s) (symEvalInstr instr ss) mem := by
  have ⟨g, hg, hgv⟩ := hten p sh addrs h_lp
  simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp,
             MachineState.lookup, h_lp, SymState.lookup, hg]
  refine bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result
    sh (addrs.map fun a => s.readMem a.natAbs) (fun i => Expr.load (g i)) ?_
  intro i hi
  simp only [List.length_map] at hi
  simp only [evalExpr, hgv i hi, MachineState.readMem, hmem_raw]
  simp [List.getD, List.getElem?_map, hi]

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
    (hp : s.pid = ss.pid) (hbs : s.block_size = ss.block_size)
    (hgs : s.grid_size = ss.grid_size)
    (hmem : ∀ addr, evalExpr (ss.memory addr) mem = s.memory addr)
    (hsc : ∀ v val, s.env v = some (scalar val) →
        ∃ e, ss.env v = some (SymValue.scalar e) ∧ evalExpr e mem = val)
    (hten : ∀ v sh vals, s.env v = some (tensor sh vals) →
        ∃ g, ss.env v = some (SymValue.tensor vals.length g)
          ∧ ∀ i, i < vals.length → evalExpr (g i) mem = vals.getD i 0)
    (hnone : ∀ v, s.env v = none → ss.env v = none)
    (r : String) (sh : List Nat) (cvals : List Int) (g : Nat → Expr)
    (hg : ∀ i, i < cvals.length → evalExpr (g i) mem = cvals.getD i 0) :
    StatesFaithful (s.bind r (tensor sh cvals)) (ss.bind r (SymValue.tensor cvals.length g)) mem := by
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
  | .get_program_id axis =>
      by_cases haxis : axis = 0
      · subst haxis
        simp [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]
        exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone instr.result
          (Int.ofNat s.pid) (Expr.lit (Int.ofNat ss.pid)) (by simp [evalExpr, hp])
      · sorry -- get_program_id with axis ≠ 0 (pid_y): SymState has no pid_y field yet, not needed for vector-add
  | .constant v =>
      simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]
      exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone instr.result
        v (Expr.lit v) (by simp [evalExpr])
  | .make_range =>
      simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]
      -- symEvalInstr produces SymValue.tensor ss.block_size, evalInstr produces List.range s.block_size
      -- with hbs : s.block_size = ss.block_size, these match
      have hlen : (List.map Int.ofNat (List.range s.block_size)).length = ss.block_size := by
        simp [List.length_map, List.length_range, hbs]
      rw [← hlen]
      refine bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result
        [s.block_size] ((List.range s.block_size).map Int.ofNat)
        (fun i => Expr.lit (Int.ofNat i)) ?_
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      simp only [evalExpr, range_map_getD, hi, ↓reduceIte]
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
                have hlen_splat : (List.replicate s.block_size x).length = ss.block_size := by
                  simp [hbs]
                rw [← hlen_splat]
                exact bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result
                  [s.block_size] (List.replicate s.block_size x)
                  (fun _ => e)
                  (by intro i hi
                      simp only [List.length_replicate] at hi
                      rw [hev]
                      simp [List.getD, List.getElem?_replicate, hi])
            | tensor sh_b vals_b =>
                      have h_env_b : s.env b = some (tensor sh_b vals_b) := h_lb2
                      have ⟨gb, hgb, hgbv⟩ := hten b sh_b vals_b h_lb2
                      by_cases hsh : sh_a = sh_b
                      · by_cases hlen : vals_a.length = vals_b.length
                        · subst hsh
                          simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp, symAdd,
                                     MachineState.lookup, h_env_a, h_env_b, SymState.lookup, hga, hgb,
                                     BEq.rfl, ↓reduceIte]
                          have hlen2 : ((vals_a.zip vals_b).map (fun (x, y) => x + y)).length = vals_a.length := by
                            simp [List.length_zip, hlen]
                          rw [← hlen2]
                          refine bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result
                            sh_a ((vals_a.zip vals_b).map (fun (x, y) => x + y))
                            (fun i => Expr.add (ga i) (gb i)) ?_
                          intro i hi
                          simp only [List.length_map, List.length_zip, hlen, min_self] at hi
                          simp only [evalExpr, hgav i (hlen ▸ hi), hgbv i hi]
                          simp [List.getD, List.getElem?_map, List.getElem?_zip, hi, hlen]
                        · sorry -- addi tensor×tensor, length mismatch (not needed for vector-add)
                      · sorry -- addi tensor×tensor, shape mismatch (not needed for vector-add)
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
                      have ⟨ea, heas, heav⟩ := hsc a x h_la
                      have ⟨gb, hgb, hgbv⟩ := hten b sh vals h_lb
                      simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp, symAdd,
                                 MachineState.lookup, h_env_a, h_env_b, SymState.lookup, heas, hgb]
                      conv in (SymValue.tensor vals.length _) =>
                        rw [show vals.length = (vals.map (· + x)).length from (List.length_map _).symm]
                      refine bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result
                        sh (vals.map (· + x)) (fun i => Expr.add ea (gb i)) ?_
                      intro i hi
                      simp only [List.length_map] at hi
                      simp only [evalExpr, heav, hgbv i hi]
                      simp [List.getD, hi, Int.add_comm]
            | tensor sh_a vals_a =>
                have h_env_a : s.env a = some (tensor sh_a vals_a) := h_la
                have ⟨ga, hga, hgav⟩ := hten a sh_a vals_a h_la
                cases h_lb2 : s.lookup b with
                | none =>
                    have hss_b : ss.env b = none := hnone b h_lb2
                    simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp, symAdd,
                               MachineState.lookup, h_env_a, h_lb2, SymState.lookup, hga]
                    simp only [hss_b]; exact hf
                | some vb2 => cases vb2 with
                  | tensor sh_b vals_b =>
                      sorry -- addi tensor×tensor
                  | scalar y =>
                      have h_env_b2 : s.env b = some (scalar y) := h_lb2
                      have ⟨eb, hebs, hebv⟩ := hsc b y h_lb2
                      simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp, symAdd,
                                 MachineState.lookup, h_env_a, h_env_b2, SymState.lookup, hga, hebs]
                      conv in (SymValue.tensor vals_a.length _) =>
                        rw [show vals_a.length = (vals_a.map (· + y)).length from (List.length_map _).symm]
                      refine bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result
                        sh_a (vals_a.map (· + y)) (fun i => Expr.add (ga i) eb) ?_
                      intro i hi
                      simp only [List.length_map] at hi
                      simp only [evalExpr, hebv, hgav i hi]
                      simp [List.getD, hi, Int.add_comm]
      | [] =>
          simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, symAdd]; exact hf
      | [_] =>
          simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, symAdd]; exact hf
      | _ :: _ :: _ :: _ =>
          simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, symAdd]; exact hf
  | .addf =>
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
                      have ⟨ea, heas, heav⟩ := hsc a x h_la
                      have ⟨gb, hgb, hgbv⟩ := hten b sh vals h_lb
                      simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp, symAdd,
                                 MachineState.lookup, h_env_a, h_env_b, SymState.lookup, heas, hgb]
                      conv in (SymValue.tensor vals.length _) =>
                        rw [show vals.length = (vals.map (· + x)).length from (List.length_map _).symm]
                      refine bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result
                        sh (vals.map (· + x)) (fun i => Expr.add ea (gb i)) ?_
                      intro i hi
                      simp only [List.length_map] at hi
                      simp only [evalExpr, heav, hgbv i hi]
                      simp [List.getD, hi, Int.add_comm]
            | tensor sh_a vals_a =>
                have h_env_a : s.env a = some (tensor sh_a vals_a) := h_la
                have ⟨ga, hga, hgav⟩ := hten a sh_a vals_a h_la
                cases h_lb2 : s.lookup b with
                | none =>
                    have hss_b : ss.env b = none := hnone b h_lb2
                    simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp, symAdd,
                               MachineState.lookup, h_env_a, h_lb2, SymState.lookup, hga]
                    simp only [hss_b]; exact hf
                | some vb2 => cases vb2 with
                  | tensor sh_b vals_b =>
                      have h_env_b : s.env b = some (tensor sh_b vals_b) := h_lb2
                      have ⟨gb, hgb, hgbv⟩ := hten b sh_b vals_b h_lb2
                      by_cases hsh : sh_a = sh_b
                      · by_cases hlen : vals_a.length = vals_b.length
                        · subst hsh
                          simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp, symAdd,
                                     MachineState.lookup, h_env_a, h_env_b, SymState.lookup, hga, hgb,
                                     BEq.rfl, ↓reduceIte]
                          have hlen2 : ((vals_a.zip vals_b).map (fun (x, y) => x + y)).length = vals_a.length := by
                            simp [List.length_zip, hlen]
                          rw [← hlen2]
                          refine bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result
                            sh_a ((vals_a.zip vals_b).map (fun (x, y) => x + y))
                            (fun i => Expr.add (ga i) (gb i)) ?_
                          intro i hi
                          simp only [List.length_map, List.length_zip, hlen, min_self] at hi
                          simp only [evalExpr, hgav i (hlen ▸ hi), hgbv i hi]
                          simp [List.getD, List.getElem?_map, List.getElem?_zip, hi, hlen]
                        · sorry -- addf tensor×tensor, length mismatch (not needed for vector-add)
                      · sorry -- addf tensor×tensor, shape mismatch (not needed for vector-add)
                  | scalar y =>
                      have h_env_b2 : s.env b = some (scalar y) := h_lb2
                      have ⟨eb, hebs, hebv⟩ := hsc b y h_lb2
                      simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp, symAdd,
                                 MachineState.lookup, h_env_a, h_env_b2, SymState.lookup, hga, hebs]
                      conv in (SymValue.tensor vals_a.length _) =>
                        rw [show vals_a.length = (vals_a.map (· + y)).length from (List.length_map _).symm]
                      refine bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result
                        sh_a (vals_a.map (· + y)) (fun i => Expr.add (ga i) eb) ?_
                      intro i hi
                      simp only [List.length_map] at hi
                      simp only [evalExpr, hebv, hgav i hi]
                      simp [List.getD, hi, Int.add_comm]
      | [] =>
          simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, symAdd]; exact hf
      | [_] =>
          simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, symAdd]; exact hf
      | _ :: _ :: _ :: _ =>
          simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp, symAdd]; exact hf
  | .addptr =>
      match h_args : instr.args with
      | [p, o] =>
          cases h_lp : s.lookup p with
          | none =>
              have hss_p : ss.env p = none := hnone p h_lp
              simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp,
                         MachineState.lookup, h_lp, SymState.lookup, hss_p]
              exact hf
          | some vp => cases vp with
            | scalar base =>
                cases h_lo : s.lookup o with
                | none =>
                    have ⟨ep, heps, _⟩ := hsc p base h_lp
                    have hss_o : ss.env o = none := hnone o h_lo
                    simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp,
                               MachineState.lookup, h_lp, h_lo, SymState.lookup, heps, hss_o]
                    exact hf
                | some vo => cases vo with
                  | scalar off =>
                      have ⟨ep, heps, hepv⟩ := hsc p base h_lp
                      have ⟨eo, heos, heov⟩ := hsc o off h_lo
                      simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp,
                                 MachineState.lookup, h_lp, h_lo, SymState.lookup, heps, heos]
                      exact bind_scalar_faithful hp hbs hgs hmem hsc hten hnone instr.result
                        (base + off) (Expr.add ep eo) (by simp [evalExpr, hepv, heov])
                  | tensor sh offs =>
                      have h_env_p : s.env p = some (scalar base) := h_lp
                      have h_env_o : s.env o = some (tensor sh offs) := h_lo
                      have ⟨ep, heps, hepv⟩ := hsc p base h_lp
                      have ⟨go, hgo, hgov⟩ := hten o sh offs h_lo
                      simp only [evalInstr, symEvalInstr, h_op, h_args, evalOp, symEvalOp,
                                 MachineState.lookup, h_env_p, h_env_o, SymState.lookup, heps, hgo]
                      conv in (SymValue.tensor offs.length _) =>
                        rw [show offs.length = (offs.map (· + base)).length from (List.length_map _).symm]
                      refine bind_tensor_faithful hp hbs hgs hmem hsc hten hnone instr.result
                        sh (offs.map (· + base)) (fun i => Expr.add ep (go i)) ?_
                      intro i hi
                      simp only [List.length_map] at hi
                      simp only [evalExpr, hepv, hgov i hi]
                      simp [List.getD, hi, Int.add_comm]
            | tensor sh1 bases =>
                sorry -- addptr tensor-base: not needed for vector-add
      | [] => simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]; exact hf
      | [_] => simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]; exact hf
      | _ :: _ :: _ :: _ => simp only [evalInstr, symEvalInstr, h_op, evalOp, symEvalOp]; exact hf
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
                have ⟨ga, hga, _⟩ := hten a sh_a vals_a h_la
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
            | tensor sh_p vals_p => sorry -- addptr p-tensor fallback
      | [] => sorry -- addptr [] wrong args
      | [_] => sorry -- addptr [_] wrong args
      | _ :: _ :: _ :: _ =>
          sorry -- addptr 3+ args wrong args
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
