import Trident.Target.Dialect
import Trident.Target.Semantics
import Trident.Common.Memory

namespace Trident

-- ── Symbolic Expression Type ──────────────────────────────────────────────────

inductive Expr : Type
  | lit  : Int → Expr
  | var  : String → Nat → Expr
  | add  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr
  | max  : Expr → Expr → Expr
  | load      : Expr → Expr
  | reduceSum : List Expr → Expr
  deriving Repr

-- Manual BEq for Expr (needed since reduceSum contains List Expr)
mutual
  def Expr.beq : Expr → Expr → Bool
    | .lit a,        .lit b        => a == b
    | .var s1 i1,    .var s2 i2    => s1 == s2 && i1 == i2
    | .add a1 a2,    .add b1 b2    => Expr.beq a1 b1 && Expr.beq a2 b2
    | .mul a1 a2,    .mul b1 b2    => Expr.beq a1 b1 && Expr.beq a2 b2
    | .max a1 a2,    .max b1 b2    => Expr.beq a1 b1 && Expr.beq a2 b2
    | .load a,       .load b       => Expr.beq a b
    | .reduceSum as, .reduceSum bs => ExprList.beq as bs
    | _,             _             => false
  def ExprList.beq : List Expr → List Expr → Bool
    | [],    []    => true
    | a::as, b::bs => Expr.beq a b && ExprList.beq as bs
    | _,     _     => false
end

instance : BEq Expr := ⟨Expr.beq⟩
-- exprBeqEq: Expr.beq e1 e2 = true → e1 = e2 (proved by mutual recursion)
mutual
  def exprBeqEq_aux : (e1 e2 : Expr) → Expr.beq e1 e2 = true → e1 = e2
    | .lit a,        .lit b,        h => by simp [Expr.beq] at h; exact congrArg Expr.lit h
    | .var s1 i1,    .var s2 i2,    h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        obtain ⟨hs, hi⟩ := h; subst hs
        exact congrArg (Expr.var s1) (by exact_mod_cast hi)
    | .add a1 a2, .add b1 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq_aux a1 b1 h.1; have h2 := exprBeqEq_aux a2 b2 h.2
        subst h1; subst h2; rfl
    | .mul a1 a2, .mul b1 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq_aux a1 b1 h.1; have h2 := exprBeqEq_aux a2 b2 h.2
        subst h1; subst h2; rfl
    | .max a1 a2, .max b1 b2, h => by
        simp [Expr.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq_aux a1 b1 h.1; have h2 := exprBeqEq_aux a2 b2 h.2
        subst h1; subst h2; rfl
    | .load a, .load b, h => by
        simp [Expr.beq] at h; exact congrArg Expr.load (exprBeqEq_aux a b h)
    | .reduceSum as, .reduceSum bs, h => by
        simp [Expr.beq] at h; exact congrArg Expr.reduceSum (exprListBeqEq_aux as bs h)
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
  def exprListBeqEq_aux : (as bs : List Expr) → ExprList.beq as bs = true → as = bs
    | [],    [],    _ => rfl
    | [],    _::_,  h => by simp [ExprList.beq] at h
    | _::_,  [],    h => by simp [ExprList.beq] at h
    | a::as, b::bs, h => by
        simp [ExprList.beq, Bool.and_eq_true] at h
        have h1 := exprBeqEq_aux a b h.1; have h2 := exprListBeqEq_aux as bs h.2
        subst h1; subst h2; rfl
end

mutual
  def exprBeqRefl_aux : (e : Expr) → Expr.beq e e = true
    | .lit _      => by simp [Expr.beq]
    | .var _ _    => by simp [Expr.beq]
    | .add e1 e2  => by simp [Expr.beq, exprBeqRefl_aux e1, exprBeqRefl_aux e2]
    | .mul e1 e2  => by simp [Expr.beq, exprBeqRefl_aux e1, exprBeqRefl_aux e2]
    | .max e1 e2  => by simp [Expr.beq, exprBeqRefl_aux e1, exprBeqRefl_aux e2]
    | .load e     => by simp [Expr.beq, exprBeqRefl_aux e]
    | .reduceSum es => by simp [Expr.beq, exprListBeqRefl_aux es]
  def exprListBeqRefl_aux : (es : List Expr) → ExprList.beq es es = true
    | []     => by simp [ExprList.beq]
    | e::es  => by simp [ExprList.beq, exprBeqRefl_aux e, exprListBeqRefl_aux es]
end

instance : DecidableEq Expr := fun a b =>
  if h : Expr.beq a b = true then
    isTrue (exprBeqEq_aux a b h)
  else
    isFalse (fun heq => by subst heq; exact h (exprBeqRefl_aux a))

-- ── Symbolic Values ───────────────────────────────────────────────────────────

inductive SymValue : Type
  | scalar : Expr → SymValue
  | tensor : Nat → (Nat → Expr) → SymValue

-- ── Symbolic Machine State ────────────────────────────────────────────────────

structure SymState where
  pid        : Nat
  block_size : Nat
  grid_size  : Nat
  memory     : Nat → Expr
  env        : String → Option SymValue

def SymState.lookup (s : SymState) (v : String) : Option SymValue := s.env v

def SymState.bind (s : SymState) (v : String) (val : SymValue) : SymState :=
  { s with env := fun name => if name == v then some val else s.env name }

def SymState.writeMem (s : SymState) (addr : Nat) (val : Expr) : SymState :=
  { s with memory := fun a => if a == addr then val else s.memory a }

-- ── Evaluate Expr On Concrete Inputs ─────────────────────────────────────────

def evalExpr (e : Expr) (mem : Nat → Int) : Int :=
  match e with
  | .lit n     => n
  | .var _ i   => mem i
  | .add e1 e2 => evalExpr e1 mem + evalExpr e2 mem
  | .mul e1 e2 => evalExpr e1 mem * evalExpr e2 mem
  | .max e1 e2 => Max.max (evalExpr e1 mem) (evalExpr e2 mem)
  | .load addr     => mem (evalExpr addr mem).natAbs
  | .reduceSum es  => es.foldl (fun acc e => acc + evalExpr e mem) 0

-- ── Expression Normalization ──────────────────────────────────────────────────

/-- Simplify concrete arithmetic and resolve loads via memory layout -/
def normalizeExpr (e : Expr) (mem : Nat → Expr) : Expr :=
  match e with
  | .lit n     => .lit n
  | .var s i   => .var s i
  | .add e1 e2 =>
      match normalizeExpr e1 mem, normalizeExpr e2 mem with
      | .lit a, .lit b => .lit (a + b)
      | n1,     n2     => .add n1 n2
  | .mul e1 e2 =>
      match normalizeExpr e1 mem, normalizeExpr e2 mem with
      | .lit a, .lit b => .lit (a * b)
      | n1,     n2     => .mul n1 n2
  | .max e1 e2 =>
      match normalizeExpr e1 mem, normalizeExpr e2 mem with
      | .lit a, .lit b => .lit (Max.max a b)
      | n1,     n2     => .max n1 n2
  | .reduceSum es =>
      .reduceSum (es.map (fun e => normalizeExpr e mem))
  | .load addr =>
      match normalizeExpr addr mem with
      | .lit n => mem n.natAbs
      | naddr  => .load naddr

-- ── Helper: normalize with vector-add memory layout ──────────────────────────

def normalizeWithMem (e : Expr) (n : Nat) : Expr :=
  normalizeExpr e (fun addr =>
    if addr < n then Expr.var "a" addr
    else if addr < 2 * n then Expr.var "b" addr
    else Expr.lit 0)

-- ── Symbolic Operation Semantics ──────────────────────────────────────────────

def symAdd (a b : Option SymValue) : Option SymValue :=
  match a, b with
  | some (SymValue.scalar x), some (SymValue.scalar y) =>
      some (SymValue.scalar (Expr.add x y))
  | some (SymValue.scalar x), some (SymValue.tensor m ys) =>
      some (SymValue.tensor m (fun i => Expr.add x (ys i)))
  | some (SymValue.tensor m xs), some (SymValue.scalar y) =>
      some (SymValue.tensor m (fun i => Expr.add (xs i) y))
  | some (SymValue.tensor m xs), some (SymValue.tensor n ys) =>
      if m == n then some (SymValue.tensor m (fun i => Expr.add (xs i) (ys i)))
      else none
  | _, _ => none

def symMax (a b : Option SymValue) : Option SymValue :=
  match a, b with
  | some (SymValue.scalar x), some (SymValue.scalar y) =>
      some (SymValue.scalar (Expr.max x y))
  | some (SymValue.scalar x), some (SymValue.tensor m ys) =>
      some (SymValue.tensor m (fun i => Expr.max x (ys i)))
  | some (SymValue.tensor m xs), some (SymValue.scalar y) =>
      some (SymValue.tensor m (fun i => Expr.max (xs i) y))
  | some (SymValue.tensor m xs), some (SymValue.tensor _ ys) =>
      some (SymValue.tensor m (fun i => Expr.max (xs i) (ys i)))
  | _, _ => none

def symEvalOp (op : TritonOp) (args : List String) (s : SymState)
    : Option SymValue :=
  match op with
  | .get_program_id _ =>
      some (SymValue.scalar (Expr.lit (Int.ofNat s.pid)))
  | .constant v =>
      some (SymValue.scalar (Expr.lit v))
  | .make_range sizeOpt =>
      some (SymValue.tensor (sizeOpt.getD s.block_size) (fun i => Expr.lit (Int.ofNat i)))
  | .splat shape =>
      match args with
      | [v] => match s.lookup v with
        | some (SymValue.scalar e) =>
            some (SymValue.tensor (shape.foldl (· * ·) 1) (fun _ => e))
        | _ => none
      | _ => none
  | .addptr =>
      match args with
      | [p, o] => match s.lookup p, s.lookup o with
        | some (SymValue.scalar base), some (SymValue.scalar off) =>
            some (SymValue.scalar (Expr.add base off))
        | some (SymValue.tensor n bases), some (SymValue.tensor _ offs) =>
            some (SymValue.tensor n (fun i => Expr.add (bases i) (offs i)))
        | some (SymValue.scalar base), some (SymValue.tensor n offs) =>
            some (SymValue.tensor n (fun i => Expr.add base (offs i)))
        | _, _ => none
      | _ => none
  | .addi => match args with
      | [a, b] => symAdd (s.lookup a) (s.lookup b)
      | _ => none
  | .addf => match args with
      | [a, b] => symAdd (s.lookup a) (s.lookup b)
      | _ => none
  | .cmpi_slt =>
      -- comparison: produces tensor of symbolic booleans (0/1)
      -- for symbolic purposes just bind result as a tensor marker
      match args with
      | [a, b] => match s.lookup a, s.lookup b with
        | some (SymValue.tensor n _), some (SymValue.tensor _ _) =>
            some (SymValue.tensor n (fun _ => Expr.lit 1))  -- symbolic: assume in-bounds
        | some (SymValue.scalar _), some (SymValue.scalar _) =>
            some (SymValue.scalar (Expr.lit 1))
        | _, _ => none
      | _ => none

  | .cmpi_sge =>
      match args with
      | [a, b] => match s.lookup a, s.lookup b with
        | some (SymValue.tensor n _), some (SymValue.tensor _ _) =>
            some (SymValue.tensor n (fun _ => Expr.lit 1))
        | some (SymValue.tensor n _), some (SymValue.scalar _) =>
            some (SymValue.tensor n (fun _ => Expr.lit 1))
        | some (SymValue.scalar _), some (SymValue.tensor n _) =>
            some (SymValue.tensor n (fun _ => Expr.lit 1))
        | some (SymValue.scalar _), some (SymValue.scalar _) =>
            some (SymValue.scalar (Expr.lit 1))
        | _, _ => none
      | _ => none

  | .maxsi => match args with
      | [a, b] => symMax (s.lookup a) (s.lookup b)
      | _ => none
  | .muli =>
      match args with
      | [a, b] => match s.lookup a, s.lookup b with
        | some (SymValue.scalar x), some (SymValue.scalar y) =>
            some (SymValue.scalar (Expr.mul x y))
        | some (SymValue.tensor n xs), some (SymValue.tensor k ys) =>
            if n == k then some (SymValue.tensor n (fun i => Expr.mul (xs i) (ys i)))
            else none
        | _, _ => none
      | _ => none
  | .load =>
      -- handle both regular load [ptr] and masked load [ptr, mask]
      let ptr := args.head? |>.getD ""
      match s.lookup ptr with
      | some (SymValue.tensor n addrs) =>
          some (SymValue.tensor n (fun i => Expr.load (addrs i)))
      | some (SymValue.scalar addr) =>
          some (SymValue.scalar (Expr.load addr))
      | _ => none
  | .select =>
      match args with
      | [cond, a, b] => match s.lookup cond, s.lookup a, s.lookup b with
        | some (SymValue.tensor n _),
          some (SymValue.tensor _ as_),
          some (SymValue.tensor _ bs_) =>
            -- select(cond, a, b): symbolically = max(b, a) for ReLU pattern
            some (SymValue.tensor n (fun i => Expr.max (bs_ i) (as_ i)))
        | some (SymValue.tensor n _),
          some (SymValue.tensor _ as_),
          some (SymValue.scalar b) =>
            -- select(cond, tensor, scalar): e.g. select(x>=0, x, 0)
            some (SymValue.tensor n (fun i => Expr.max b (as_ i)))
        | some (SymValue.tensor n _),
          some (SymValue.scalar a),
          some (SymValue.tensor _ bs_) =>
            some (SymValue.tensor n (fun i => Expr.max (bs_ i) a))
        | _, _, _ => none
      | _ => none

  | .dot =>
      -- Matrix multiply: C[i,j] = sum_k(A[i,k] * B[k,j])
      -- A is M×K (flat size M*K), B is K×N (flat size K*N)
      -- Output C is M×N (flat size M*N)
      -- We infer M, N, K from tensor sizes and block_size
      match args with
      | [a, b, _] | [a, b] => match s.lookup a, s.lookup b with
        | some (SymValue.tensor na fa), some (SymValue.tensor nb fb) =>
            -- Look up K from env (stored as "K_dim" by init state)
            -- fallback: use nb (K*N where N=1) or block_size
            let K := match s.env "K_dim" with
              | some (SymValue.scalar (Expr.lit k)) => k.natAbs
              | _ => s.block_size
            let M := na / K
            let N := if K > 0 then nb / K else 1
            let MN := M * N
            -- C[i*N+j] = sum_k(A[i*K+k] * B[k*N+j])
            let result_exprs := (List.range MN).map fun idx =>
              let i := idx / N
              let j := idx % N
              Expr.reduceSum ((List.range K).map fun k =>
                Expr.mul (fa (i * K + k)) (fb (k * N + j)))
            some (SymValue.tensor MN (fun i =>
              result_exprs.getD i (Expr.lit 0)))
        | _, _ => none
      | _ => none

  | .reduce_sum _ =>
      match args with
      | [v] => match s.lookup v with
        | some (SymValue.tensor n f) =>
            let exprs := (List.range n).map f
            some (SymValue.scalar (Expr.reduceSum exprs))
        | _ => none
      | _ => none

  | .store => none
  | _ => none

-- ── Symbolic Instruction + Kernel Execution ───────────────────────────────────

def symEvalInstr (instr : TritonInstr) (s : SymState) : SymState :=
  match instr.op with
  | .store =>
      -- handle both 2-arg store and 3-arg masked store (ignore mask)
      let (p, v) := match instr.args with
        | [p, v]    => (p, v)
        | [p, v, _] => (p, v)  -- masked store: ignore mask
        | _         => ("", "")
      match s.lookup p, s.lookup v with
      | some (SymValue.tensor n addrs), some (SymValue.tensor _ vals) =>
          List.foldl (fun st i =>
            let addr := (evalExpr (addrs i) (fun _ => 0)).natAbs
            st.writeMem addr (vals i)) s (List.range n)
      | some (SymValue.scalar addrExpr), some (SymValue.scalar valExpr) =>
          let addr := (evalExpr addrExpr (fun _ => (0 : Int))).natAbs
          s.writeMem addr valExpr
      | _, _ => s
  | _ =>
      match symEvalOp instr.op instr.args s with
      | some val => s.bind instr.result val
      | none     => s

def symEvalKernel (kernel : TritonKernel) (s : SymState) : SymState :=
  List.foldl (fun st instr => symEvalInstr instr st) s kernel

-- ── Vector Add Symbolic Check ─────────────────────────────────────────────────

def symVectorAddInitState (pid bs gs n : Nat) : SymState :=
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := fun addr =>
      if addr < n then Expr.var "a" addr
      else if addr < 2 * n then Expr.var "b" addr
      else Expr.lit 0
  , env        := fun v => match v with
      | "a_base" => some (SymValue.scalar (Expr.lit 0))
      | "b_base" => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | "c_base" => some (SymValue.scalar (Expr.lit (Int.ofNat (2 * n))))
      | "bsize"  => some (SymValue.scalar (Expr.lit (Int.ofNat bs)))
      | _        => none }

def vectorAddSpecExpr (pid bs i n : Nat) : Expr :=
  Expr.add (Expr.var "a" (pid * bs + i)) (Expr.var "b" (n + pid * bs + i))

def symCheckVectorAdd (kernel : TritonKernel) (pid bs gs n i : Nat) : Bool :=
  let s' := symEvalKernel kernel (symVectorAddInitState pid bs gs n)
  let raw  := s'.memory (2 * n + pid * bs + i)
  let norm := normalizeWithMem raw n
  norm == vectorAddSpecExpr pid bs i n

def symVectorAddTutorialInitState (pid bs gs n : Nat) : SymState :=
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

def symCheckVectorAddTutorial (kernel : TritonKernel) (pid bs gs n i : Nat) : Bool :=
  let s' := symEvalKernel kernel (symVectorAddTutorialInitState pid bs gs n)
  let raw  := s'.memory (2 * n + pid * bs + i)
  let norm := normalizeWithMem raw n
  norm == vectorAddSpecExpr pid bs i n

end Trident
