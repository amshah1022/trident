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
  | load : Expr → Expr
  deriving Repr, DecidableEq

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
  | .load addr => mem (evalExpr addr mem).natAbs

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
  | .load addr =>
      match normalizeExpr addr mem with
      | .lit n => mem n.natAbs
      | naddr  => .load naddr

-- ── Helper: normalize with vector-add memory layout ──────────────────────────

def normalizeWithMem (e : Expr) (n : Nat) : Expr :=
  normalizeExpr e (fun addr =>
    if addr < n then Expr.var "a" addr
    else if addr < 2 * n then Expr.var "b" (addr - n)
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
  | some (SymValue.tensor m xs), some (SymValue.tensor _ ys) =>
      some (SymValue.tensor m (fun i => Expr.add (xs i) (ys i)))
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
  | .make_range =>
      some (SymValue.tensor s.block_size (fun i => Expr.lit (Int.ofNat i)))
  | .splat =>
      match args with
      | [v] => match s.lookup v with
        | some (SymValue.scalar e) =>
            some (SymValue.tensor s.block_size (fun _ => e))
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
  | .maxsi => match args with
      | [a, b] => symMax (s.lookup a) (s.lookup b)
      | _ => none
  | .muli =>
      match args with
      | [a, b] => match s.lookup a, s.lookup b with
        | some (SymValue.scalar x), some (SymValue.scalar y) =>
            some (SymValue.scalar (Expr.mul x y))
        | _, _ => none
      | _ => none
  | .load =>
      match args with
      | [p] => match s.lookup p with
        | some (SymValue.tensor n addrs) =>
            some (SymValue.tensor n (fun i => Expr.load (addrs i)))
        | some (SymValue.scalar addr) =>
            some (SymValue.scalar (Expr.load addr))
        | _ => none
      | _ => none
  | .store => none
  | _ => none

-- ── Symbolic Instruction + Kernel Execution ───────────────────────────────────

def symEvalInstr (instr : TritonInstr) (s : SymState) : SymState :=
  match instr.op with
  | .store =>
      match instr.args with
      | [p, v] => match s.lookup p, s.lookup v with
        | some (SymValue.tensor n addrs), some (SymValue.tensor _ vals) =>
            List.foldl (fun st i =>
              let addr := (evalExpr (addrs i) (fun _ => 0)).natAbs
              st.writeMem addr (vals i)) s (List.range n)
        | _, _ => s
      | _ => s
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
      else if addr < 2 * n then Expr.var "b" (addr - n)
      else Expr.lit 0
  , env        := fun v => match v with
      | "a_base" => some (SymValue.scalar (Expr.lit 0))
      | "b_base" => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | "c_base" => some (SymValue.scalar (Expr.lit (Int.ofNat (2 * n))))
      | "arg0"   => some (SymValue.scalar (Expr.lit 0))
      | "arg1"   => some (SymValue.scalar (Expr.lit (Int.ofNat n)))
      | "arg2"   => some (SymValue.scalar (Expr.lit (Int.ofNat (2 * n))))
      | "bsize"  => some (SymValue.scalar (Expr.lit (Int.ofNat bs)))
      | _        => none }

def vectorAddSpecExpr (pid bs i : Nat) : Expr :=
  Expr.add (Expr.var "a" (pid * bs + i)) (Expr.var "b" (pid * bs + i))

def symCheckVectorAdd (kernel : TritonKernel) (pid bs gs n i : Nat) : Bool :=
  let s' := symEvalKernel kernel (symVectorAddInitState pid bs gs n)
  let raw  := s'.memory (2 * n + pid * bs + i)
  let norm := normalizeWithMem raw n
  norm == vectorAddSpecExpr pid bs i

end Trident
