-- Trident.Common.Values
-- Runtime values that exist during Triton kernel execution.
-- Shared between Source and Target languages.
--
-- CompCert equivalent: common/Values.v

namespace Trident

/--
A `TritonValue` is the data that lives in a register during execution.
Either a single scalar integer, or a tile (tensor) of integers.

We work over `Int` (arbitrary precision) rather than `Int32` for now.
This avoids bitvector overflow complications during initial proof development.
Bitvector semantics can be added as a refinement later.
-/
inductive TritonValue where
  | scalar (val : Int)
  | tensor (shape : List Nat) (vals : List Int)
  deriving BEq, Repr

namespace TritonValue

-- Smart constructors for common cases
def scalar0 : TritonValue := scalar 0
def tile (bs : Nat) (vals : List Int) : TritonValue := tensor [bs] vals

-- Accessors
def isScalar : TritonValue → Bool
  | scalar _ => true
  | _        => false

def isTensor : TritonValue → Bool
  | tensor _ _ => true
  | _          => false

def asScalar : TritonValue → Option Int
  | scalar v => some v
  | _        => none

def asTensor : TritonValue → Option (List Nat × List Int)
  | tensor s vs => some (s, vs)
  | _           => none

/-- Element-wise map over a TritonValue -/
def map (f : Int → Int) : TritonValue → TritonValue
  | scalar v      => scalar (f v)
  | tensor s vals => tensor s (vals.map f)

/-- Element-wise zip of two TritonValues with the same shape -/
def zipWith (f : Int → Int → Int) : TritonValue → TritonValue → Option TritonValue
  | scalar x,      scalar y      => some (scalar (f x y))
  | tensor s1 xs,  tensor s2 ys  =>
      if s1 == s2
      then some (tensor s1 ((xs.zip ys).map (fun (x, y) => f x y)))
      else none
  | _,             _             => none

end TritonValue
end Trident
