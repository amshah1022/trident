import Trident.Dialect

namespace Trident

/-
The runtime values that can exist inside a Triton execution environment.
Variables can either be individual scalars or multi-dimensional tiles.
-/
inductive TritonValue
  | scalar (val : Int)
  | tensor (shape : List Nat) (vals : List Int)
  deriving BEq, Repr -- Fixed: Changed 'Show' to 'Repr'

structure MachineState where
  pid        : Nat
  block_size : Nat
  grid_size  : Nat
  memory     : Nat → Int
  env        : String → Option TritonValue

end Trident
