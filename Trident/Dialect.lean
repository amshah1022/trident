import SSA

namespace Trident

/-
1. THE TRITON TYPE SYSTEM
Here we declare the types your encoder cared about: integers,
pointers (!tt.ptr<>), and tensors (tensor<...>)
-/
inductive TritonType
  | int (width : Nat)
  | float (width : Nat)
  | ptr (elemTy : TritonType)
  | tensor (shape : List Nat) (elemTy : TritonType)
  deriving TypeName, BEq, DecidableEq

/-
2. THE TRITON OPERATION SET
We map the exact string operations from your Python dictionary
and if/elif blocks into a strongly typed Lean inductive set.
-/
inductive TritonOp
  -- Core hardware/grid parameters
  | get_program_id (axis : Nat)
  -- Memory operations
  | make_range
  | splat
  | addptr
  | load
  | store
  -- Triton layout manipulations
  | expand_dims (axis : Nat)
  | broadcast
  -- Standard Arithmetic Dialect ops used by Triton
  | constant (val : Int)
  | addi | subi | muli
  | divsi | divui | remsi | remui
  deriving BEq, DecidableEq

/-
3. OPERATION SIGNATURES (Pre-conditions and Post-conditions)
This defines what inputs each operation expects and what type it returns,
matching how your encoder processed operands and results.
-/
def TritonOp.signature : TritonOp → List TritonType × TritonType
  | .get_program_id _ => ([], .int 32)
  | .constant _       => ([], .int 32) -- simplified for now
  | .make_range       => ([], .tensor [] (.int 32))
  | .splat            => ([.int 32], .tensor [] (.int 32))
  | .addptr           => ([.ptr (.int 32), .tensor [] (.int 32)], .ptr (.int 32))
  | .load             => ([.ptr (.int 32)], .int 32)
  | .store            => ([.ptr (.int 32), .int 32], .int 0) -- returns void/unit
  | _                 => ([], .int 32) -- Fallback placeholder for arithmetic

end Trident
