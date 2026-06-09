-- Trident.Dialect
-- The Triton type system and operation AST.
-- This is the "target language" in CompCert terms —
-- the IR whose semantics we formally define.

import Mathlib.Data.List.Basic

namespace Trident

/-
1. THE TRITON TYPE SYSTEM
Models the types that appear in Triton IR:
  - Scalars: i32, f32, etc.
  - Pointers: !tt.ptr<i32> etc.
  - Tensors: tensor<1024xi32> etc.
-/
inductive TritonType
  | int   (width : Nat)
  | float (width : Nat)
  | ptr   (elemTy : TritonType)
  | tensor (shape : List Nat) (elemTy : TritonType)
  deriving BEq, DecidableEq, Repr

/-
2. THE TRITON OPERATION SET
Every op that can appear in a Triton kernel's TTIR.
We cover the full set needed for: vector ops, matmul, attention.
-/
inductive TritonOp
  -- Grid/program ID
  | get_program_id (axis : Nat)
  -- Range and pointer arithmetic
  | make_range
  | splat
  | addptr
  | expand_dims (axis : Nat)
  | broadcast
  -- Memory
  | load
  | store
  -- Integer arithmetic
  | constant (val : Int)
  | addi | subi | muli
  | divsi | divui
  | remsi | remui
  -- Float arithmetic (needed for matmul, attention)
  | addf | subf | mulf | divf
  -- Comparison (needed for masking)
  | cmpi_slt | cmpi_sle | cmpi_eq
  -- Reduction ops (needed for softmax, layer norm)
  | reduce_add | reduce_max
  -- Dot product (needed for matmul)
  | dot
  deriving BEq, DecidableEq, Repr

/-
3. OPERATION SIGNATURES
What types each operation consumes and produces.
This is the typechecking contract — used by the interpreter
to validate IR before attempting to execute it.
-/
def TritonOp.signature : TritonOp → List TritonType × TritonType
  | .get_program_id _  => ([], .int 32)
  | .constant _        => ([], .int 32)
  | .make_range        => ([], .tensor [] (.int 32))
  | .splat             => ([.int 32], .tensor [] (.int 32))
  | .addptr            => ([.ptr (.int 32), .tensor [] (.int 32)], .ptr (.int 32))
  | .expand_dims _     => ([.tensor [] (.int 32)], .tensor [] (.int 32))
  | .broadcast         => ([.tensor [] (.int 32)], .tensor [] (.int 32))
  | .load              => ([.ptr (.int 32)], .int 32)
  | .store             => ([.ptr (.int 32), .int 32], .int 0)
  | .addi              => ([.int 32, .int 32], .int 32)
  | .subi              => ([.int 32, .int 32], .int 32)
  | .muli              => ([.int 32, .int 32], .int 32)
  | .addf              => ([.float 32, .float 32], .float 32)
  | .mulf              => ([.float 32, .float 32], .float 32)
  | .dot               => ([.tensor [] (.float 32), .tensor [] (.float 32)], .tensor [] (.float 32))
  | .reduce_add        => ([.tensor [] (.int 32)], .int 32)
  | .reduce_max        => ([.tensor [] (.int 32)], .int 32)
  | _                  => ([], .int 32)

/-
4. IR PROGRAM REPRESENTATION
A Triton IR program is a sequence of named instructions.
Each instruction binds a result variable to an operation applied to argument variables.
This is the SSA form that Triton's compiler produces.
-/
structure TritonInstr where
  result : String        -- The SSA variable this instruction defines
  op     : TritonOp      -- The operation
  args   : List String   -- The SSA variables this instruction consumes
  deriving Repr

-- A complete kernel is a list of instructions in SSA order
abbrev TritonKernel := List TritonInstr

end Trident
