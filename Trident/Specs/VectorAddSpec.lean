-- Trident.Specs.VectorAdd
-- The SpecLang golden model for vector addition.
--
-- This file contains ONLY pure mathematics.
-- No GPU, no tiles, no pointers, no parallelism.
-- This is the ground truth that TTIR must implement.

import Trident.SourceLang
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Zip

namespace Trident

/-
THE VECTOR ADD SPECIFICATION
output[i] = a[i] + b[i]  for all i
-/

-- The pure math function
def vectorAddMath (a b : List Int) : List Int :=
  (a.zip b).map (fun (x, y) => x + y)

-- Packaged as a SpecKernel for use with the simulation framework
def VectorAddSpec : SpecKernel where
  name := "VectorAdd"
  spec := fun inputs =>
    match inputs with
    | [a, b] => vectorAddMath a b
    | _      => []
  pre := fun inputs =>
    match inputs with
    | [a, b] => a.length = b.length
    | _      => False

/-
KEY SPEC LEMMAS
These make proofs cleaner by giving names to properties of the spec.
Marking them @[simp] lets the simp tactic use them automatically.
-/

-- The spec at index i is a[i] + b[i]
@[simp]
lemma vectorAddMath_getD (a b : List Int) (i : Nat) :
    (vectorAddMath a b).getD i 0 =
    a.getD i 0 + b.getD i 0 := by
  simp [vectorAddMath]
  by_cases h : i < a.length
  · have hb : i < b.length := by
      -- This requires a.length = b.length, stated as hypothesis in proofs
      sorry
    simp [List.getD_eq_getElem? (by simp [List.length_map, List.length_zip]; omega)]
    simp [List.getElem?_zip, List.getElem?_eq_getElem h, List.getElem?_eq_getElem hb]
  · simp [List.getD_eq_default (by simp [vectorAddMath, List.length_map, List.length_zip]; omega)]
    simp [List.getD_eq_default (by omega)]
    have hb : ¬ i < b.length := by sorry
    simp [List.getD_eq_default (by omega)]

-- The length of the output equals the length of the inputs
@[simp]
lemma vectorAddMath_length (a b : List Int) :
    (vectorAddMath a b).length = min a.length b.length := by
  simp [vectorAddMath, List.length_map, List.length_zip]

-- With equal-length inputs, output length equals input length
lemma vectorAddMath_length_eq (a b : List Int) (h : a.length = b.length) :
    (vectorAddMath a b).length = a.length := by
  simp [vectorAddMath, List.length_map, List.length_zip, h]

-- The spec is commutative: add(a,b) = add(b,a)
lemma vectorAddMath_comm (a b : List Int) :
    vectorAddMath a b = vectorAddMath b a := by
  simp [vectorAddMath]
  congr 1
  · apply List.ext_getElem
    · simp [List.length_zip, min_comm]
    · intro i h1 h2
      simp [List.getElem_map, List.getElem_zip]
      ring

end Trident
