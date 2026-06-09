namespace Trident

/-
THE FUNCTIONAL SPECIFICATION (The Golden Model)
This is pure, high-level math. It does not know what a GPU,
a pointer, a tile, or an MLIR instruction is.
-/
def VectorAddSpec (vectorA : List Int) (vectorB : List Int) : List Int :=
  List.zipWith (fun a b => a + b) vectorA vectorB

end Trident
