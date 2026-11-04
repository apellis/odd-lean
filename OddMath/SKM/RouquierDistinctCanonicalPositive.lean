import OddMath.SKM.RouquierDistinctCanonicalCupRotation
import OddMath.SKM.RouquierDistinctCupPitchfork

/-!
# Canonical distinct left-mate invertibility in the strict cup range

The raw cup identity proved from the Rouquier relations uses precisely
the canonical unscaled left units. Closing it gives the actual
canonical left mate with no additional compatibility premise.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) {Sc : Scalars D k}
  (M : RouquierMulticolour T Sc) {i j : I} (hne : i ≠ j)
  {a b c d : X} (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d)

include M hne in
/-- The exact canonical left mate is invertible in the strict cup
range, measured at the top of its first edge. -/
theorem leftCrossMate_isIso_of_cupRange (hh : D.d i j < D.h i b) :
    IsIso (leftCrossMate (T.leftAdjoints.adjL i hi) (T.leftAdjoints.adjL i hji)
      (T.cross j i hi hij hj hji)) := by
  have hej : (b + D.α i) + D.α j = d + D.α i := by
    rw [← hij]
    abel
  apply T.leftCrossMate_isIso_of_raw_cup M hne hi hj hij hji (Sc.t i j)
  exact T.distinctCupLeft_eq_of_gt M hne hi hj hij hji rfl rfl hej hh

end RouquierFamily
end OddMath.SKM
