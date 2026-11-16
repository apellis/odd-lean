import OddMath.SKM.RouquierDistinctCanonicalRotation
import OddMath.SKM.RouquierDistinctCapNonpositive

/-!
# Canonical distinct left-mate invertibility at nonpositive height

The exact raw cap identity proved from the Rouquier relations is
normalized by the canonical scalar units and contracted with the
canonical left cup. No cap or left-mate hypothesis remains.
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
/-- Actual canonical distinct left mates are invertible in the entire
nonpositive-height range. The positive-height ranges remain separate. -/
theorem leftCrossMate_isIso_of_nonpos (hh : D.h i a ≤ 0) :
    IsIso (leftCrossMate (T.leftAdjoints.adjL i hi) (T.leftAdjoints.adjL i hji)
      (T.cross j i hi hij hj hji)) := by
  apply T.leftCrossMate_isIso_of_raw_cap M hne hi hj hij hji (Sc.t i j)
  exact T.distinctCap_of_nonpos M hne (sub_add_cancel a (D.α i)) hi hj hij hji
    (sub_add_cancel c (D.α i)) hh

end RouquierFamily
end OddMath.SKM
