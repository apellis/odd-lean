import OddMath.SKM.RouquierDistinctCanonicalNonpositive
import OddMath.SKM.RouquierDistinctCapMiddleIdentity

/-!
# Canonical left-mate invertibility in the cap range

The nonpositive and intermediate cap identities cover Lemma 7.1's full
cap range. Their actual scalar coefficients are units, so the exact
canonical left mate is invertible throughout this range.
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
/-- The actual canonical left mate is invertible in the intermediate
positive cap window, including its raw height sign. -/
theorem leftCrossMate_isIso_of_middle (hpos : 0 < D.h i a) (hbound : D.h i a < D.d i j) :
    IsIso (leftCrossMate (T.leftAdjoints.adjL i hi) (T.leftAdjoints.adjL i hji)
      (T.cross j i hi hij hj hji)) := by
  have he : zsign k (D.parity i * (D.h i a).toNat) *
      zsign k (D.parity i * (D.h i a).toNat) = 1 := by
    unfold zsign
    split_ifs <;> simp
  let e : kˣ := ⟨zsign k (D.parity i * (D.h i a).toNat),
    zsign k (D.parity i * (D.h i a).toNat), he, he⟩
  apply T.leftCrossMate_isIso_of_raw_cap M hne hi hj hij hji (e * Sc.t i j)
  exact T.distinctCap_of_middle M hne (sub_add_cancel a (D.α i)) hi hj hij hji
    (sub_add_cancel c (D.α i)) hpos hbound

include M hne in
/-- The exact canonical left mate is invertible over the complete cap
range of Lemma 7.1. The complementary cup range is not asserted here. -/
theorem leftCrossMate_isIso_of_capRange (hh : D.h i a ≤ max (D.d i j - 1) 0) :
    IsIso (leftCrossMate (T.leftAdjoints.adjL i hi) (T.leftAdjoints.adjL i hji)
      (T.cross j i hi hij hj hji)) := by
  by_cases hnonpos : D.h i a ≤ 0
  · exact T.leftCrossMate_isIso_of_nonpos M hne hi hj hij hji hnonpos
  · exact T.leftCrossMate_isIso_of_middle M hne hi hj hij hji (by omega) (by omega)

end RouquierFamily
end OddMath.SKM
