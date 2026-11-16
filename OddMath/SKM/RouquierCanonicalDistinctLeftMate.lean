import OddMath.SKM.RouquierDistinctCanonicalCapRange
import OddMath.SKM.RouquierDistinctCanonicalPositive

/-!
# Canonical distinct left-mate invertibility

The actual inverse-defined canonical left adjunctions satisfy the
missing distinct left-mate condition. The cap range and shifted strict
cup range cover every weight. Their identities were derived from the
Rouquier relations, without a new action or cyclicity premise.
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
  (M : RouquierMulticolour T Sc)

include M in
/-- The canonical left adjunctions satisfy distinct left-mate
invertibility at every weight, from the actual multicolour relations. -/
theorem canonicalLeftMateInvertible : LeftMateInvertible T T.leftAdjoints := by
  intro i j hne a b c d hi hij hj hji
  by_cases hh : D.h i a ≤ max (D.d i j - 1) 0
  · exact T.leftCrossMate_isIso_of_capRange M hne hi hj hij hji hh
  · have hb : D.h i b = D.h i a + 2 := by
      rw [← hi]
      simp [Datum.h, Datum.α, map_add, D.cd.coroot_root_self]
    exact T.leftCrossMate_isIso_of_cupRange M hne hi hj hij hji (by omega)

end RouquierFamily
end OddMath.SKM
