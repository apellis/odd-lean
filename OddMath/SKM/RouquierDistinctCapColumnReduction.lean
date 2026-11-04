import OddMath.SKM.RouquierDistinctDottedUnit
import OddMath.SKM.RouquierDistinctCapDetection
import OddMath.SKM.RouquierDistinctMixedBraid

/-!
# The finite distinct cap-column reduction

The exact left cap word, precomposed with the prescribed distinct source
chart and a dotted cup, is the upper dotted cup followed by the upward
quadratic word and the inverse-defined upper cap. This is the
bicategorical form of Brundan–Ellis Lemma 7.1, `pfL_b_reduce`.
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
  {a₀ a b c₀ c d : X} (h₀ : a₀ + D.α i = a)
  (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d) (hprev : c₀ + D.α i = c)

/-- The actual upward crossing followed by the upper inverse-defined cap. -/
def distinctCapLeft : (T.E i hi ≫ T.E j hij) ≫ T.F i hji ⟶ T.E j hj :=
  T.cross j i hi hij hj hji ▷ T.F i hji ≫
    (associator (T.E j hj) (T.E i hji) (T.F i hji)).hom ≫
    T.E j hj ◁ (T.loc i hprev hji).capL ≫ (rightUnitor (T.E j hj)).hom

omit [TwoSupercategory k B] in
/-- The principal left test is exactly the mixed-braid word already
computed by the correction-monomial argument. -/
theorem distinctCapLeft_principal_word :
    (T.loc i h₀ hi).sig ▷ T.E j hj ≫ T.distinctCapSource hi hj hij hji ≫
      T.distinctCapLeft hi hj hij hji hprev =
    T.distinctMixedBraidLeft i j h₀ hj hi hji hij ≫
      T.E j hj ◁ (T.loc i hprev hji).capL ≫ (rightUnitor (T.E j hj)).hom := by
  simp only [distinctCapSource, distinctCapLeft, distinctMixedBraidLeft, Category.assoc,
    crossMate_eq_rouquierMate]
  rfl

include M hne in
/-- Every finite left cup column reduces to the actual upper quadratic
word; the two dot-transport signs have already cancelled. -/
theorem distinctCapLeft_column_reduce (n : ℕ) :
    (leftUnitor (T.E j hj)).inv ≫ (T.loc i h₀ hi).cupD n ▷ T.E j hj ≫
      T.distinctCapSource hi hj hij hji ≫ T.distinctCapLeft hi hj hij hji hprev =
    (rightUnitor (T.E j hj)).inv ≫ T.E j hj ◁ (T.loc i hprev hji).cupD n ≫
      (associator (T.E j hj) (T.E i hji) (T.F i hji)).inv ≫
      (T.cross i j hj hji hi hij ≫ T.cross j i hi hij hj hji) ▷ T.F i hji ≫
      (associator (T.E j hj) (T.E i hji) (T.F i hji)).hom ≫
      T.E j hj ◁ (T.loc i hprev hji).capL ≫ (rightUnitor (T.E j hj)).hom := by
  have hu := T.distinctCrossMate_dottedUnit M i j hne hj hji hi hij n
  change (leftUnitor (T.E j hj)).inv ≫ (T.loc i h₀ hi).cupD n ▷ T.E j hj ≫
      (associator (T.E i hi) (T.F i hi) (T.E j hj)).hom ≫
      T.E i hi ◁ crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij) =
    (rightUnitor (T.E j hj)).inv ≫ T.E j hj ◁ (T.loc i hprev hji).cupD n ≫
      (associator (T.E j hj) (T.E i hji) (T.F i hji)).inv ≫
      T.cross i j hj hji hi hij ▷ T.F i hji ≫
      (associator (T.E i hi) (T.E j hij) (T.F i hji)).hom at hu
  unfold distinctCapSource distinctCapLeft
  simp only [Category.assoc, TwoSupercategory.comp_whiskerRight (R := k)]
  rw [reassoc_of% hu]
  simp only [Iso.hom_inv_id_assoc]

end RouquierFamily
end OddMath.SKM
