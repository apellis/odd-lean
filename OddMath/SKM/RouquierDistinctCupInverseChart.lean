import OddMath.SKM.RouquierDistinctCupTests

/-!
# The inverse of the prescribed distinct cup chart

The cup target chart is inverted by its inverse associator and the
whiskered inverse of the actual right mate. This is the exact-map bridge
from the raw cup identity to canonical left rotation.
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
  {a b c d e : X} (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d) (hnext : d + D.α i = e)

/-- The target inverse is the whiskered inverse of the specified right
mate, with the inverse associator retained. -/
theorem distinctCupTarget_inv :
    letI := T.distinctCupTarget_isIso M hne hi hj hij hji
    letI := M.invNe i j hne hj hji hi hij
    inv (T.distinctCupTarget hi hj hij hji) =
      (associator (T.E j hij) (T.F i hji) (T.E i hji)).inv ≫
      inv (crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij)) ▷ T.E i hji := by
  have := T.distinctCupTarget_isIso M hne hi hj hij hji
  have := M.invNe i j hne hj hji hi hij
  let r := (associator (T.E j hij) (T.F i hji) (T.E i hji)).inv ≫
    inv (crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij)) ▷ T.E i hji
  have hr : T.distinctCupTarget hi hj hij hji ≫ r = 𝟙 _ := by
    dsimp [distinctCupTarget, r]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← TwoSupercategory.comp_whiskerRight (R := k), IsIso.hom_inv_id,
      TwoSupercategory.id_whiskerRight (R := k)]
  change inv (T.distinctCupTarget hi hj hij hji) = r
  calc
    _ = inv (T.distinctCupTarget hi hj hij hji) ≫ (T.distinctCupTarget hi hj hij hji ≫ r) := by
      rw [hr, Category.comp_id]
    _ = r := by rw [IsIso.inv_hom_id_assoc]

/-- The right cup word is the upper raw cup followed by the actual
inverse mate. No independent leftward crossing is chosen. -/
theorem distinctCupRight_eq_inverseMate :
    letI := M.invNe i j hne hj hji hi hij
    T.distinctCupRight M hne hi hj hij hji hnext =
      (rightUnitor (T.E j hij)).inv ≫ T.E j hij ◁ (T.loc i hji hnext).cupL ≫
      (associator (T.E j hij) (T.F i hji) (T.E i hji)).inv ≫
      inv (crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij)) ▷ T.E i hji := by
  have := M.invNe i j hne hj hji hi hij
  rw [distinctCupRight, T.distinctCupTarget_inv M hne hi hj hij hji]

end RouquierFamily
end OddMath.SKM
