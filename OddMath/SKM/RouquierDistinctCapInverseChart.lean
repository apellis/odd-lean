import OddMath.SKM.RouquierDistinctCapTests

/-!
# The inverse of the prescribed distinct cap chart

The inverse source chart is the whiskered inverse of the actual right
mate, with both associators retained. This identifies the exact map in
the raw cap pitchfork with the map used in left rotation.
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
  {a₀ a b c d : X} (h₀ : a₀ + D.α i = a)
  (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d)

include M hne in
/-- The chart inverse uses the inverse of the specified right mate;
there is no independently selected crossing. -/
theorem distinctCapSource_inv :
    letI := T.distinctCapSource_isIso M hne hi hj hij hji
    letI := M.invNe i j hne hj hji hi hij
    inv (T.distinctCapSource hi hj hij hji) =
      (associator (T.E i hi) (T.E j hij) (T.F i hji)).hom ≫
      T.E i hi ◁ inv (crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij)) ≫
      (associator (T.E i hi) (T.F i hi) (T.E j hj)).inv := by
  have := T.distinctCapSource_isIso M hne hi hj hij hji
  have := M.invNe i j hne hj hji hi hij
  let r := (associator (T.E i hi) (T.E j hij) (T.F i hji)).hom ≫
    T.E i hi ◁ inv (crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij)) ≫
    (associator (T.E i hi) (T.F i hi) (T.E j hj)).inv
  have hr : T.distinctCapSource hi hj hij hji ≫ r = 𝟙 _ := by
    dsimp [distinctCapSource, r]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← reassoc_of% (TwoSupercategory.whiskerLeft_comp (R := k) (T.E i hi)
      (crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij))
      (inv (crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij)))),
      IsIso.hom_inv_id, TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp,
      Iso.hom_inv_id]
  change inv (T.distinctCapSource hi hj hij hji) = r
  calc
    _ = inv (T.distinctCapSource hi hj hij hji) ≫ (T.distinctCapSource hi hj hij hji ≫ r) := by
      rw [hr, Category.comp_id]
    _ = r := by rw [IsIso.inv_hom_id_assoc]

/-- The right cap word is exactly a whiskered inverse mate followed by
its lower raw cap, with the two source bracketings explicit. -/
theorem distinctCapRight_eq_inverseMate :
    letI := M.invNe i j hne hj hji hi hij
    T.distinctCapRight M hne h₀ hi hj hij hji =
      (associator (T.E i hi) (T.E j hij) (T.F i hji)).hom ≫
      T.E i hi ◁ inv (crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij)) ≫
      (associator (T.E i hi) (T.F i hi) (T.E j hj)).inv ≫
      (T.loc i h₀ hi).capL ▷ T.E j hj ≫ (leftUnitor (T.E j hj)).hom := by
  have := M.invNe i j hne hj hji hi hij
  rw [distinctCapRight, T.distinctCapSource_inv M hne hi hj hij hji]
  simp only [Category.assoc]

end RouquierFamily
end OddMath.SKM
