import OddMath.SKM.RouquierDistinctCupRowTests

/-! # The distinct cup pitchfork in the strict positive range

Brundan–Ellis Lemma 7.1, (7.2), in the strict range needed above the
cap-pitchfork range. Principal tests follow from the corrected mixed
braid; finite cap rows follow from the quadratic relation. The positive
augmented inverse detects the literal raw cup identity.
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
  {a b c d e f : X}
  (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d)
  (hupper : b + D.α i = e) (hnext : d + D.α i = f) (hej : e + D.α j = f)

include hej in
/-- The two prescribed raw cup words satisfy the strict positive branch
of the distinct cup pitchfork, with the leading quadratic parameter. -/
theorem distinctCupLeft_eq_of_gt (hh : D.d i j < D.h i b) :
    T.distinctCupLeft hi hj hij hji hupper =
      (Sc.t i j : k) • T.distinctCupRight M hne hi hj hij hji hnext := by
  have hd : D.h i d = D.h i b - D.d i j := by
    rw [← hij, Datum.h, map_add]
    change D.h i b + D.h i (D.α j) = _
    rw [Datum.d]
    ring
  have hdpos : 0 < D.h i d := by omega
  apply T.distinctCup_hom_ext_of_nonneg M hne hi hj hij hji hnext hdpos.le
  · simp only [Linear.smul_comp]
    rw [T.distinctCupLeft_principal_of_gt M hne hi hj hij hji hupper hnext hej hh,
      T.distinctCupRight_principal_of_pos M hne hi hj hij hji hnext hdpos, smul_zero]
  · intro n hn
    apply (cancel_mono (rightUnitor (T.E j hij)).hom).mp
    simp only [Linear.smul_comp, Category.assoc]
    rw [T.distinctCupLeft_row_of_gt M hne hi hj hij hji hupper hnext hh n hn,
      T.distinctCupRight_row_of_pos M hne hi hj hij hji hnext hdpos n hn]

end RouquierFamily
end OddMath.SKM
