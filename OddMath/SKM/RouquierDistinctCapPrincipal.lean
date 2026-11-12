import OddMath.SKM.RouquierDistinctCapTests
import OddMath.SKM.RouquierDistinctCapMonomials

/-!
# The negative-height principal distinct cap test

Brundan–Ellis, Lemma 7.1, the strictly negative case of the first test
in `pf_a`: every mixed-braid correction monomial is below the shifted
cap boundary, while the second mixed word vanishes by the local inverse
relation. The first mixed word therefore also has zero cap composite.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) {Sc : Scalars D k}
  (M : RouquierMulticolour T Sc) {i j : I} (hne : i ≠ j)
  {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)

include hne in
/-- Every monomial whose right-dot exponent is below `d_ij` lies
strictly below the shifted cap boundary at negative central height. -/
theorem distinctMixedBraidOuterMate_monomial_cap_zero (hh : D.h i b < 0)
    (s q n : ℕ) (hn : n < D.dn i j) :
    T.distinctMixedBraidOuterMate i j hab hbc hcd
      (rouquierPower (T.dot i hab) s ▷ (T.E j hbc ≫ T.E i hcd) ≫
        T.E i hab ◁ (rouquierPower (T.dot j hbc) q ▷ T.E i hcd) ≫
        T.E i hab ◁ T.E j hbc ◁ rouquierPower (T.dot i hcd) n) ≫
      T.E j hbc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor (T.E j hbc)).hom = 0 := by
  have hw : D.h i c = D.h i b - D.d i j := by
    rw [← hbc]
    simp [Datum.d, map_add]
  have hd := D.dn_cast hne
  have hc : D.h i c < 0 := by omega
  have hn' : n < (-D.h i c).toNat := by omega
  have hn'' : n ≠ (-D.h i c - 1).toNat := by omega
  rw [T.distinctMixedBraidOuterMate_monomial_cap i j hab hbc hcd hfc hc s q n hn',
    ite_eq_right hn'']

include M hne haf in
/-- The first mixed word's principal cap test vanishes at every
strictly negative central height, for the actual multicolour relation. -/
theorem distinctMixedBraidLeft_cap_of_neg (hh : D.h i b < 0) :
    T.distinctMixedBraidLeft i j hab hbc hbe hcd hed ≫
      T.E j hbc ◁ (T.loc i hfc hcd).capL ≫ (rightUnitor (T.E j hbc)).hom = 0 := by
  have hw : D.h i c = D.h i b - D.d i j := by
    rw [← hbc]
    simp [Datum.d, map_add]
  have hd := D.d_nonneg hne
  have hc : D.h i c < 0 := by omega
  have he := congrArg (fun z => z ≫ T.E j hbc ◁ (T.loc i hfc hcd).capL ≫
    (rightUnitor (T.E j hbc)).hom)
    (T.distinctMixedBraid_correction i j hab haf hbc hbe hfc hcd hed M hne)
  simp only [Preadditive.sub_comp,
    T.distinctMixedBraidRight_cap_of_neg hab haf hbc hfc hcd hc, sub_zero] at he
  rw [he]
  simp only [Preadditive.add_comp, Preadditive.sum_comp, Linear.smul_comp]
  refine (congrArg₂ (fun x y => x + y) ?_ ?_).trans (zero_add (0 : _))
  · apply Finset.sum_eq_zero
    intro s hs
    have hs' := Finset.mem_range.mp hs
    have hz := T.distinctMixedBraidOuterMate_monomial_cap_zero hne hab hbc hfc hcd hh
      s 0 (D.dn i j - 1 - s) (by omega)
    simp only [rouquierPower_zero, TwoSupercategory.id_whiskerRight (R := k),
      TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp] at hz
    rw [hz, smul_zero]
  · apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q _
    apply Finset.sum_eq_zero
    intro s hs
    have hp' := Finset.mem_range.mp hp
    have hs' := Finset.mem_range.mp hs
    rw [T.distinctMixedBraidOuterMate_monomial_cap_zero hne hab hbc hfc hcd hh
      s q (p - 1 - s) (by omega), smul_zero]

end RouquierFamily
end OddMath.SKM
