import OddMath.SKM.RouquierDistinctCapMiddle
import OddMath.SKM.RouquierDistinctCapColumnReduction
import OddMath.SKM.RouquierDistinctCapTests

/-!
# The exact raw cap identity in the intermediate window

The computed correction sum is converted to the actual cap word using
`sigL ≫ sig = -1` at positive height, then the prescribed distinct
source chart is cancelled. This is Lemma 7.1 (7.3) in raw factor maps.
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

/-- The exact intermediate cap identity, retaining its raw height sign. -/
theorem distinctCap_of_middle (hpos : 0 < D.h i a) (hbound : D.h i a < D.d i j) :
    T.distinctCapLeft hi hj hij hji hprev =
      (zsign k (D.parity i * (D.h i a).toNat) * (Sc.t i j : k)) •
        T.distinctCapRight M hne h₀ hi hj hij hji := by
  have hside : a₀ + D.α j = c₀ := by
    have hs : (a₀ + D.α j) + D.α i = c₀ + D.α i := by
      calc
        _ = (a₀ + D.α i) + D.α j := by abel
        _ = a + D.α j := by rw [h₀]
        _ = c := hj
        _ = c₀ + D.α i := hprev.symm
    exact add_right_cancel hs
  have hb := T.distinctMixedBraidLeft_cap_middle M hne h₀ hside hj hi hprev hji hij hpos hbound
  rw [← T.distinctCapLeft_principal_word h₀ hi hj hij hji hprev] at hb
  rw [← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
    (T.loc i h₀ hi).sigL_sig_of_nonneg hpos.le] at hb
  simp only [TwoSupercategory.neg_whiskerRight (R := k),
    TwoSupercategory.id_whiskerRight (R := k), Preadditive.neg_comp,
    Category.id_comp, neg_neg] at hb
  have := T.distinctCapSource_isIso M hne hi hj hij hji
  apply (cancel_epi (T.distinctCapSource hi hj hij hji)).mp
  rw [Linear.comp_smul, T.distinctCapSource_right M hne h₀ hi hj hij hji]
  exact hb

end RouquierFamily
end OddMath.SKM
