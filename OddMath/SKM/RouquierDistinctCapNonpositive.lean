import OddMath.SKM.RouquierDistinctCapColumnReduction
import OddMath.SKM.RouquierDistinctCapColumns
import OddMath.SKM.RouquierDistinctCapPrincipal
import OddMath.SKM.RouquierDistinctConnectedCapBoundary

/-!
# The actual nonpositive-height distinct cap pitchfork

Brundan–Ellis, Lemma 7.1, the nonpositive range. Both principal and every
finite-column test are proved from the actual multicolour relations and
inverse-defined local cap, then the augmented inverse detects equality.
No cap compatibility premise is introduced.
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

/-- The exact raw cap pitchfork at every nonpositive central height. -/
theorem distinctCap_of_nonpos (hh : D.h i a ≤ 0) :
    T.distinctCapLeft hi hj hij hji hprev =
      (Sc.t i j : k) • T.distinctCapRight M hne h₀ hi hj hij hji := by
  have hside : a₀ + D.α j = c₀ := by
    have hs : (a₀ + D.α j) + D.α i = c₀ + D.α i := by
      calc
        _ = (a₀ + D.α i) + D.α j := by abel
        _ = a + D.α j := by rw [h₀]
        _ = c := hj
        _ = c₀ + D.α i := hprev.symm
    exact add_right_cancel hs
  apply T.distinctCap_hom_ext_of_nonpos M hne h₀ hi hj hij hji hh
  · simp only [Linear.comp_smul]
    rw [T.distinctCapLeft_principal_word h₀ hi hj hij hji hprev]
    by_cases hneg : D.h i a < 0
    · rw [T.distinctMixedBraidLeft_cap_of_neg M hne h₀ hside hj hi hprev hji hij hneg,
        T.distinctCapRight_principal_of_neg M hne h₀ hi hj hij hji hneg, smul_zero]
    · have heq : D.h i a = 0 := by omega
      rw [T.distinctMixedBraidLeft_cap_of_zero M hne h₀ hside hj hi hprev hji hij heq,
        T.distinctCapRight_principal_of_zero M hne h₀ hj hi hji hij heq]
  · intro n hn
    have hneg : D.h i a < 0 := by omega
    apply (cancel_epi (leftUnitor (T.E j hj)).inv).mp
    simp only [Linear.comp_smul]
    rw [T.distinctCapLeft_column_reduce M hne h₀ hi hj hij hji hprev n,
      T.distinctCapQuadraticColumn_of_neg M hne hi hj hij hji hprev hneg n hn,
      T.distinctCapRight_column_of_neg M hne h₀ hi hj hij hji hneg n hn]
    split_ifs <;> simp only [Iso.inv_hom_id, Limits.comp_zero]

end RouquierFamily
end OddMath.SKM
