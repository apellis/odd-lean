import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMulticolourBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierBraidEquation

/-! # The general multicolour braid field of the chosen weight data

Brundan--Ellis (1.9), outside the repeated-outer correction case. The
field retains every prescribed crossing and associator on all weights.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a bl bj bi clj cli cji d : X}
  (hal : a + D.α l = bl) (haj : a + D.α j = bj) (hai : a + D.α i = bi)
  (hlj : bl + D.α j = clj) (hli : bl + D.α i = cli) (hjl : bj + D.α l = clj)
  (hji : bj + D.α i = cji) (hil : bi + D.α l = cli) (hij : bi + D.α j = cji)
  (hd₁ : clj + D.α i = d) (hd₂ : cli + D.α j = d) (hd₃ : cji + D.α l = d)

/-- Exactly the uncorrected RouquierMulticolour braid field for the
independently selected weight data, with only the source colour condition. -/
theorem elvRouquierData_multicolour_braid (hb : ¬ (i = l ∧ i ≠ j)) :
    rouquierMulticolourBraidEquation D (elvRouquierData D Sc cutoff bound Λ)
      i j l hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ := by
  apply rouquierMulticolourBraidEquation_of_paths
  have h := elvActionCross_multicolour_braid D Sc cutoff bound i j l Λ
    hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ hb
  simp only [elvRouquierData, elvWeightPrefixCross, elvWeightSuffixCross] at h ⊢
  convert h using 1

end OddMath.QuiverHecke.ELVOld
