import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierMixedBraidEquation

/-! # The dotted mixed braid field of the selected weight data

Brundan--Ellis (1.9), repeated outer colour. This is exactly the
RouquierMulticolour.braidEq field for the independently selected maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "Sc'" => parameterTwist D Sc
local notation "E₁" => elvE D Sc' cutoff bound i Λ hab
local notation "E₂" => elvE D Sc' cutoff bound j Λ hbc
local notation "E₃" => elvE D Sc' cutoff bound i Λ hcd

/-- The exact repeated-outer dotted braid field, with original Sc and
all prescribed crossings, associators and rouquierPower terms. -/
theorem elvRouquierData_braidEq (hij : i ≠ j) :
    rouquierMixedBraidEquation D Sc (elvRouquierData D Sc' cutoff bound Λ)
      i j hab haf hbc hbe hfc hcd hed := by
  apply rouquierMixedBraidEquation_of_polynomial
  have h := elvActionCross_mixedBraid D Sc cutoff bound i j Λ
    hab haf hbc hbe hfc hcd hed hij
  simp only [elvRouquierData, elvWeightPrefixCross, elvWeightSuffixCross] at h ⊢
  convert h using 1

end OddMath.QuiverHecke.ELVOld
