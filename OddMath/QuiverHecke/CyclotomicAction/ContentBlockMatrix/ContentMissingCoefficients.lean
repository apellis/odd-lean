import OddMath.QuiverHecke.CyclotomicAction.ContentHom.ContentMissingUnitModules
import OddMath.QuiverHecke.CyclotomicAction.InductionGridRouquier.InductionVacuumCoefficients

/-!
# Content block matrix

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The prescribed old-content dotted-unit missing-colour boundary

Brundan–Ellis (1.13): the constructed old missing-colour module inverse
supplies the existing finite boundary-coefficient record at any content missing the moving colour,
with the ordinary unit, the chosen dot and full old coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
local notation "K" => oldContentAppend D Sc cutoff γ i
local notation "hDot" => oldContentAppendDot_supernatural D Sc cutoff γ i
local notation "count" => contentUnitCount D cutoff i (γ : Multiset I)

/-- The existing finite boundary record, constructed from the prescribed
old matrix inverse rather than supplied as an action-family hypothesis. -/
def contentMissingBoundaryCoefficients :
    SKM.RouquierBoundary.Coefficients (inductionModuleAdjunction (k := k) K)
      (inductionModuleDot K hDot) (D.parity i) count :=
  inductionVacuumCoefficients K hDot count
    (contentMissingUnitModuleIso D Sc cutoff γ i hi)
    (contentMissingUnitModuleIso_hom D Sc cutoff γ i hi)

end OddMath.QuiverHecke.ELV
end

end
