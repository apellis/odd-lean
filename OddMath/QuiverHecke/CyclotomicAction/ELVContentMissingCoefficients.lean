import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitModules
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitInverseRows
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitInverseNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierFields
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionVacuumCoefficients

/-! # The prescribed old-content dotted-unit missing-colour boundary

Brundan–Ellis (1.13): the constructed old missing-colour module inverse
supplies the existing finite boundary-coefficient record at any content missing the moving colour,
with the ordinary unit, the chosen dot and full old coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
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

/-- Each boundary coefficient retains the original inverse-defined module row. -/
theorem contentMissingBoundary_coefficient_total (n : ℕ) (hn : n < count)
    (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k)) :
    ((contentMissingBoundaryCoefficients D Sc cutoff γ i hi).coeff n).total N =
      contentMissingUnitRow D Sc cutoff γ i hi N ⟨n, hn⟩ :=
  inductionVacuumCoefficient_total K hDot count
    (contentMissingUnitModuleIso D Sc cutoff γ i hi)
    (contentMissingUnitModuleIso_hom D Sc cutoff γ i hi) n hn N

/-- This is the raw top inverse row. The normalized left-adjunction
counit has its separate prescribed scalar factor. -/
theorem contentMissingBoundary_cap_total (hc : 0 < count)
    (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k)) :
    ((contentMissingBoundaryCoefficients D Sc cutoff γ i hi).cap).total N =
      contentMissingUnitRow D Sc cutoff γ i hi N ⟨count - 1, by omega⟩ := by
  rw [SKM.RouquierBoundary.Coefficients.cap, ite_eq_left hc]
  exact contentMissingBoundary_coefficient_total D Sc cutoff γ i hi (count - 1) (by omega) N

end OddMath.QuiverHecke.ELVOld
