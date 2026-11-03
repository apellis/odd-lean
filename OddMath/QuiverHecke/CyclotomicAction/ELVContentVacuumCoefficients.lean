import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionVacuumCoefficients

/-! # The prescribed old-content dotted-unit vacuum boundary

Brundan–Ellis (1.13): the constructed old missing-colour module inverse
supplies the existing finite boundary-coefficient record at empty content,
with the ordinary unit, the chosen dot and full old coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (i : I)
local notation "K" => oldContentAppend D Sc cutoff [] i
local notation "hDot" => oldContentAppendDot_supernatural D Sc cutoff [] i
local notation "count" => contentUnitCount D cutoff i (([] : List I) : Multiset I)

/-- The existing finite boundary record, constructed from the prescribed
old matrix inverse rather than supplied as an action-family hypothesis. -/
def contentVacuumBoundaryCoefficients :
    SKM.RouquierBoundary.Coefficients (inductionModuleAdjunction (k := k) K)
      (inductionModuleDot K hDot) (D.parity i) count :=
  inductionVacuumCoefficients K hDot count
    (contentMissingUnitModuleIso D Sc cutoff [] i (by simp))
    (contentMissingUnitModuleIso_hom D Sc cutoff [] i (by simp))

/-- Each boundary coefficient retains the original inverse-defined module row. -/
theorem contentVacuumBoundary_coefficient_total (n : ℕ) (hn : n < count)
    (N : Superfunctor k (OldContentCategory D Sc cutoff []) (SVec k)) :
    ((contentVacuumBoundaryCoefficients D Sc cutoff i).coeff n).total N =
      contentMissingUnitRow D Sc cutoff [] i (by simp) N ⟨n, hn⟩ :=
  inductionVacuumCoefficient_total K hDot count
    (contentMissingUnitModuleIso D Sc cutoff [] i (by simp))
    (contentMissingUnitModuleIso_hom D Sc cutoff [] i (by simp)) n hn N

/-- This is the raw top inverse row. The normalized left-adjunction
counit has its separate prescribed scalar factor. -/
theorem contentVacuumBoundary_cap_total (hc : 0 < count)
    (N : Superfunctor k (OldContentCategory D Sc cutoff []) (SVec k)) :
    ((contentVacuumBoundaryCoefficients D Sc cutoff i).cap).total N =
      contentMissingUnitRow D Sc cutoff [] i (by simp) N ⟨count - 1, by omega⟩ := by
  rw [SKM.RouquierBoundary.Coefficients.cap, ite_eq_left hc]
  exact contentVacuumBoundary_coefficient_total D Sc cutoff i (count - 1) (by omega) N

end OddMath.QuiverHecke.ELVOld
