import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitRows
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitInverseNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierFields

/-! # Input supernaturality of the prescribed old missing-colour inverse rows

Brundan–Ellis (1.13): the constructed old module inverses and their given
even forward columns yield natural inverse rows on every input map,
including odd and inhomogeneous module morphisms.
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

/-- The constructed inverse row is supernatural, with its original r-th
source-unshift degree and no independently supplied inverse-naturality law. -/
theorem contentMissingUnitRow_supernatural (r : Fin count) :
    IsSupernatural k (r.val • D.parity i) (F := induction K ⋙ restriction K)
      (G := 𝟭 (Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k)))
      (fun N => contentMissingUnitRow D Sc cutoff γ i hi N r) :=
  unitColumnModuleInverseRow_supernatural K hDot count
    (contentMissingUnitModuleIso D Sc cutoff γ i hi)
    (contentMissingUnitModuleIso_hom D Sc cutoff γ i hi) r

/-- The specified inverse row as a cell in the native module parity target. -/
def contentMissingUnitRowTransformation (r : Fin count) :
    inductionModuleCell (k := k) K ≫ restrictionModuleCell (k := k) K ⟶
      𝟙 (inductionModulePiCategory (k := k) (OldContentCategory D Sc cutoff γ)) :=
  unitColumnModuleInverseTransformation K hDot count
    (contentMissingUnitModuleIso D Sc cutoff γ i hi)
    (contentMissingUnitModuleIso_hom D Sc cutoff γ i hi) r

/-- Evaluation retains the original inverse-defined module row. -/
theorem contentMissingUnitRowTransformation_total (r : Fin count)
    (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k)) :
    (contentMissingUnitRowTransformation D Sc cutoff γ i hi r).total N =
      contentMissingUnitRow D Sc cutoff γ i hi N r :=
  unitColumnModuleInverseTransformation_total K hDot count
    (contentMissingUnitModuleIso D Sc cutoff γ i hi)
    (contentMissingUnitModuleIso_hom D Sc cutoff γ i hi) r N

end OddMath.QuiverHecke.ELVOld
