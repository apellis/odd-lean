import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingStoredCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeZeroBoundary
import OddMath.SKM.RouquierZeroLocal

/-! # The missing-colour local record at a stored upper representative

Brundan–Ellis (1.13)–(1.14): the selected evaluated upper adjunction and
dot, with the constructed zero lower cell, have the prescribed local
inverse at every missing-colour content, including height zero.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ) (hi : i ∉ γ)
local notation "Z" => probeEvaluatedZeroCell D Sc m γ
local notation "A₀" => probeEvaluatedZeroAdjunction D Sc m γ
local notation "E" => probeAppendToE D Sc m γ i μ h
local notation "A₁" => probeAppendToRightAdjunction D Sc m γ i μ h
local notation "dot" => probeAppendToInductionDot D Sc m γ i μ h
local notation "count" => contentUnitCount D (probeCutoff D m) i (γ : Multiset I)

/-- The selected missing-colour local data retain both zero-height inverse
orientations, with no positive-cutoff or local-inverse premise. -/
def probeMissingStoredLoc :
    SKM.SuperRouquierLoc A₀ A₁ (0 : End Z) dot (0 : End (Z ≫ E)) (D.parity i)
      (-contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I)) := by
  have L := SKM.RouquierZeroLocal.ofCoefficients A₀ A₁ dot (D.parity i) count
    (probeMissingStoredCoefficients D Sc m γ i h hi)
    (probeEvaluatedZeroCell_comp_id D Sc m γ (probeEvaluatedTarget D Sc m γ) Z)
    (probeEvaluatedZeroCell_comp_id D Sc m γ (probeEvaluatedTarget D Sc m μ) E)
  simpa only [contentUnitCount_cast D (probeCutoff D m) i (γ : Multiset I)
    (contentCrossingHeight_nonneg_of_not_mem D (probeCutoff D m) γ i hi)] using L

end OddMath.QuiverHecke
