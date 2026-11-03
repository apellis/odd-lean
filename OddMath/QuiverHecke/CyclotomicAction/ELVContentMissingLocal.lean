import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleZeroLocalInverse

/-! # Local inverse data when the moving colour is absent

Brundan–Ellis (1.13)–(1.14): the prescribed missing-colour unit matrix
constructs the local record at every absent-predecessor content. The
content may be nonempty. At height zero both inverse orientations are
retained, with no positivity assumption on the cutoff.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
local notation "C₀" => OldContentCategory D Sc cutoff γ
local notation "C₁" => OldContentCategory D Sc cutoff (i :: γ)
local notation "K" => oldContentAppend D Sc cutoff γ i
local notation "hDot" => oldContentAppendDot_supernatural D Sc cutoff γ i
local notation "Z" => zeroModuleCell (k := k) C₀
local notation "count" => contentUnitCount D cutoff i (γ : Multiset I)

/-- The untruncated prescribed upper append adjunction and dot give the
local record with a zero lower edge, including the zero-height case. -/
def contentMissingLoc :
    SKM.SuperRouquierLoc (zeroModuleCellAdjunction (k := k) C₀)
      (inductionModuleAdjunction (k := k) K) (0 : End Z) (inductionModuleDot K hDot)
      (0 : End (Z ≫ inductionModuleCell (k := k) K)) (D.parity i)
      (-contentCrossingHeight D cutoff i (γ : Multiset I)) := by
  have L := moduleZeroBoundaryLoc_nonpositive C₀ (inductionModulePiCategory (k := k) C₁)
    (inductionModuleAdjunction (k := k) K) (inductionModuleDot K hDot) (D.parity i) count
    (contentMissingBoundaryCoefficients D Sc cutoff γ i hi)
  simpa only [contentUnitCount_cast D cutoff i (γ : Multiset I)
    (contentCrossingHeight_nonneg_of_not_mem D cutoff γ i hi)] using L

end OddMath.QuiverHecke.ELVOld
