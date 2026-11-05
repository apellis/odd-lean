import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridLocal
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridCrossSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentAffineRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVContentGridMatrixInverse

/-! # Local Rouquier records on old content modules

Brundan–Ellis (1.7)–(1.8), (1.13)–(1.14): the literal old quotient relations
and constructed prescribed matrix inverses supply the local record on
successive old-content induction edges. No local-record, inverse,
compatibility, or complete-family hypothesis remains.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J" => oldContentAppend D Sc cutoff ν i
local notation "K" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "hCross" => oldContentMatrixCross_supernatural D Sc cutoff ν i
local notation "hDotJ" => oldContentAppendDot_supernatural D Sc cutoff ν i
local notation "hDotK" => oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i

/-- The prescribed local data at minus the intermediate content height. -/
def oldContentLoc : SKM.SuperRouquierLoc (k := k)
    (inductionModuleAdjunction (k := k) J) (inductionModuleAdjunction (k := k) K)
    (inductionModuleDot J hDotJ) (inductionModuleDot K hDotK)
    (inductionModuleCross J K hCross) (D.parity i)
    (-contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I)) := by
  refine inductionModuleLoc J K hCross hDotJ hDotK
    (contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I)) ?_ ?_
    (fun hh N => oldContentGridUnitMatrixIso D Sc cutoff ν i N hh)
    (fun hh N => oldContentGridUnitMatrixIso_hom D Sc cutoff ν i N hh)
    (fun hh N => oldContentGridCapMatrixIso D Sc cutoff ν i N hh)
    (fun hh N => oldContentGridCapMatrixIso_hom D Sc cutoff ν i N hh)
  · intro s
    have h := oldContentEqualCross_slideLeft D Sc cutoff ν i s
    rw [koszulSign_smul (R := k)] at h
    convert! h using 1
  · intro s
    have h := oldContentEqualCross_slideRight D Sc cutoff ν i s
    rw [koszulSign_smul (R := k)] at h
    convert! h using 1

end OddMath.QuiverHecke.ELVOld
