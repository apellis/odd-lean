import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentGridMatrixInverse

/-! # Constructed local inverse fields on old content modules

Brundan–Ellis (1.13)–(1.14): the given old content matrix inverses supply
the input-natural inverse entries of the actual ordinary-adjunction
Rouquier mate and dotted fields. No matrix compatibility, evenness or
inverse-naturality premise remains.
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

/-- The constructed prescribed unit inverse, on every old input module,
for the exact native Rouquier principal and unit/dot fields. -/
def oldContentRouquierInverseFrom
    (hh : 0 ≤ contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I)) :=
  inductionModuleInverseFromFamily J K hCross hDotK
    (contentUnitCount D cutoff i ((i :: ν : List I) : Multiset I))
    (fun N => oldContentGridUnitMatrixIso D Sc cutoff ν i N hh)
    (fun N => oldContentGridUnitMatrixIso_hom D Sc cutoff ν i N hh)

/-- The constructed prescribed cap inverse, for the same native Rouquier
principal field and the ordinary right-counit/dot rows. -/
def oldContentRouquierInverseTo
    (hh : contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I) ≤ 0) :=
  inductionModuleInverseToFamily J K hCross hDotJ
    (contentCapCount D cutoff i ((i :: ν : List I) : Multiset I))
    (fun N => oldContentGridCapMatrixIso D Sc cutoff ν i N hh)
    (fun N => oldContentGridCapMatrixIso_hom D Sc cutoff ν i N hh)

end OddMath.QuiverHecke.ELVOld
