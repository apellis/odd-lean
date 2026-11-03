import OddMath.QuiverHecke.CyclotomicAction.ELVContentVacuumCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleZeroLocalInverse

/-! # Constructed old-content local data at the vacuum

Brundan–Ellis (1.14) at negative vacuum height: the prescribed old matrix
inverse supplies the finite boundary coefficients, and the canonical zero
lower cell supplies its slides and lower adjunction. No local-inverse or
complete-family hypothesis is imposed on this construction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (i : I)
local notation "C₀" => OldContentCategory D Sc cutoff []
local notation "C₁" => OldContentCategory D Sc cutoff [i]
local notation "K" => oldContentAppend D Sc cutoff [] i
local notation "hDot" => oldContentAppendDot_supernatural D Sc cutoff [] i
local notation "Z" => zeroModuleCell (k := k) C₀
local notation "count" => contentUnitCount D cutoff i (([] : List I) : Multiset I)

/-- The actual negative vacuum local record uses the original ordinary
append adjunction and dot, with inverse entries constructed from the given
old matrix and a zero lower cell in the same module category. -/
def contentVacuumLoc (hi : 0 < cutoff i) :
    SKM.SuperRouquierLoc (zeroModuleCellAdjunction (k := k) C₀)
      (inductionModuleAdjunction (k := k) K) (0 : End Z) (inductionModuleDot K hDot)
      (0 : End (Z ≫ inductionModuleCell (k := k) K)) (D.parity i) (-((cutoff i : ℕ) : ℤ)) := by
  have hc : count = cutoff i := by simp [contentUnitCount, contentCrossingHeight]
  have L := moduleZeroBoundaryLoc C₀ (inductionModulePiCategory (k := k) C₁)
    (inductionModuleAdjunction (k := k) K) (inductionModuleDot K hDot) (D.parity i) count
    (contentVacuumBoundaryCoefficients D Sc cutoff i) (by simpa only [hc] using hi)
  simpa only [hc] using L

end OddMath.QuiverHecke.ELVOld
