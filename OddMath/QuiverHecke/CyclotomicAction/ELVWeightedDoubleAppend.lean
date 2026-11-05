import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPairAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp

/-! # Iterated weighted append comparison

DeformedActionAssembly §5 and DeformedMatrixComparison (2), (4) use the
crossing on iterated induction. The comparison is obtained from the chosen
pair comparison by descending the old induction flattening and undoing the
truncated flattening. Thus its flattening coherence uses the prescribed maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

variable (i j : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "K" => CyclotomicCrossingTensor.append D Sc cutoff j
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "U" => truncatedAppend D Sc cutoff N [j]
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "FI" => Functor.obj (BalancedInduction.induction J ⋙ BalancedInduction.induction K) RM
local notation "FP" => BalancedInduction.induced (J ⋙ K) RM
local notation "hFP" => pairInduced_killsWeightedCoefficients D Sc cutoff N i j RM
  (weightedRestriction_kills D Sc cutoff N M)

/-- The twice-induced old module satisfies the complete weighted annihilator. -/
theorem doubleInduced_killsWeightedCoefficients :
    KillsWeightedCoefficients D Sc cutoff N FI :=
  induced_killsWeightedCoefficients D Sc cutoff N j _
    (induced_killsWeightedCoefficients D Sc cutoff N i RM
      (weightedRestriction_kills D Sc cutoff N M))
local notation "hFI" => doubleInduced_killsWeightedCoefficients D Sc cutoff N i j M

/-- The old canonical induction flattening descends componentwise. -/
def weightedInductionFlattening :
    weightedModule D Sc cutoff N FI hFI ≅ weightedModule D Sc cutoff N FP hFP :=
  weightedModuleIso D Sc cutoff N FI FP hFI hFP
    ((BalancedInduction.inductionComp J K).app RM)

private def pairFunctorIso : weightedModule D Sc cutoff N FP hFP ≅
    (BalancedInduction.induction (T ⋙ U)).obj M :=
  pairWeightedModuleIso D Sc cutoff N i j M

/-- The selected comparison on the two iterated inductions. -/
def doubleWeightedModuleIso :
    weightedModule D Sc cutoff N FI hFI ≅
      (BalancedInduction.induction T ⋙ BalancedInduction.induction U).obj M :=
  weightedInductionFlattening D Sc cutoff N i j M ≪≫
    pairFunctorIso D Sc cutoff N i j M ≪≫
      ((BalancedInduction.inductionComp T U).app M).symm

end OddMath.QuiverHecke.ELVOld
