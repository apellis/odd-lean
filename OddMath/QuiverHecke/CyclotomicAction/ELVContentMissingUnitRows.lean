import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitModules
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitInverseRows

/-! # Finite inverse rows on old missing-colour content modules

Brundan–Ellis (1.13): the constructed prescribed module unit inverse
supplies the finite coefficient rows and their window and decomposition.
These rows support the empty local Rouquier inverse over full coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
  (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
local notation "K" => oldContentAppend D Sc cutoff γ i
local notation "hDot" => oldContentAppendDot_supernatural D Sc cutoff γ i
local notation "count" => contentUnitCount D cutoff i (γ : Multiset I)

end OddMath.QuiverHecke.ELVOld
