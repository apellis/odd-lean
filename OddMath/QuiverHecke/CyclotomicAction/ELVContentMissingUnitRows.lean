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

/-- The coefficient row of the constructed prescribed module inverse,
restored to its unshifted value module. -/
def contentMissingUnitRow (r : Fin count) :
    (restriction K).obj ((induction K).obj N) ⟶ N :=
  unitColumnModuleInverseRow K N count (contentMissingUnitModuleIso D Sc cutoff γ i hi N) r

/-- The original r-th source shift determines the row degree. -/
theorem contentMissingUnitRow_mem (r : Fin count) :
    contentMissingUnitRow D Sc cutoff γ i hi N r ∈ parity (R := k) _ _ (r.val • D.parity i) :=
  unitColumnModuleInverseRow_mem K hDot N count (contentMissingUnitModuleIso D Sc cutoff γ i hi N)
    (contentMissingUnitModuleIso_hom D Sc cutoff γ i hi N) r

/-- Every prescribed unit/dot column pairs with its own coefficient row,
and is killed by the other finite rows. -/
theorem contentMissingUnitColumn_row (a r : Fin count) :
    unitDotColumn K hDot N a.val ≫ contentMissingUnitRow D Sc cutoff γ i hi N r =
      if a = r then 𝟙 N else 0 :=
  unitDotColumn_inverseRow K hDot N count (contentMissingUnitModuleIso D Sc cutoff γ i hi N)
    (contentMissingUnitModuleIso_hom D Sc cutoff γ i hi N) a r

/-- The extracted inverse rows and given unit columns reconstruct native F/E. -/
theorem contentMissingUnitRow_total :
    (∑ r : Fin count, contentMissingUnitRow D Sc cutoff γ i hi N r ≫ unitDotColumn K hDot N r.val) =
      𝟙 ((restriction K).obj ((induction K).obj N)) :=
  sum_unitColumnModuleInverseRow_unitDotColumn K hDot N count (contentMissingUnitModuleIso D Sc cutoff γ i hi N)
    (contentMissingUnitModuleIso_hom D Sc cutoff γ i hi N)

end OddMath.QuiverHecke.ELVOld
