import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitColumnModules

/-! # The old missing-colour inverse as a module isomorphism

Brundan–Ellis (1.13): the prescribed component inverses assemble with the
ordinary shifted unit columns to an even module inverse, including the
empty old content category and its full coefficient algebra.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
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

/-- The constructed even inverse of the actual finite module unit matrix. -/
def contentMissingUnitModuleIso :
    OddMath.FiniteSupermodule.product (unitColumnModuleFamily (D.parity i) N count) ≅
      (restriction K).obj ((induction K).obj N) :=
  unitColumnModuleIso K hDot N count
    (contentMissingUnitMatrixIso D Sc cutoff γ i hi N)
    (contentMissingUnitMatrixIso_hom D Sc cutoff γ i hi N)

/-- The forward module field is exactly the prescribed ordinary shifted unit columns. -/
theorem contentMissingUnitModuleIso_hom :
    (contentMissingUnitModuleIso D Sc cutoff γ i hi N).hom = unitColumnModuleMap K hDot N count :=
  unitColumnModuleIso_hom K hDot N count _ _

end OddMath.QuiverHecke.ELVOld
