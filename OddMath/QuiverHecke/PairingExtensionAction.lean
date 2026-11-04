import OddMath.SKM.PairingExtensionPresentation
import OddMath.QuiverHecke.UpwardModuleAction

/-! # Pullback of the combined action to original external weights

`SwappedNondegeneracy.md` §2 uses the pairing extension to choose the two
factor highest weights, then evaluates their combined action at `(μ,0)`.
This pulls back that action along the checked presentation functor, keeping
every module carrier unchanged. No restriction of the separate factors or
faithfulness of the presentation functor is used.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (μ : X)
local notation "Dₑ" => ReservoirWeights.pairingExtension D
local notation "Scₑ" => ReservoirWeights.pairingExtensionScalars D Sc

/-- Restrict the combined upward action, retaining its modules at every word. -/
def UpwardModuleAction.restrictPairingExtension
    (A : UpwardModuleAction.{u,w} Dₑ Scₑ (μ, 0)) : UpwardModuleAction D Sc μ where
  V := A.V
  act s t := (A.act s t).comp (SKM.PairingExtension.homMap D Sc μ (upWord s) (upWord t))
  act_id s := by
    simpa only [LinearMap.comp_apply, SKM.PairingExtension.homMap_id] using A.act_id s
  act_comp s t r f g := by
    change A.act s r (SKM.PairingExtension.homMap D Sc μ _ _ (f ≫ g)) = _
    rw [SKM.PairingExtension.homMap_comp]
    exact A.act_comp s t r _ _

@[simp] theorem UpwardModuleAction.restrictPairingExtension_V
    (A : UpwardModuleAction.{u,w} Dₑ Scₑ (μ, 0)) (s : List I) :
    (A.restrictPairingExtension D Sc μ).V s = A.V s := rfl

theorem UpwardModuleAction.restrictPairingExtension_act
    (A : UpwardModuleAction.{u,w} Dₑ Scₑ (μ, 0)) (s t : List I) (f : UpwardHom D Sc μ s t) :
    (A.restrictPairingExtension D Sc μ).act s t f =
      A.act s t (SKM.PairingExtension.homMap D Sc μ (upWord s) (upWord t) f) := rfl

end OddMath.QuiverHecke
