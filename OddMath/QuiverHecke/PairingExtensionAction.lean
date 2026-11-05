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

end OddMath.QuiverHecke
