import OddMath.QuiverHecke.PairingExtensionAction
import OddMath.QuiverHecke.PairingExtensionAffine
import OddMath.SKM.PairingExtensionBubbles
import OddMath.SKM.BubbleCoefficientBasis

/-! # Observation equations after pullback from the pairing extension

`SwappedVacuumCoordinates.md` §7 requires upward labelling, source-placed
normalized coefficients, and the coefficient filtration to retain their
original indices. These equations specialize the presentation comparisons
to the pulled-back action. They do not assume or construct a vacuum/corner
evaluation or a nondegeneracy statement.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
local notation "Dₑ" => ReservoirWeights.pairingExtension D
local notation "Scₑ" => ReservoirWeights.pairingExtensionScalars D Sc

namespace PairingExtension

end PairingExtension
end OddMath.QuiverHecke
