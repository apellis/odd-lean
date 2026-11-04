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

theorem UpwardModuleAction.restrictPairingExtension_upAct (μ : X)
    (A : UpwardModuleAction.{u,w} Dₑ Scₑ (μ, 0)) {s t : List I}
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    (A.restrictPairingExtension D Sc μ).act s t ((alpha D Sc μ).map f) =
      A.act s t ((alpha Dₑ Scₑ (μ, 0)).map ((PairingExtension.presentationFunctor D Sc).map f)) := by
  rw [UpwardModuleAction.restrictPairingExtension_act, PairingExtension.alpha_map]

theorem UpwardModuleAction.restrictPairingExtension_bubbles (cs : SKM.CScalars Sc) (μ : X)
    (A : UpwardModuleAction.{u,w} Dₑ Scₑ (μ, 0)) (s : List I) (a : SKM.SYM D k) :
    (A.restrictPairingExtension D Sc μ).bubbles cs s a =
      A.bubbles (ReservoirWeights.pairingExtensionCScalars D cs) s
        (SKM.PairingExtension.coefficientEquiv D a) := by
  rw [UpwardModuleAction.bubbles_apply, UpwardModuleAction.restrictPairingExtension_act,
    SKM.PairingExtension.homMap_bubAt_betaSYM, UpwardModuleAction.bubbles_apply]

namespace PairingExtension

/-- The full coefficient basis, including every ordered exterior component, is retained. -/
theorem coefficientEquiv_basis (a : SKM.SYM.CoefficientIndex D) :
    SKM.PairingExtension.coefficientEquiv D (SKM.SYM.coefficientBasis D k a) =
      SKM.SYM.coefficientBasis Dₑ k a := by
  apply (SKM.SYM.polynomialExteriorEquiv Dₑ k).injective
  change (SKM.SYM.polynomialExteriorEquiv Dₑ k)
    ((SKM.SYM.polynomialExteriorEquiv Dₑ k).symm
      ((SKM.SYM.polynomialExteriorEquiv D k) (SKM.SYM.coefficientBasis D k a))) = _
  rw [AlgEquiv.apply_symm_apply, SKM.SYM.coefficientBasis_projection,
    SKM.SYM.coefficientBasis_projection]
  rfl

/-- The coefficient part of the bounded observation window is unchanged. -/
theorem coefficientEquiv_mem_atMost {n : ℕ} {a : SKM.SYM D k}
    (ha : a ∈ SKM.SYM.CoefficientAtMost D k n) :
    SKM.PairingExtension.coefficientEquiv D a ∈ SKM.SYM.CoefficientAtMost Dₑ k n := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, hb, rfl⟩ := ha
    rw [coefficientEquiv_basis]
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- The lower coefficient filtration used to bound the observation kernel is unchanged. -/
theorem coefficientEquiv_mem_atLeast {n : ℕ} {a : SKM.SYM D k}
    (ha : a ∈ SKM.SYM.CoefficientAtLeast D k n) :
    SKM.PairingExtension.coefficientEquiv D a ∈ SKM.SYM.CoefficientAtLeast Dₑ k n := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, hb, rfl⟩ := ha
    rw [coefficientEquiv_basis]
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

end PairingExtension
end OddMath.QuiverHecke
