import OddMath.SKM.PairingExtensionPresentation
import OddMath.QuiverHecke.UpwardModuleAction
import OddMath.QuiverHecke.PairingExtensionAffine
import OddMath.SKM.PairingExtensionBubbles
import OddMath.SKM.BubbleCoefficientBasis
import OddMath.QuiverHecke.WeightedCoefficientSeparation

/-! # Pairing extension on affine and coefficient PBW coordinates

`SwappedVacuumCoordinates.md` §7 uses unchanged upward diagrams and source
coefficient indices under the pairing extension. The independently proved
quiver-Hecke basis theorem (KKT Corollary 3.15, BE §11) supplies the inverse
of the exact presentation map. Tensor transport then preserves the joint
coefficient/PBW degree. No SKM nondegeneracy or observation kernel is assumed.
-/
noncomputable section
namespace OddMath.QuiverHecke.PairingExtension
open CategoryTheory StringDiagrams
open scoped TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
local notation "Dₑ" => ReservoirWeights.pairingExtension D
local notation "Scₑ" => ReservoirWeights.pairingExtensionScalars D Sc

/-- The exact affine map fixes every normal-form index. -/
theorem presentationFunctor_nf {s t : List I} (i : NFIdx s t) :
    (presentationFunctor D Sc).map (i.nf (D := D) (Sc := Sc)) =
      i.nf (D := Dₑ) (Sc := Scₑ) := by
  unfold NFIdx.nf cl
  exact presentationFunctor_diag D Sc _

/-- Inverse of the presentation map, constructed from the independent affine basis. -/
def affineEquiv (s t : List I) :
    ((pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) ≃ₗ[k]
      ((pres Dₑ Scₑ).obj (ob Dₑ s) ⟶ (pres Dₑ Scₑ).obj (ob Dₑ t)) :=
  (basisNF D Sc s t).equiv (basisNF Dₑ Scₑ s t) (Equiv.refl _)

theorem affineEquiv_nf {s t : List I} (i : NFIdx s t) :
    affineEquiv D Sc s t (i.nf (D := D) (Sc := Sc)) =
      i.nf (D := Dₑ) (Sc := Scₑ) := by
  simpa only [affineEquiv, basisNF_apply, Equiv.refl_apply] using
    (basisNF D Sc s t).equiv_apply i (basisNF Dₑ Scₑ s t) (Equiv.refl _)

/-- The equivalence uses the previously constructed raw-diagram map exactly. -/
theorem affineEquiv_apply {s t : List I}
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    affineEquiv D Sc s t f = (presentationFunctor D Sc).map f := by
  have h : (affineEquiv D Sc s t).toLinearMap =
      (presentationFunctor D Sc).mapLinearMap k := by
    apply (basisNF D Sc s t).ext
    intro i
    change affineEquiv D Sc s t (basisNF D Sc s t i) =
      (presentationFunctor D Sc).map (basisNF D Sc s t i)
    rw [basisNF_apply, affineEquiv_nf, presentationFunctor_nf]
  exact LinearMap.congr_fun h f

/-- Tensor transport before identifying the coefficient-extended Hom spaces. -/
def sourceEquiv (s t : List I) :
    (SKM.SYM D k ⊗[k] ((pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t))) ≃ₗ[k]
      (SKM.SYM Dₑ k ⊗[k] ((pres Dₑ Scₑ).obj (ob Dₑ s) ⟶ (pres Dₑ Scₑ).obj (ob Dₑ t))) :=
  TensorProduct.congr (SKM.PairingExtension.coefficientEquiv (k := k) D).toLinearEquiv
    (affineEquiv D Sc s t)

/-- The tensor equivalence transports the full source coefficient algebra. -/
def coefficientHomEquiv (s t : List I) :
    (coefficientObj (k := k) D Sc s ⟶ coefficientObj (k := k) D Sc t) ≃ₗ[k]
      (coefficientObj (k := k) Dₑ Scₑ s ⟶ coefficientObj (k := k) Dₑ Scₑ t) :=
  TensorProduct.congr (LinearEquiv.refl k (SKM.SYM.PolynomialExterior D k))
    (affineEquiv D Sc s t)

theorem coefficientHomEquiv_source {s t : List I} (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    coefficientHomEquiv D Sc s t (sourceCoefficientHom (k := k) (t := s) (t' := t) D Sc a f) =
      sourceCoefficientHom (k := k) (t := s) (t' := t) Dₑ Scₑ (SKM.PairingExtension.coefficientEquiv (k := k) D a)
        ((presentationFunctor D Sc).map f) := by
  change (SKM.SYM.polynomialExteriorEquiv D k a) ⊗ₜ[k] (affineEquiv D Sc s t f) =
    (SKM.SYM.polynomialExteriorEquiv Dₑ k
      ((SKM.SYM.polynomialExteriorEquiv Dₑ k).symm
        (SKM.SYM.polynomialExteriorEquiv D k a))) ⊗ₜ[k] ((presentationFunctor D Sc).map f)
  rw [AlgEquiv.apply_symm_apply, affineEquiv_apply]

theorem coefficientHomEquiv_basis {s t : List I}
    (i : SKM.SYM.CoefficientIndex D × NFIdx s t) :
    coefficientHomEquiv D Sc s t (extensionBasis D Sc s t i) =
      extensionBasis Dₑ Scₑ s t i := by
  rcases i with ⟨a, i⟩
  rw [extensionBasis_apply, coefficientHomEquiv_source, coefficientEquiv_basis,
    presentationFunctor_nf, extensionBasis_apply]

theorem extensionDegree_eq {s t : List I}
    (i : SKM.SYM.CoefficientIndex D × NFIdx s t) :
    extensionDegree Dₑ i = extensionDegree D i := rfl

theorem coefficientHomEquiv_mem_atMost {s t : List I} {d : ℕ}
    {f : coefficientObj (k := k) D Sc s ⟶ coefficientObj (k := k) D Sc t}
    (hf : f ∈ ExtendedAtMost D Sc s t d) :
    coefficientHomEquiv D Sc s t f ∈ ExtendedAtMost Dₑ Scₑ s t d := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, hi, rfl⟩ := hf
    rw [coefficientHomEquiv_basis]
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

theorem coefficientHomEquiv_mem_atLeast {s t : List I} {d : ℤ}
    {f : coefficientObj (k := k) D Sc s ⟶ coefficientObj (k := k) D Sc t}
    (hf : f ∈ ExtendedAtLeast D Sc s t d) :
    coefficientHomEquiv D Sc s t f ∈ ExtendedAtLeast Dₑ Scₑ s t d := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, hi, rfl⟩ := hf
    rw [coefficientHomEquiv_basis]
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

end OddMath.QuiverHecke.PairingExtension
