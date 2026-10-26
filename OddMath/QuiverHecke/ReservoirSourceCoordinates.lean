/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ReservoirRegular
import OddMath.QuiverHecke.HomDimension

/-! # Source-order normalization of regular vacuum coordinates

Ports the normalization step of
`Categorification/KLR/Unfurling/GenericVacuumWordCoordinates.lean` and
`Categorification/KLR/Unfurling/Triangular.lean`. In the super coefficient
category, applying a source coefficient and then an affine morphism introduces
the Koszul sign. This involutive diagonal change preserves the bounded PBW
window. Its extraction from the regular quotient is only asserted on that
window; no automorphism of the cyclotomic quotient is claimed.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The sign for putting the coefficient below the affine diagram. -/
def reservoirSourceOrder (t t' : List I) :
    (coefficientObj D Sc t ⟶ coefficientObj D Sc t') →ₗ[k]
      (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  (extensionBasis D Sc t t').constr k (fun j =>
    sign k ((j.1.2.card : ZMod 2) * j.2.par D) • extensionBasis D Sc t t' j)

@[simp] theorem reservoirSourceOrder_basis (t t' : List I)
    (j : SKM.SYM.CoefficientIndex D × NFIdx t t') :
    reservoirSourceOrder D Sc t t' (extensionBasis D Sc t t' j) =
      sign k ((j.1.2.card : ZMod 2) * j.2.par D) • extensionBasis D Sc t t' j := by
  simp [reservoirSourceOrder]

/-- Source-order normalization is an involution before quotienting. -/
theorem reservoirSourceOrder_involutive (t t' : List I) :
    Function.Involutive (reservoirSourceOrder D Sc t t') := by
  have h : (reservoirSourceOrder D Sc t t').comp (reservoirSourceOrder D Sc t t') =
      LinearMap.id := by
    apply (extensionBasis D Sc t t').ext
    intro j
    simp
  intro f
  exact LinearMap.congr_fun h f

/-- The normalization preserves the joint coefficient/dot filtration. -/
theorem reservoirSourceOrder_mem {t t' : List I} {d : ℕ}
    {f : coefficientObj D Sc t ⟶ coefficientObj D Sc t'}
    (hf : f ∈ ExtendedAtMost D Sc t t' d) :
    reservoirSourceOrder D Sc t t' f ∈ ExtendedAtMost D Sc t t' d := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, hj, rfl⟩ := hf
    rw [reservoirSourceOrder_basis]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  | zero => simp
  | add f g _ _ hf hg => simpa using Submodule.add_mem _ hf hg
  | smul r f _ hf => simpa using Submodule.smul_mem _ r hf

/-- In the zero window there is no exterior coefficient to cross. -/
theorem reservoirSourceOrder_zero_window {t t' : List I}
    {f : coefficientObj D Sc t ⟶ coefficientObj D Sc t'}
    (hf : f ∈ ExtendedAtMost D Sc t t' 0) :
    reservoirSourceOrder D Sc t t' f = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, hj, rfl⟩ := hf
    have hc : j.1.2.card = 0 := by
      change SKM.SYM.coefficientWeight D j.1 + j.2.1.1.length ≤ 0 at hj
      unfold SKM.SYM.coefficientWeight at hj
      omega
    simp only [reservoirSourceOrder_basis, hc, Nat.cast_zero, zero_mul, sign_zero, one_smul]
  | zero => simp
  | add f g _ _ hf hg => simp only [map_add, hf, hg]
  | smul r f _ hf => simp only [map_smul, hf]

private def sourceProductBilinear (t t' : List I) :
    SKM.SYM D k →ₗ[k]
      (((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) →ₗ[k]
        (coefficientObj D Sc t ⟶ coefficientObj D Sc t')) where
  toFun a :=
    { toFun := fun f => sourceCoefficientHom D Sc a (𝟙 _) ≫ sourceCoefficientHom D Sc 1 f
      map_add' := by intros; simp only [sourceCoefficientHom_add_right, Preadditive.comp_add]
      map_smul' := by
        intros
        simp only [sourceCoefficientHom_smul_right, Linear.comp_smul, RingHom.id_apply] }
  map_add' := by
    intro a b
    ext f
    have he : sourceCoefficientHom D Sc (a + b) (𝟙 ((pres D Sc).obj (ob D t))) =
        sourceCoefficientHom D Sc a (𝟙 _) + sourceCoefficientHom D Sc b (𝟙 _) := by
      change SKM.SYM.polynomialExteriorEquiv D k (a + b) ⊗ₜ[k] _ =
        SKM.SYM.polynomialExteriorEquiv D k a ⊗ₜ[k] _ +
          SKM.SYM.polynomialExteriorEquiv D k b ⊗ₜ[k] _
      rw [map_add, TensorProduct.add_tmul]
    change sourceCoefficientHom D Sc (a + b) (𝟙 ((pres D Sc).obj (ob D t))) ≫
      sourceCoefficientHom D Sc 1 f =
      sourceCoefficientHom D Sc a (𝟙 _) ≫ sourceCoefficientHom D Sc 1 f +
        sourceCoefficientHom D Sc b (𝟙 _) ≫ sourceCoefficientHom D Sc 1 f
    rw [he, Preadditive.add_comp]
  map_smul' := by
    intro c a
    ext f
    change sourceCoefficientHom D Sc (c • a) (𝟙 ((pres D Sc).obj (ob D t))) ≫
      sourceCoefficientHom D Sc 1 f =
      c • (sourceCoefficientHom D Sc a (𝟙 _) ≫ sourceCoefficientHom D Sc 1 f)
    rw [sourceCoefficientHom_smul, Linear.smul_comp]

/-- Ordered source application equals the explicit Koszul normalization. -/
theorem reservoirSourceOrder_source {t t' : List I} (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    reservoirSourceOrder D Sc t t' (sourceCoefficientHom D Sc a f) =
      sourceCoefficientHom D Sc a (𝟙 _) ≫ sourceCoefficientHom D Sc 1 f := by
  let P := (TensorProduct.lift (sourceProductBilinear D Sc t t')).comp
    (sourceTensorEquiv D Sc t t').symm.toLinearMap
  have h : reservoirSourceOrder D Sc t t' = P := by
    apply (extensionBasis D Sc t t').ext
    rintro ⟨a, j⟩
    rw [reservoirSourceOrder_basis, extensionBasis_apply]
    change _ = (TensorProduct.lift (sourceProductBilinear D Sc t t'))
      ((sourceTensorEquiv D Sc t t').symm (sourceCoefficientHom D Sc _ _))
    rw [← sourceTensorEquiv_tmul, LinearEquiv.symm_apply_apply]
    change _ = sourceCoefficientHom D Sc _ (𝟙 _) ≫ sourceCoefficientHom D Sc 1 _
    rw [sourceCoefficientHom_comp D Sc (coefficientBasis_mem_parity D a) _ _
      (show j.nf (D := D) (Sc := Sc) ∈ parity (R := k) _ _ (j.par D) from
        j.nf_mem_parity D Sc), one_mul, Category.id_comp, koszulSign_smul (R := k)]
    rfl
  rw [h]
  change (TensorProduct.lift (sourceProductBilinear D Sc t t'))
    ((sourceTensorEquiv D Sc t t').symm (sourceCoefficientHom D Sc a f)) = _
  rw [← sourceTensorEquiv_tmul, LinearEquiv.symm_apply_apply]
  rfl

section Field
variable {K : Type u} [Field K] (S : SKM.Scalars D K)

/-- The regular source action has normalized affine coordinates on every C0
window. The single recovery map works for all coefficients and all affine
morphisms in the window, including odd coefficients followed by odd crossings. -/
theorem exists_reservoir_source_coordinates (cutoff : I → ℕ) (t t' : List I)
    (d : ℕ) {N : ℕ} (hN : ∀ i, N ≤ cutoff i)
    (hb : d + 2 * t.length.choose 2 < N) :
    ∃ recover : ReservoirQuotient D S cutoff t t' →ₗ[K]
        ReservoirQuotient D S cutoff t t',
      ∀ (a : SKM.SYM D K)
        (f : (pres D S).obj (ob D t) ⟶ (pres D S).obj (ob D t')),
        sourceCoefficientHom D S a f ∈ ExtendedAtMost D S t t' d →
        recover (reservoirPostcomp D S cutoff (sourceCoefficientHom D S 1 f)
          (reservoirPostcomp D S cutoff (sourceCoefficientHom D S a (𝟙 _))
            (reservoirRegularGenerator D S cutoff t))) =
          (ELVRelationSpan D S cutoff t t').mkQ (sourceCoefficientHom D S a f) := by
  obtain ⟨recover, hrecover⟩ := exists_bounded_reservoir_extraction D S cutoff t t' d
    ((ELVRelationSpan D S cutoff t t').mkQ.comp (reservoirSourceOrder D S t t')) hN hb
  refine ⟨recover, ?_⟩
  intro a f hf
  rw [reservoirPostcomp_generator, reservoirPostcomp_mk,
    ← reservoirSourceOrder_source]
  rw [hrecover _ (reservoirSourceOrder_mem D S hf)]
  change (ELVRelationSpan D S cutoff t t').mkQ
    (reservoirSourceOrder D S t t' (reservoirSourceOrder D S t t'
      (sourceCoefficientHom D S a f))) = _
  rw [reservoirSourceOrder_involutive]

end Field
end OddMath.QuiverHecke
