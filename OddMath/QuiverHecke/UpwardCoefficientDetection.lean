/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ELVCyclotomicSeparation
import OddMath.QuiverHecke.Alpha
import OddMath.SKM.BubbleAlgebra
import OddMath.SKM.SpanBubbleProd

/-! # The precise action interface for upward coefficient independence

The actual map uses source-placed `betaSYM` and the repository's upward
functor `alpha`. Finite quotient observations are only required to agree on
the explicit affine/coefficient basis; no faithfulness is assumed.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

abbrev UpwardHom (μ : X) (t t' : List I) :=
  (SKM.pres D Sc).obj (SKM.ob D μ (upWord t)) ⟶
    (SKM.pres D Sc).obj (SKM.ob D μ (upWord t'))

def upwardCoefficientBilinear (μ : X) (t t' : List I) :
    SKM.SYM D k →ₗ[k]
      (((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) →ₗ[k] UpwardHom D Sc μ t t') where
  toFun a :=
    { toFun := fun f => SKM.bubAt D Sc μ (upWord t) (SKM.betaSYM cs μ a) ≫ (alpha D Sc μ).map f
      map_add' := by intros; simp only [Functor.map_add, Preadditive.comp_add]
      map_smul' := by intros; simp only [Functor.map_smul, Linear.comp_smul, RingHom.id_apply] }
  map_add' := by intros; ext f; dsimp; simp only [map_add, Preadditive.add_comp]
  map_smul' := by intros; ext f; dsimp; simp only [map_smul, Linear.smul_comp]

/-- Actual upward evaluation with full abstract coefficients at the source. -/
def upwardCoefficientMap (μ : X) (t t' : List I) :
    (coefficientObj D Sc t ⟶ coefficientObj D Sc t') →ₗ[k] UpwardHom D Sc μ t t' :=
  (TensorProduct.lift (upwardCoefficientBilinear D Sc cs μ t t')).comp
    (sourceTensorEquiv D Sc t t').symm.toLinearMap

@[simp] theorem upwardCoefficientMap_source (μ : X) {t t' : List I}
    (a : SKM.SYM D k) (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    upwardCoefficientMap D Sc cs μ t t' (sourceCoefficientHom D Sc a f) =
      SKM.bubAt D Sc μ (upWord t) (SKM.betaSYM cs μ a) ≫ (alpha D Sc μ).map f := by
  change (TensorProduct.lift (upwardCoefficientBilinear D Sc cs μ t t'))
    ((sourceTensorEquiv D Sc t t').symm (sourceCoefficientHom D Sc a f)) = _
  rw [← sourceTensorEquiv_tmul, LinearEquiv.symm_apply_apply]
  rfl

/-- Observation obtained from an action at the *fixed* external weight `μ`,
evaluation on a chosen cyclic vector, and a linear coordinate-recovery map.
The recovery map may implement a bounded probe-series correction; no map is
assumed injective. Both parity components of all modules are retained. -/
def cyclicObservation (μ : X) (t t' : List I) (m : ℕ)
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (act : UpwardHom D Sc μ t t' →ₗ[k] (V →ₗ[k] W)) (v : V)
    (recover : W →ₗ[k]
      ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸
        ELVRelationSpan D Sc (fun _ => 2 * m) t t')) :
    UpwardHom D Sc μ t t' →ₗ[k]
      ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸
        ELVRelationSpan D Sc (fun _ => 2 * m) t t') where
  toFun f := recover (act f v)
  map_add' := by intros; simp
  map_smul' := by intros; simp

/-- Precise missing action obligation. For each finite list of explicit
coefficient/PBW vectors, an observation at the same external weight `μ`
recovers their coordinates in a sufficiently large *specified* ELV quotient.
No faithfulness of an action, coefficient map, or observation is a premise.
Compatibility is finite, so normalization need not be an automorphism of the
whole truncated coefficient ring. -/
def FiniteUpwardObservations (μ : X) (t t' : List I) : Prop :=
  ∀ S : Finset (SKM.SYM.CoefficientIndex D × NFIdx t t'),
    ∃ m : ℕ, S.sup (extensionDegree D) + 2 * t.length.choose 2 < 2 * m ∧
    ∃ observe : UpwardHom D Sc μ t t' →ₗ[k]
      ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸
        ELVRelationSpan D Sc (fun _ => 2 * m) t t'),
      ∀ i ∈ S, observe (upwardCoefficientMap D Sc cs μ t t' (extensionBasis D Sc t t' i)) =
        (ELVRelationSpan D Sc (fun _ => 2 * m) t t').mkQ (extensionBasis D Sc t t' i)

/-- Fixed-weight upward independence follows from finite, normalized action
observations and the independently proved explicit cyclotomic separation. -/
theorem upwardCoefficientMap_injective_of_observations (μ : X) (t t' : List I)
    (hobs : FiniteUpwardObservations D Sc cs μ t t') :
    Function.Injective (upwardCoefficientMap D Sc cs μ t t') := by
  suffices hzero : ∀ f, upwardCoefficientMap D Sc cs μ t t' f = 0 → f = 0 by
    intro f g hfg
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hfg, sub_self]
  intro f hf
  let b := extensionBasis D Sc t t'
  let S := (b.repr f).support
  obtain ⟨m, hm, observe, hcompat⟩ := hobs S
  have hmem : f ∈ ExtendedAtMost D Sc t t' (S.sup (extensionDegree D)) := by
    rw [← b.linearCombination_repr f, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.le_sup (f := extensionDegree D) hi, rfl⟩)
  have he : observe (upwardCoefficientMap D Sc cs μ t t' f) =
      (ELVRelationSpan D Sc (fun _ => 2 * m) t t').mkQ f := by
    rw [← b.linearCombination_repr f, Finsupp.linearCombination_apply, Finsupp.sum]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcompat i hi]
  have hinj := elv_quotient_injective_on_extendedAtMost D Sc
    (cutoff := fun _ => 2 * m) (t := t) (t' := t')
    (d := S.sup (extensionDegree D)) (N := 2 * m) (fun _ => le_rfl) hm
  have h := hinj (a₁ := ⟨f, hmem⟩) (a₂ := 0) (by simpa [hf] using he.symm)
  exact congrArg Subtype.val h

end OddMath.QuiverHecke
