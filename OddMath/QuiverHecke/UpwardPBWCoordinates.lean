/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.UpwardCoefficientDetection

/-! # Full-SYM coordinates of the native upward PBW expansion -/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

def coefficientPBWCoordinate {t t' : List I} (i : NFIdx t t') :
    (coefficientObj D Sc t ⟶ coefficientObj D Sc t') →ₗ[k] SKM.SYM D k :=
  (TensorProduct.rid k (SKM.SYM D k)).toLinearMap.comp
    ((TensorProduct.map (LinearMap.id : SKM.SYM D k →ₗ[k] SKM.SYM D k)
      ((basisNF D Sc t t').coord i)).comp (sourceTensorEquiv D Sc t t').symm.toLinearMap)

@[simp] theorem coefficientPBWCoordinate_source {t t' : List I} (i j : NFIdx t t') (a : SKM.SYM D k) :
    coefficientPBWCoordinate D Sc i (sourceCoefficientHom D Sc a (j.nf (D := D) (Sc := Sc))) =
      if j = i then a else 0 := by
  unfold coefficientPBWCoordinate
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← sourceTensorEquiv_tmul, LinearEquiv.symm_apply_apply]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.rid_tmul]
  have hc : (basisNF D Sc t t').coord i j.nf = if j = i then 1 else 0 := by
    change (basisNF D Sc t t').repr j.nf i = _
    rw [← basisNF_apply D Sc t t' j, Module.Basis.repr_self, Finsupp.single_apply]
  rw [hc]
  split_ifs <;> simp

def coefficientPBWExpansion (t t' : List I) :
    (NFIdx t t' →₀ SKM.SYM D k) →ₗ[k] (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  Finsupp.lsum k (fun i =>
    { toFun := fun a => sourceCoefficientHom D Sc a (i.nf (D := D) (Sc := Sc))
      map_add' := fun a b => sourceCoefficientHom_add_left D Sc a b _
      map_smul' := fun r a => sourceCoefficientHom_smul D Sc r a _ })

@[simp] theorem coefficientPBWExpansion_single {t t' : List I} (i : NFIdx t t') (a : SKM.SYM D k) :
    coefficientPBWExpansion D Sc t t' (Finsupp.single i a) = sourceCoefficientHom D Sc a i.nf :=
  Finsupp.lsum_single k _ i a

@[simp] theorem coefficientPBWCoordinate_expansion {t t' : List I}
    (i : NFIdx t t') (f : NFIdx t t' →₀ SKM.SYM D k) :
    coefficientPBWCoordinate D Sc i (coefficientPBWExpansion D Sc t t' f) = f i := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single j a => simp [Finsupp.single_apply]

theorem coefficientPBWExpansion_injective (t t' : List I) :
    Function.Injective (coefficientPBWExpansion D Sc t t') := by
  intro f g h
  ext i
  simpa only [coefficientPBWCoordinate_expansion] using congrArg (coefficientPBWCoordinate D Sc i) h

def upwardPBWExpansion (μ : X) (t t' : List I) :
    (NFIdx t t' →₀ SKM.SYM D k) →ₗ[k] UpwardHom D Sc μ t t' :=
  (upwardCoefficientMap D Sc cs μ t t').comp (coefficientPBWExpansion D Sc t t')

@[simp] theorem upwardPBWExpansion_single (μ : X) {t t' : List I} (i : NFIdx t t') (a : SKM.SYM D k) :
    upwardPBWExpansion D Sc cs μ t t' (Finsupp.single i a) =
      SKM.bubAt D Sc μ (upWord t) (SKM.betaSYM cs μ a) ≫ (alpha D Sc μ).map i.nf := by
  simp [upwardPBWExpansion]

theorem upwardPBWExpansion_injective_of_observations (μ : X) (t t' : List I)
    (h : FiniteUpwardObservations D Sc cs μ t t') :
    Function.Injective (upwardPBWExpansion D Sc cs μ t t') :=
  (upwardCoefficientMap_injective_of_observations D Sc cs μ t t' h).comp
    (coefficientPBWExpansion_injective D Sc t t')

end OddMath.QuiverHecke
