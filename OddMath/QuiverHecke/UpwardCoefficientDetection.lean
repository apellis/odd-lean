/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ELVCyclotomicSeparation
import OddMath.QuiverHecke.Alpha
import OddMath.SKM.BubbleAlgebra
import OddMath.SKM.SpanBubbleProd

/-! # Vacuum-coordinate observations for upward coefficient independence

The map uses source-placed `betaSYM` and the upward functor `alpha`.
Finite observations below recover a quotient on the active words alone.
They are a sufficient criterion, not the interface directly supplied by a
cyclotomic action with spectators. See `SpectatorDetection` for that interface.
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

end OddMath.QuiverHecke
