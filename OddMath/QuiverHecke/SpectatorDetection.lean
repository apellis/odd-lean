/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.UpwardMatchingIndependence

/-! # Fixed-weight evaluation with spectator strands

Supporting the upward-independence step of the nondegeneracy programme.
An evaluation takes values in a cyclotomic Hom space on the *whole* word,
including spectators. Its coefficient image is a product of specified bubble
images and the affine action. Joint detection of these products is a separate
hypothesis; neither bubble independence nor affine independence implies it.

This is an interface extracted from an action, not a construction of an action.
In particular, its bubble images and product compatibility remain obligations.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- The cyclotomic quotient uses the content of spectators and active strands. -/
abbrev SpectatorQuotient (cutoff : I → ℕ) (s t t' : List I) :=
  (coefficientObj D Sc (s ++ t) ⟶ coefficientObj D Sc (s ++ t')) ⧸
    ELVRelationSpan D Sc cutoff (s ++ t) (s ++ t')

/-- The affine operator is ordinary whiskering by the spectator identity,
followed by extension of scalars. It is not an arbitrary coordinate map. -/
def spectatorAffine (s t t' : List I) :
    ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) →ₗ[k]
      (coefficientObj D Sc (s ++ t) ⟶ coefficientObj D Sc (s ++ t')) where
  toFun f := sourceCoefficientHom D Sc 1 ((pres D Sc).obj (ob D s) ◁ f)
  map_add' := by
    intro f g
    rw [MonoidalSupercategory.whiskerLeft_add (R := k)]
    exact sourceCoefficientHom_add_right D Sc (t := s ++ t) (t' := s ++ t') 1 _ _
  map_smul' := by
    intro r f
    rw [MonoidalSupercategory.whiskerLeft_smul (R := k)]
    exact sourceCoefficientHom_smul_right D Sc (t := s ++ t) (t' := s ++ t') 1 r _

/-- Algebraic data of an evaluation object at `μ`. The base weight need not be
fixed as the cutoff changes. A lowest-weight realization must additionally
identify it with its lowest weight; this structure does not assert dominance. -/
structure SpectatorImage (μ : X) (t t' : List I) where
  spectators : List I
  baseWeight : X
  weight_eq : SKM.wt D baseWeight (upWord spectators) = μ
  cutoff : I → ℕ
  bubble : SKM.SYM D k →ₗ[k]
    (coefficientObj D Sc (spectators ++ t) ⟶ coefficientObj D Sc (spectators ++ t))

variable {D Sc}
namespace SpectatorImage
variable {μ : X} {t t' : List I} (P : SpectatorImage D Sc μ t t')

/-- The specified bubble operator followed by the specified affine operator.
Composition is in the signed coefficient category, not an unsigned tensor model. -/
def productBilinear : SKM.SYM D k →ₗ[k]
    (((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) →ₗ[k]
      (coefficientObj D Sc (P.spectators ++ t) ⟶ coefficientObj D Sc (P.spectators ++ t'))) where
  toFun a :=
    { toFun := fun f => P.bubble a ≫ spectatorAffine D Sc P.spectators t t' f
      map_add' := by intros; simp only [map_add, Preadditive.comp_add]
      map_smul' := by intros; simp only [map_smul, Linear.comp_smul, RingHom.id_apply] }
  map_add' := by intros; ext f; dsimp; simp only [map_add, Preadditive.add_comp]
  map_smul' := by intros; ext f; dsimp; simp only [map_smul, Linear.smul_comp]

/-- Algebraic image of the full coefficient-extended affine morphism. -/
def image : (coefficientObj D Sc t ⟶ coefficientObj D Sc t') →ₗ[k]
    (coefficientObj D Sc (P.spectators ++ t) ⟶ coefficientObj D Sc (P.spectators ++ t')) :=
  (TensorProduct.lift P.productBilinear).comp (sourceTensorEquiv D Sc t t').symm.toLinearMap

@[simp] theorem image_source (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    P.image (sourceCoefficientHom D Sc a f) = P.bubble a ≫ spectatorAffine D Sc P.spectators t t' f := by
  change (TensorProduct.lift P.productBilinear)
    ((sourceTensorEquiv D Sc t t').symm (sourceCoefficientHom D Sc a f)) = _
  rw [← sourceTensorEquiv_tmul, LinearEquiv.symm_apply_apply]
  rfl

/-- The algebraic cyclotomic image, with no categorical faithfulness premise. -/
def quotientImage : (coefficientObj D Sc t ⟶ coefficientObj D Sc t') →ₗ[k]
    SpectatorQuotient D Sc P.cutoff P.spectators t t' :=
  (ELVRelationSpan D Sc P.cutoff (P.spectators ++ t) (P.spectators ++ t')).mkQ.comp P.image

end SpectatorImage
variable (D Sc)

/-- The component of an upward action on the regular object with spectators.
The cyclic vector is the identity of the whole source word. Only the product
law needed by detection is retained; full 2-representation coherence is not
asserted by this extracted interface. -/
structure SpectatorEvaluation (μ : X) (t t' : List I)
    (P : SpectatorImage D Sc μ t t') where
  act : UpwardHom D Sc μ t t' →ₗ[k]
    (SpectatorQuotient D Sc P.cutoff P.spectators t t →ₗ[k]
      SpectatorQuotient D Sc P.cutoff P.spectators t t')
  product_law : ∀ (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')),
    act (upwardCoefficientMap D Sc cs μ t t' (sourceCoefficientHom D Sc a f))
      ((ELVRelationSpan D Sc P.cutoff (P.spectators ++ t) (P.spectators ++ t)).mkQ (𝟙 _)) =
    P.quotientImage (sourceCoefficientHom D Sc a f)

variable {D Sc cs}
namespace SpectatorEvaluation
variable {μ : X} {t t' : List I} {P : SpectatorImage D Sc μ t t'}
  (E : SpectatorEvaluation D Sc cs μ t t' P)

/-- Evaluation at the cyclic identity, without a vacuum coordinate-recovery map. -/
def observe : UpwardHom D Sc μ t t' →ₗ[k]
    SpectatorQuotient D Sc P.cutoff P.spectators t t' where
  toFun f := E.act f
    ((ELVRelationSpan D Sc P.cutoff (P.spectators ++ t) (P.spectators ++ t)).mkQ (𝟙 _))
  map_add' := by intros; simp
  map_smul' := by intros; simp

theorem observe_coefficient (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t') :
    E.observe (upwardCoefficientMap D Sc cs μ t t' f) = P.quotientImage f := by
  obtain ⟨x, rfl⟩ := (sourceTensorEquiv D Sc t t').surjective f
  induction x using TensorProduct.inductionOn with
  | tmul a f => exact E.product_law a f
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end SpectatorEvaluation
variable (D Sc cs)

/-- Fixed-weight upward independence from joint algebraic detection. The same
`μ` occurs in every evaluation, while spectators and cutoffs may vary freely.
Joint detection is an explicit missing algebraic input, not a consequence of
the separate independence of bubbles and affine diagrams. -/
theorem upwardCoefficientMap_injective_of_spectators (μ : X) (t t' : List I)
    {A : Type*} (P : A → SpectatorImage D Sc μ t t')
    (E : ∀ a, SpectatorEvaluation D Sc cs μ t t' (P a))
    (hdetect : ∀ f, (∀ a, (P a).quotientImage f = 0) → f = 0) :
    Function.Injective (upwardCoefficientMap D Sc cs μ t t') := by
  suffices hz : ∀ f, upwardCoefficientMap D Sc cs μ t t' f = 0 → f = 0 by
    intro f g h
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, h, sub_self]
  intro f hf
  apply hdetect f
  intro a
  rw [← (E a).observe_coefficient, hf, map_zero]

/-- Spectator evaluations at every external weight supply the upward
independence hypothesis consumed by the oriented reduction. -/
theorem upward_independence_of_spectators {A : Type*}
    (P : ∀ (μ : X) (t t' : List I), A → SpectatorImage D Sc μ t t')
    (E : ∀ μ t t' a, SpectatorEvaluation D Sc cs μ t t' (P μ t t' a))
    (hdetect : ∀ μ t t' f, (∀ a, (P μ t t' a).quotientImage f = 0) → f = 0) :
    SKM.WeakMate.UpwardIndependence cs := by
  apply upward_independence_of_coefficientMap D Sc cs
  intro t t' _ μ
  exact upwardCoefficientMap_injective_of_spectators D Sc cs μ t t'
    (P μ t t') (E μ t t') (hdetect μ t t')

end OddMath.QuiverHecke
