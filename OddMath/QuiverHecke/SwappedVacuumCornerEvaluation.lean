/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuumBasisEvaluation
import OddMath.QuiverHecke.ReservoirSourceCoordinates

/-!
# The vacuum basis values from a natural corner evaluation

Research issue #345, toward the Nondegeneracy Conjecture of Brundan–Ellis,
*Super Kac–Moody 2-categories* (arXiv:1701.04133v2), §8. This file derives the
signed tensor-basis values of `SwappedVacuumBlock` (`SwappedVacuumCoordinates.md`
§§2–7) from a corner evaluation that is natural for the affine generators.

Fix a source word `s`. A `VacuumCornerEvaluation` of an upward module action `A`
consists of

* submodules `K t` of the coefficient-extended Hom spaces from `s` (the transformed
  two-sided ideal of §5);
* linear maps `ev t : A.V t → (s ⟶ t) ⧸ K t` (the evaluation at the reservoir corner,
  pulled back through the super-opposite presentation map `U` of §4);
* the generator square `ev_layer`: if `v` evaluates to the class of `y`, a generating
  layer applied to `v` evaluates to the class of `y ≫ (1 ⊗ layer)`, with no sign (§2 and
  the first part of (7)); this is consistent because the ideal of §5 is closed under
  right composition;
* the vacuum value `ev s (raw a · vac) = [a ⊗ 1]` (§3).

From these:

* `VacuumCornerEvaluation.ev_act`: naturality for every affine morphism, by
  induction over layers; only even coefficients occur, so no Koszul sign appears;
* `sourceCoefficientHom_id_comp`: `(a ⊗ 1) ≫ (1 ⊗ f) = σ(a ⊗ f)`, the placement sign;
* `VacuumCornerEvaluation.vacuum_evaluation`: the second part of (7),
  `ev(act(α f)(raw a · vac)) = [σ(a ⊗ f)]`;
* `VacuumCornerEvaluation.basis_values`: the hypothesis of
  `SwappedVacuumBlock.ofMoments`;
* `SwappedVacuumBlock.ofCornerEvaluation`: a vacuum block from moments, a corner
  evaluation and the weight bound on its ideal.

The fields of `VacuumCornerEvaluation` are the inputs still to be supplied by the
swapped action: the word values of §2 with `U` of §4 and the ideal of §5 give
`ev_layer`, and the coefficient action of §3 gives `ev_vacuum`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k}

theorem one_mem_polynomialExteriorParity_zero :
    (1 : SKM.SYM.PolynomialExterior D k) ∈ SKM.SYM.polynomialExteriorParity D k 0 :=
  SetLike.GradedOne.one_mem

theorem coefficientHom_add_right {t t' : List I} (b : SKM.SYM.PolynomialExterior D k)
    (g g' : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    coefficientHom D Sc b (g + g') = coefficientHom D Sc b g + coefficientHom D Sc b g' :=
  BoxProd.tmulHom_add_right _ _ _

theorem coefficientHom_smul_right {t t' : List I} (b : SKM.SYM.PolynomialExterior D k) (r : k)
    (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    coefficientHom D Sc b (r • g) = r • coefficientHom D Sc b g :=
  BoxProd.tmulHom_smul_right _ _ _

theorem coefficientHom_zero_right {t t' : List I} (b : SKM.SYM.PolynomialExterior D k) :
    coefficientHom D Sc b (0 : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) = 0 := by
  simpa using coefficientHom_smul_right b (0 : k) (0 : (pres D Sc).obj (ob D t) ⟶ _)

/-- An even unit coefficient composes with any coefficient without a sign. -/
theorem coefficientHom_one_comp {t t' t'' : List I}
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    (b : SKM.SYM.PolynomialExterior D k)
    (g : (pres D Sc).obj (ob D t') ⟶ (pres D Sc).obj (ob D t'')) :
    coefficientHom D Sc 1 f ≫ coefficientHom D Sc b g = coefficientHom D Sc b (f ≫ g) := by
  induction g using (pres D Sc).hom_induction with
  | diag d =>
    have hd := (pres D Sc).diag_isHomogeneous (isParityHomogeneous D Sc) d
    rw [coefficientHom_comp D Sc one_mem_polynomialExteriorParity_zero b f hd, mul_one]
    simp [Supercategory.koszulSign]
  | zero => rw [coefficientHom_zero_right, Limits.comp_zero, Limits.comp_zero,
      coefficientHom_zero_right]
  | add g g' hg hg' =>
    rw [coefficientHom_add_right, Preadditive.comp_add, hg, hg', Preadditive.comp_add,
      coefficientHom_add_right]
  | smul r g hg =>
    rw [coefficientHom_smul_right, Linear.comp_smul, hg, Linear.comp_smul,
      coefficientHom_smul_right]

/-- Placing a coefficient below an affine morphism: `(a ⊗ 1) ≫ (1 ⊗ f) = σ(a ⊗ f)`. -/
theorem sourceCoefficientHom_id_comp {t t' : List I} (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    sourceCoefficientHom D Sc a (𝟙 _) ≫ coefficientHom D Sc 1 f =
      placementSign D Sc t t' (sourceCoefficientHom D Sc a f) := by
  have ho : placementSign D Sc t t' = (reservoirSourceOrder D Sc t t' : _ →ₗ[k] _) := by
    apply (extensionBasis D Sc t t').ext
    intro j
    rw [reservoirSourceOrder_basis, LinearEquiv.coe_coe, placementSign_apply,
      placementSignMap_basis]
    unfold placementSignCoeff Supercategory.sign
    split_ifs <;> simp_all
  rw [show placementSign D Sc t t' (sourceCoefficientHom D Sc a f) =
      reservoirSourceOrder D Sc t t' (sourceCoefficientHom D Sc a f) from
    LinearMap.congr_fun ho _, reservoirSourceOrder_source]
  simp only [sourceCoefficientHom, map_one]

namespace UpwardModuleAction
variable {μ : X} (A : UpwardModuleAction D Sc μ)

/-- The action of affine morphisms between word objects through `α`. -/
def upAct (t t' : List I) :
    ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) →ₗ[k] (A.V t →ₗ[k] A.V t') :=
  (A.act t t').comp ((alpha D Sc μ).mapLinearMap k)

theorem upAct_apply {t t' : List I} (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    A.upAct t t' f = A.act t t' ((alpha D Sc μ).map f) := rfl

theorem upAct_id (t : List I) : A.upAct t t (𝟙 _) = LinearMap.id := by
  rw [upAct_apply]
  exact (congrArg (A.act t t) ((alpha D Sc μ).map_id _)).trans (A.act_id t)

theorem upAct_comp {t t' t'' : List I}
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    (g : (pres D Sc).obj (ob D t') ⟶ (pres D Sc).obj (ob D t'')) :
    A.upAct t t'' (f ≫ g) = (A.upAct t' t'' g).comp (A.upAct t t' f) := by
  rw [upAct_apply, Functor.map_comp]
  exact A.act_comp t t' t'' _ _

end UpwardModuleAction

variable (D Sc) in
/-- **A corner evaluation of an upward module action at source word `s`.** The fields
are the inputs of `SwappedVacuumCoordinates.md` §§2–5 not yet supplied by the swapped
action: submodules `K t` (the transformed ideal), evaluation maps into the quotients,
the generator square on each layer (if `v` evaluates to the class of `y`, then the layer
applied to `v` evaluates to the class of `y ≫ (1 ⊗ layer)`), and the vacuum value. The
square is consistent because the ideal of §5 is closed under right composition. -/
structure VacuumCornerEvaluation {μ : X} (A : UpwardModuleAction D Sc μ) (s : List I)
    (raw : SKM.SYM D k →ₐ[k] Module.End k (A.V s)) (vacuum : A.V s) where
  K : ∀ t, Submodule k (coefficientObj D Sc s ⟶ coefficientObj D Sc t)
  ev : ∀ t, A.V t →ₗ[k] (coefficientObj D Sc s ⟶ coefficientObj D Sc t) ⧸ K t
  ev_layer : ∀ (L : Layer (sig D)) (hv : L.Valid) (v : A.V L.dom.word)
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc L.dom.word),
    ev L.dom.word v = (K L.dom.word).mkQ y →
    ev L.cod.word (A.act L.dom.word L.cod.word
      ((alpha D Sc μ).map ((pres D Sc).diag (Diagram.ofLayer L hv))) v) =
      (K L.cod.word).mkQ (y ≫ coefficientHom D Sc 1
        (t := L.dom.word) (t' := L.cod.word) ((pres D Sc).diag (Diagram.ofLayer L hv)))
  ev_vacuum : ∀ a, ev s (raw a vacuum) = (K s).mkQ (sourceCoefficientHom D Sc a (𝟙 _))

namespace VacuumCornerEvaluation
variable {μ : X} {A : UpwardModuleAction D Sc μ} {s : List I}
  {raw : SKM.SYM D k →ₐ[k] Module.End k (A.V s)} {vacuum : A.V s}
  (E : VacuumCornerEvaluation D Sc A s raw vacuum)

/-- The corner square for one affine morphism between word objects. -/
def Square {t t' : List I} (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) : Prop :=
  ∀ (v : A.V t) (y : coefficientObj D Sc s ⟶ coefficientObj D Sc t),
    E.ev t v = (E.K t).mkQ y →
      E.ev t' (A.upAct t t' f v) = (E.K t').mkQ (y ≫ coefficientHom D Sc 1 f)

theorem square_id (t : List I) : E.Square (𝟙 ((pres D Sc).obj (ob D t))) := by
  intro v y hy
  rw [A.upAct_id, LinearMap.id_apply, hy]
  congr 1
  change y = y ≫ 𝟙 (coefficientObj D Sc t)
  exact (Category.comp_id y).symm

theorem square_comp {t t' t'' : List I}
    {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    {g : (pres D Sc).obj (ob D t') ⟶ (pres D Sc).obj (ob D t'')}
    (hf : E.Square f) (hg : E.Square g) : E.Square (f ≫ g) := by
  intro v y hy
  rw [A.upAct_comp, LinearMap.comp_apply, hg _ _ (hf v y hy), Category.assoc,
    coefficientHom_one_comp]

theorem square_zero {t t' : List I} :
    E.Square (0 : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) := by
  intro v y _
  rw [map_zero, LinearMap.zero_apply, map_zero, coefficientHom_zero_right, Limits.comp_zero,
    map_zero]

theorem square_add {t t' : List I}
    {f g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    (hf : E.Square f) (hg : E.Square g) : E.Square (f + g) := by
  intro v y hy
  have e : y ≫ coefficientHom D Sc 1 (f + g) =
      y ≫ coefficientHom D Sc 1 f + y ≫ coefficientHom D Sc 1 g := by
    rw [coefficientHom_add_right, Preadditive.comp_add]
  rw [map_add, LinearMap.add_apply, map_add, hf v y hy, hg v y hy, e,
    LinearMap.map_add]

theorem square_smul {t t' : List I} (r : k)
    {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    (hf : E.Square f) : E.Square (r • f) := by
  intro v y hy
  rw [map_smul, LinearMap.smul_apply, map_smul, hf v y hy, coefficientHom_smul_right,
    Linear.comp_smul, map_smul]

/-- **Naturality of the corner evaluation** for every affine morphism, by induction
over the generating layers. -/
theorem ev_act {t t' : List I} (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    (v : A.V t) (y : coefficientObj D Sc s ⟶ coefficientObj D Sc t)
    (hy : E.ev t v = (E.K t).mkQ y) :
    E.ev t' (A.act t t' ((alpha D Sc μ).map f) v) =
      (E.K t').mkQ (y ≫ coefficientHom D Sc 1 f) := by
  have key : ∀ {a b : Obj (sig D)} (f : (pres D Sc).obj a ⟶ (pres D Sc).obj b),
      E.Square (t := a.word) (t' := b.word) f := by
    intro a b f
    induction f using (pres D Sc).hom_induction_layers with
    | nil h =>
      subst h
      rw [eqToHom_refl, (pres D Sc).diag_id]
      exact E.square_id _
    | layer L hv => exact E.ev_layer L hv
    | comp f g hf hg => exact E.square_comp hf hg
    | zero => exact E.square_zero
    | add f g hf hg => exact E.square_add hf hg
    | smul r f hf => exact E.square_smul r hf
  exact key (a := ob D t) (b := ob D t') f v y hy

/-- **(7) of `SwappedVacuumCoordinates.md`**: the corner evaluation of `α f` applied to a
coefficient on the vacuum is the class of the placed coefficient `σ(a ⊗ f)`. -/
theorem vacuum_evaluation {t' : List I} (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t')) :
    E.ev t' (A.act s t' ((alpha D Sc μ).map f) (raw a vacuum)) =
      (E.K t').mkQ (placementSign D Sc s t' (sourceCoefficientHom D Sc a f)) := by
  rw [E.ev_act f _ _ (E.ev_vacuum a), sourceCoefficientHom_id_comp]

/-- The signed basis values: the hypothesis of `SwappedVacuumBlock.ofMoments`. -/
theorem basis_values {t' : List I} (a : SKM.SYM.CoefficientIndex D) (i : NFIdx s t') :
    E.ev t' (A.act s t' ((alpha D Sc μ).map i.nf)
      (raw (SKM.SYM.coefficientBasis D k a) vacuum)) =
      basisKoszulSign k a i • (E.K t').mkQ
        (sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k a) i.nf) := by
  rw [E.vacuum_evaluation, placementSign_sourceCoefficientHom, map_smul]

end VacuumCornerEvaluation

variable (cs : SKM.CScalars Sc)

/-- **A vacuum block from moments and a corner evaluation**: the right-bubble moments at
the schedule, a natural corner evaluation, and the weight bound on its ideal at the
target word. -/
def SwappedVacuumBlock.ofCornerEvaluation {μ : X} {t t' : List I} {d : ℕ}
    (A : UpwardModuleAction D Sc μ) (vacuum : A.V t)
    (raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t))
    (hm : VacuumMoments cs A t raw (probeExponent D μ t d) (reservoirLevel D μ t d))
    (E : VacuumCornerEvaluation D Sc A t raw vacuum)
    (ideal_le : E.K t' ≤ ExtendedAtLeast D Sc t t'
      ((vacuumCutoff t d : ℤ) - 2 * t.length.choose 2)) :
    SwappedVacuumBlock D Sc cs μ t t' d :=
  SwappedVacuumBlock.ofMoments cs A vacuum raw hm (E.K t') ideal_le (E.ev t') E.basis_values

end OddMath.QuiverHecke
