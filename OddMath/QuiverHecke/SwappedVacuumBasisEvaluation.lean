/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuumBubbleSeries

/-!
# The vacuum evaluation from its values on the tensor basis

Research issue #345, toward the Nondegeneracy Conjecture of Brundan–Ellis,
*Super Kac–Moody 2-categories* (arXiv:1701.04133v2), §8. The literal vacuum
evaluation (A18) of `SwappedVacuumBlock` is bilinear in the source coefficient
and the affine morphism. This file reduces it to the tensor basis
`coefficientBasis a ⊗ nf i`, where the swapped evaluation carries the Koszul sign
`(-1)^(|a||i|)` of source placement (`SwappedVacuumCoordinates.md` (2)–(3) and §7:
`(-1)^(|b||z|) z b a = b z a`), and identifies that sign with `placementSign`:

* `vacuum_evaluation_raw_of_basis`: the basis values with the Koszul sign give the
  raw form of (A18) for every coefficient and morphism;
* `vacuum_evaluation_of_basis`: hence (A18) for any bubble substitution `θ`, in the
  form of the field `SwappedVacuumBlock.evaluation`;
* `SwappedVacuumBlock.ofMoments`: a vacuum block from an upward module action, the
  right-bubble moments (`VacuumMoments`), the ideal with its weight bound, and the
  basis evaluation.

The basis values themselves are the computation of `SwappedVacuumCoordinates.md`
§§2–7 and remain hypotheses here.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k}

variable (k) in
/-- The Koszul sign `(-1)^(|a||i|)` of a tensor basis vector. -/
abbrev basisKoszulSign {t t' : List I} (a : SKM.SYM.CoefficientIndex D) (i : NFIdx t t') : k :=
  if ((a.2.card : ZMod 2) * i.par D) = 0 then 1 else -1

section
variable {μ : X} (A : UpwardModuleAction D Sc μ) {t t' : List I} (vacuum : A.V t)
  (raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t))
  (ideal : Submodule k (coefficientObj D Sc t ⟶ coefficientObj D Sc t'))
  (coordinate : A.V t' →ₗ[k] ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ ideal))

/-- The swapped vacuum evaluation `(b, f) ↦ coordK(act(α f)(raw b · vac))`, bilinear. -/
def vacuumEvaluationBilin :
    SKM.SYM D k →ₗ[k] ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) →ₗ[k]
      ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ ideal) :=
  LinearMap.mk₂ k (fun b f => coordinate (A.act t t' ((alpha D Sc μ).map f) (raw b vacuum)))
    (fun b b' f => by simp only [map_add, LinearMap.add_apply])
    (fun c b f => by simp only [map_smul, LinearMap.smul_apply])
    (fun b f f' => by simp only [Functor.map_add, map_add, LinearMap.add_apply])
    (fun c b f => by simp only [Functor.map_smul, map_smul, LinearMap.smul_apply])

/-- The placed source coefficient `(b, f) ↦ q_K(σ(b ⊗ f))`, bilinear. -/
def placedCoefficientBilin :
    SKM.SYM D k →ₗ[k] ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) →ₗ[k]
      ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ ideal) :=
  (TensorProduct.mk k _ _).compr₂ (ideal.mkQ ∘ₗ (placementSign D Sc t t').toLinearMap ∘ₗ
    (sourceTensorEquiv D Sc t t').toLinearMap)

/-- **(A18), raw form, from the tensor basis**: if the swapped evaluation of each
basis vector `coefficientBasis a ⊗ nf i` is the class of that vector times the
Koszul sign `(-1)^(|a||i|)`, then for every coefficient `b` and morphism `f` the
evaluation is the class of the placed coefficient `σ(b ⊗ f)`. -/
theorem vacuum_evaluation_raw_of_basis
    (h : ∀ (a : SKM.SYM.CoefficientIndex D) (i : NFIdx t t'),
      coordinate (A.act t t' ((alpha D Sc μ).map i.nf)
        (raw (SKM.SYM.coefficientBasis D k a) vacuum)) =
        basisKoszulSign k a i • ideal.mkQ
          (sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k a) i.nf))
    (b : SKM.SYM D k) (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    coordinate (A.act t t' ((alpha D Sc μ).map f) (raw b vacuum)) =
      ideal.mkQ (placementSign D Sc t t' (sourceCoefficientHom D Sc b f)) := by
  have e : vacuumEvaluationBilin A vacuum raw ideal coordinate = placedCoefficientBilin ideal :=
    LinearMap.ext_basis (SKM.SYM.coefficientBasis D k) (basisNF D Sc t t') fun a i => by
      simp only [vacuumEvaluationBilin, placedCoefficientBilin, LinearMap.mk₂_apply,
        LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, sourceTensorEquiv_tmul, basisNF_apply, h,
        placementSign_sourceCoefficientHom, map_smul, Submodule.mkQ_apply]
  have := LinearMap.congr_fun₂ e b f
  simpa only [vacuumEvaluationBilin, placedCoefficientBilin, LinearMap.mk₂_apply,
    LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, sourceTensorEquiv_tmul] using this

/-- **(A18) from the tensor basis**, for any bubble substitution `θ`: the form of the
field `SwappedVacuumBlock.evaluation`. -/
theorem vacuum_evaluation_of_basis (θ : SKM.SYM D k ≃ₐ[k] SKM.SYM D k)
    (h : ∀ (a : SKM.SYM.CoefficientIndex D) (i : NFIdx t t'),
      coordinate (A.act t t' ((alpha D Sc μ).map i.nf)
        (raw (SKM.SYM.coefficientBasis D k a) vacuum)) =
        basisKoszulSign k a i • ideal.mkQ
          (sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k a) i.nf))
    (a : SKM.SYM D k) (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    coordinate (A.act t t' ((alpha D Sc μ).map f) (raw (θ a) vacuum)) =
      ideal.mkQ (placementSign D Sc t t'
        (coefficientSubstitution D Sc θ t t' (sourceCoefficientHom D Sc a f))) := by
  rw [coefficientSubstitution_source]
  exact vacuum_evaluation_raw_of_basis A vacuum raw ideal coordinate h (θ a) f

end

variable (cs : SKM.CScalars Sc)

/-- **A vacuum block from moments and basis values**: an upward module action with a
vacuum, raw coefficient action, right-bubble moments at the schedule, a last-boundary
ideal with its weight bound and coordinates whose basis values carry the source
placement sign. -/
def SwappedVacuumBlock.ofMoments {μ : X} {t t' : List I} {d : ℕ}
    (A : UpwardModuleAction D Sc μ) (vacuum : A.V t)
    (raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t))
    (hm : VacuumMoments cs A t raw (probeExponent D μ t d) (reservoirLevel D μ t d))
    (ideal : Submodule k (coefficientObj D Sc t ⟶ coefficientObj D Sc t'))
    (ideal_le : ideal ≤ ExtendedAtLeast D Sc t t'
      ((vacuumCutoff t d : ℤ) - 2 * t.length.choose 2))
    (coordinate : A.V t' →ₗ[k] ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ ideal))
    (h : ∀ (a : SKM.SYM.CoefficientIndex D) (i : NFIdx t t'),
      coordinate (A.act t t' ((alpha D Sc μ).map i.nf)
        (raw (SKM.SYM.coefficientBasis D k a) vacuum)) =
        basisKoszulSign k a i • ideal.mkQ
          (sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k a) i.nf)) :
    SwappedVacuumBlock D Sc cs μ t t' d where
  A := A
  vacuum := vacuum
  raw := raw
  bubbles_eq := hm.vacuum_bubbles_eq
  ideal := ideal
  ideal_le := ideal_le
  coordinate := coordinate
  evaluation := vacuum_evaluation_of_basis A vacuum raw ideal coordinate _ h

end OddMath.QuiverHecke
