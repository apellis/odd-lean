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

end

variable (cs : SKM.CScalars Sc)

end OddMath.QuiverHecke
