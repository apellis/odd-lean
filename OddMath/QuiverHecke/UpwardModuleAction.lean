/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ReservoirVacuumDetection

/-! # Upward module actions at a fixed weight

The output interface of a 2-representation of `𝔘(𝔤)` after evaluation at a
fixed rightmost weight `μ` (Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5). An `UpwardModuleAction` assigns a
`k`-module `V t` to each upward word `E_t 1_μ` and acts by the upward Hom
spaces `UpwardHom D Sc μ t t'`, functorially. The finite-colour swapped Hom
action of `docs/Nondegeneracy/SwappedActionAssembly.md`, evaluated on one
Hom sector, is to be supplied in this form.

The bubble algebra then acts on every `V t` through `β` placed in the
rightmost region (`UpwardModuleAction.bubbles`); multiplicativity is proved
here, not assumed. `UpwardModuleAction.toReservoirVacuumEvaluation` turns an
upward action, together with a vacuum, reservoir coordinates and their
recovery maps, into the consumer `ReservoirVacuumEvaluation`. No action is
constructed in this file.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- A functorial `k`-linear action of the upward Hom spaces at rightmost weight `μ`. -/
structure UpwardModuleAction (μ : X) where
  V : List I → Type w
  [addV : ∀ t, AddCommGroup (V t)]
  [moduleV : ∀ t, Module k (V t)]
  act : ∀ t t', UpwardHom D Sc μ t t' →ₗ[k] (V t →ₗ[k] V t')
  act_id : ∀ t, act t t (𝟙 _) = LinearMap.id
  act_comp : ∀ t t' t'' (f : UpwardHom D Sc μ t t') (g : UpwardHom D Sc μ t' t''),
    act t t'' (f ≫ g) = (act t' t'' g).comp (act t t' f)

attribute [instance] UpwardModuleAction.addV UpwardModuleAction.moduleV

variable {D Sc}
namespace UpwardModuleAction
variable {μ : X} (A : UpwardModuleAction D Sc μ)

/-- Closed diagrams in the rightmost region, acting on `V t`. -/
def closedAct (t : List I) :
    End ((SKM.pres D Sc).obj (SKM.ob D μ [])) →ₐ[k] Module.End k (A.V t) where
  toFun β := A.act t t (SKM.bubAt D Sc μ (upWord t) β)
  map_one' := by
    change A.act t t (SKM.bubAt D Sc μ (upWord t) (𝟙 _)) = LinearMap.id
    rw [SKM.bubAt_id, A.act_id]
  map_mul' β γ := by
    change A.act t t (SKM.bubAt D Sc μ (upWord t) (γ ≫ β)) = _
    rw [SKM.bubAt_comp, A.act_comp]
    rfl
  map_zero' := by simp
  map_add' := by intros; simp
  commutes' r := by
    change A.act t t (SKM.bubAt D Sc μ (upWord t) (r • 𝟙 _)) = _
    rw [map_smul, SKM.bubAt_id, map_smul, A.act_id]
    rfl


/-- The bubble algebra acting on `V t` through `β` of (1.22). -/
def bubbles (t : List I) : SKM.SYM D k →ₐ[k] Module.End k (A.V t) :=
  (A.closedAct t).comp (SKM.betaSYM cs μ)

theorem bubbles_apply (t : List I) (a : SKM.SYM D k) :
    A.bubbles cs t a = A.act t t (SKM.bubAt D Sc μ (upWord t) (SKM.betaSYM cs μ a)) := rfl


/-- An upward action, a vacuum, reservoir coordinates and their recovery maps
give the reservoir-vacuum consumer. The bubble field is the derived action. -/
def toReservoirVacuumEvaluation (cutoff : I → ℕ) (vacuum : ∀ t, A.V t)
    (reservoir : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (A.V t))
    (recover : ∀ t t', A.V t' →ₗ[k] ReservoirQuotient D Sc cutoff t t')
    (window : List I → List I → ℕ)
    (affine_coordinates : ∀ t t' (a : SKM.SYM D k)
      (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')),
      sourceCoefficientHom D Sc a f ∈ ExtendedAtMost D Sc t t' (window t t') →
      recover t t' (A.act t t' ((alpha D Sc μ).map f) (reservoir t a (vacuum t))) =
        (ELVRelationSpan D Sc cutoff t t').mkQ (sourceCoefficientHom D Sc a f)) :
    ReservoirVacuumEvaluation D Sc cs μ cutoff where
  V := A.V
  act := A.act
  act_comp := A.act_comp
  vacuum := vacuum
  bubbles := A.bubbles cs
  bubbles_eq _ _ := rfl
  reservoir := reservoir
  recover := recover
  window := window
  affine_coordinates := affine_coordinates

end UpwardModuleAction
end OddMath.QuiverHecke
