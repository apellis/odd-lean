/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendTensorRightDot
import OddMath.QuiverHecke.CyclotomicAction.BoundaryCosets

/-!
# The target side of the append-side Mackey boundary

`MackeyCosets` (`BoundaryCosets.lean`) bundles claims about the target `L₀` (its decomposition
`L₀ = F(L₀') ⊕ j(V₀)`, the dot slides and the right `B`-action) with claims about the source
`L₁` and the map `P`. `MackeyTarget` records the target-side fields alone, and
`MackeyCosets.ofTarget` assembles a `MackeyCosets` from them and the source-side data.

For a ring `B` that is a left `Hn (n+1)`-module with `(r • y) b = r • (y b)`, and a ring
endomorphism `σ` of `B` with `σ (r • y) = tw(r) • σ y` (`tw` the parity twist of the appended
colour), `appendMackeyTarget` instantiates every target-side field on

* `L₀ = ψ(1) (Hn (n+2) ψ(1) ⊗_(Hn (n+1)) B)` (`appendTensorFixed`),
* `L₀' = ⊕_(j ≤ n, m) ψ'(1) B` (`appendTensorLeftCoordinates`),

with `F`, `j` the two summands of `appendTensorCornerEquiv` (so `direct` and `span` are that
equivalence), `R_t` the `σ`-twisted right dot `appendTensorRightDot`, and the right `B`-action
`z ⊗ y ↦ z ⊗ y b`. This is the target of `DeformedMackeyBoundary.md` (append side,
`AppendCoordinates.md` §4; Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Lemma 8.1, mirror
form).
-/

noncomputable section
open Finsupp Categorification StringDiagrams

namespace OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

variable {B : Type*} [Ring B] (σ : B →+* B)

/-- The target-side fields of `MackeyCosets`. -/
structure MackeyTarget (L₀ L₀' : Type*) [AddCommGroup L₀] [AddCommGroup L₀'] where
  /-- The target right-dot action `R_t`. -/
  Rt : L₀ →+ L₀
  /-- The crossing summand `F : L₀' → L₀`. -/
  F : L₀' →+ L₀
  /-- The polynomial summand. -/
  j : (ℕ →₀ B) →+ L₀
  /-- The crossing-contraction operator `X` on `L₀'`. -/
  X : L₀' →+ L₀'
  /-- The degree-zero operator `E : L₀' → B`. -/
  E : L₀' →+ B
  /-- The right `B`-action on the target. -/
  r₀ : B → L₀ →+ L₀
  Rt_F : ∀ u, Rt (F u) = F (X u) + j (single 0 (E u))
  Rt_j : ∀ f, Rt (j f) = j (tShift σ f)
  direct : ∀ u f, F u + j f = 0 → u = 0 ∧ f = 0
  span : ∀ y, ∃ u f, y = F u + j f
  F_r : ∀ (b : B) u, ∃ u', r₀ b (F u) = F u'
  j_r : ∀ (b : B) f, r₀ b (j f) = j (rsmul b f)

end OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

namespace OddMath.QuiverHecke
open CyclotomicAction.BoundaryPolynomial
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (n : ℕ) (B : Type w) [Ring B] [Module (Hn D Sc (n + 1)) B]
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "T" => InductionAlong.Ind B ψ

/-! ## The two summands -/

/-- The crossing summand `F u = Σ ψ(c'_j x^m) τ ⊗ u_(j,m)`. -/
def appendTargetF : appendTensorLeftCoordinates D Sc i n B →+ appendTensorFixed D Sc i n B :=
  (appendTensorCornerEquiv D Sc i n B).toAddMonoidHom.comp (AddMonoidHom.inl _ _)

/-- The polynomial summand `j g = Σ z^m ⊗ g_m`. -/
def appendTargetJ : (ℕ →₀ B) →+ appendTensorFixed D Sc i n B :=
  (appendTensorCornerEquiv D Sc i n B).toAddMonoidHom.comp (AddMonoidHom.inr _ _)

@[simp] theorem appendTargetF_coe (u : appendTensorLeftCoordinates D Sc i n B) :
    (appendTargetF D Sc i n B u : T) = appendLeftTensor D Sc i n B u.1 := by
  simp [appendTargetF, appendTensorCornerEquiv_apply]

@[simp] theorem appendTargetJ_coe (f : ℕ →₀ B) :
    (appendTargetJ D Sc i n B f : T) = appendPolyTensor D Sc i n B f := by
  simp [appendTargetJ, appendTensorCornerEquiv_apply]

/-! ## The twisted right dot -/

variable (σ : B →+* B)
  (hσ : ∀ (r : Hn D Sc (n + 1)) (y : B),
    σ (r • y) = homMatrixTwist D Sc (n + 1) (D.parity i) r • σ y)

/-- The `σ`-twisted right dot on the `ψ(1)`-fixed part. -/
def appendTargetRt : appendTensorFixed D Sc i n B →+ appendTensorFixed D Sc i n B :=
  AddMonoidHom.codRestrict
    ((appendTensorRightDot D Sc i n B σ.toAddMonoidHom hσ).toAddMonoidHom.comp
      (appendTensorFixed D Sc i n B).subtype)
    _ fun t => appendTensorRightDot_mem_fixed D Sc i n B _ hσ t.1 t.2

@[simp] theorem appendTargetRt_coe (t : appendTensorFixed D Sc i n B) :
    (appendTargetRt D Sc i n B σ hσ t : T) =
      appendTensorRightDot D Sc i n B σ.toAddMonoidHom hσ t.1 := rfl

/-! ## Right multiplication on the coefficients -/

variable [IsScalarTower (Hn D Sc (n + 1)) B B]

/-- Right multiplication by `b` as a left `Hn (n+1)`-linear map of `B`. -/
def appendCoefficientMulRight (b : B) : B →ₗ[Hn D Sc (n + 1)] B where
  toFun y := y * b
  map_add' y y' := add_mul y y' b
  map_smul' r y := smul_mul_assoc r y b

end OddMath.QuiverHecke
