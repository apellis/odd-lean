/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendCornerTensor

/-!
# The twisted right dot on append-induced modules

The new dot `x_(n+2)` only supercommutes with the append map: `ψ(r) x = x ψ(tw r)`
(`affineLastDot_twist_comm`). Right multiplication by it therefore descends to the induced
module `Ind M = Hn (n+2) ψ(1) ⊗_(Hn (n+1)) M` only after twisting the coefficients. We encode
the twist by an additive map `θ : M → M` with

`θ (r • y) = tw(r) • θ y`,

where `tw` is the parity twist `homMatrixTwist (n+1) (D.parity i)`. For the regular
supermodule of the cyclotomic quotient this is the parity involution `rightDotCoefficient`
(`rightDotCoefficient_smul`).

Main results: the twisted right dot `appendTensorRightDot θ` (`z ⊗ y ↦ z x ⊗ θ y`), its action
on the two summands of `appendTensorCornerEquiv`,

* `R_t(Σ z^m ⊗ g_m) = Σ z^(m+1) ⊗ θ g_m`,
* `R_t(Σ ψ(c'_j x^m) τ ⊗ f_(j,m)) = s Σ ψ(c'_j x^(m+1)) τ ⊗ θ f_(j,m) - s (1 ⊗ Σ c'_j x^m ψ'(1) θ f_(j,m))`,

with `s = koszulSign (D.parity i) (D.parity i)`, and the stability of the `ψ(1)`-fixed part and
of the left-crossing coordinates. These are the module forms of `appendPolySum_mul_lastDot`
and `appendLeftSum_mul_lastDot` (the identities `R_t j = j t` and `R_t F = F X + j E` of
`DeformedMackeyBoundary.md`, append side; Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of
Lemma 8.1, mirror form).
-/

noncomputable section
open StringDiagrams Categorification MulOpposite
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (n : ℕ) (M : Type w) [AddCommGroup M] [Module (Hn D Sc (n + 1)) M]
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "C" => InductionAlong.Corner ψ
local notation "T" => InductionAlong.Ind M ψ

variable (θ : M →+ M)
  (hθ : ∀ (r : Hn D Sc (n + 1)) (y : M),
    θ (r • y) = homMatrixTwist D Sc (n + 1) (D.parity i) r • θ y)

/-- The twisted right dot `z ⊗ y ↦ z x_(n+2) ⊗ θ y` on the induced module. -/
def appendTensorRightDot : Module.End (Hn D Sc (n + 1 + 1)) T :=
  InductionAlong.Ind.lift
    (fun z y => InductionAlong.Ind.tmul (rightDotCorner D Sc i (n + 1) z) (θ y))
    (by intros; rw [map_add, InductionAlong.Ind.add_tmul])
    (by intros; rw [map_add, InductionAlong.Ind.tmul_add])
    (by intros; rw [rightDotCorner_op_smul, InductionAlong.Ind.op_smul_tmul, hθ])
    (by intros; rw [map_smul, InductionAlong.Ind.smul_tmul])

/-! ## Coordinate maps -/

include hθ in

/-! ## The slides -/

end OddMath.QuiverHecke
