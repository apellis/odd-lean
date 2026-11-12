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

/-- Elementary tensors as an additive map in the corner variable. -/
def appendTensorCornerHom (y : M) : C →+ T :=
  AddMonoidHom.mk' (fun z => InductionAlong.Ind.tmul z y)
    (fun z z' => InductionAlong.Ind.add_tmul z z' y)

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

@[simp] theorem appendTensorRightDot_tmul (z : C) (y : M) :
    appendTensorRightDot D Sc i n M θ hθ (InductionAlong.Ind.tmul z y) =
      InductionAlong.Ind.tmul (rightDotCorner D Sc i (n + 1) z) (θ y) := rfl

/-- The twisted right dot preserves the `ψ(1)`-fixed part. -/
theorem appendTensorRightDot_mem_fixed (t : T) (ht : t ∈ appendTensorFixed D Sc i n M) :
    appendTensorRightDot D Sc i n M θ hθ t ∈ appendTensorFixed D Sc i n M := by
  change (appendAlgebra D Sc i (n + 1) 1 : Hn D Sc (n + 1 + 1)) • _ = _
  rw [← LinearMap.map_smul]
  exact congrArg _ ht

/-! ## Coordinate maps -/

/-- Shift of the dot exponent of left-crossing coefficients, with the twist `θ`. -/
def appendTensorLeftShift :
    ((Fin (n + 1) × ℕ) →₀ M) →+ ((Fin (n + 1) × ℕ) →₀ M) :=
  (Finsupp.mapDomain.addMonoidHom fun p : Fin (n + 1) × ℕ => (p.1, p.2 + 1)).comp
    (Finsupp.mapRange.addMonoidHom θ)

/-- Shift of the polynomial coefficients, with the twist `θ`. -/
def appendTensorPolyShift : (ℕ →₀ M) →+ (ℕ →₀ M) :=
  (Finsupp.mapDomain.addMonoidHom Nat.succ).comp (Finsupp.mapRange.addMonoidHom θ)

/-- The degree-zero correction `Σ c'_j x^m ψ'(1) θ f_(j,m)`. -/
def appendTensorLeftDegree : ((Fin (n + 1) × ℕ) →₀ M) →+ M :=
  Finsupp.liftAddHom fun p =>
    (DistribSMul.toAddMonoidHom M (appendShuffleElement D Sc i (appendRun n p.1) *
      affineLastDot D Sc i n ^ p.2 * appendAlgebra D Sc i n 1)).comp θ

/-! ## The slides -/

end OddMath.QuiverHecke
