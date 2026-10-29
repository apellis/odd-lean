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

theorem appendTensor_zsmul_tmul (c : ℤ) (z : C) (y : M) :
    InductionAlong.Ind.tmul (c • z) y = c • InductionAlong.Ind.tmul z y :=
  map_zsmul (appendTensorCornerHom D Sc i n M y) c z

theorem appendTensor_sub_tmul (z z' : C) (y : M) :
    InductionAlong.Ind.tmul (z - z') y =
      InductionAlong.Ind.tmul z y - InductionAlong.Ind.tmul z' y :=
  (appendTensorCornerHom D Sc i n M y).map_sub z z'

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

include hθ in
/-- `θ` preserves left-crossing coordinates in `ψ'(1) M`. -/
theorem appendTensorLeftShift_mem (f : (Fin (n + 1) × ℕ) →₀ M)
    (hf : f ∈ appendTensorLeftCoordinates D Sc i n M) :
    appendTensorLeftShift n M θ f ∈ appendTensorLeftCoordinates D Sc i n M := by
  have hfix : ∀ y : M, (appendAlgebra D Sc i n 1 : Hn D Sc (n + 1)) • y = y →
      (appendAlgebra D Sc i n 1 : Hn D Sc (n + 1)) • θ y = θ y := by
    intro y hy
    rw [← homMatrixTwist_appendAlgebra_one D Sc i n (D.parity i), ← hθ, hy]
  have hinj : Function.Injective fun p : Fin (n + 1) × ℕ => (p.1, p.2 + 1) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    rw [h.1, Nat.add_right_cancel h.2]
  intro p
  simp only [appendTensorLeftShift, AddMonoidHom.comp_apply,
    Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapRange.addMonoidHom_apply]
  by_cases hp : p ∈ Set.range fun p : Fin (n + 1) × ℕ => (p.1, p.2 + 1)
  · obtain ⟨q, rfl⟩ := hp
    rw [Finsupp.mapDomain_apply_of_injective hinj, Finsupp.mapRange_apply]
    exact hfix _ (hf q)
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hp, smul_zero]

/-! ## The slides -/

/-- `R_t j = j t`: the twisted right dot on polynomial tensors. -/
theorem appendTensorRightDot_polyTensor (g : ℕ →₀ M) :
    appendTensorRightDot D Sc i n M θ hθ (appendPolyTensor D Sc i n M g) =
      appendPolyTensor D Sc i n M (appendTensorPolyShift M θ g) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, LinearMap.map_add, hf, hg, map_add, map_add]
  | single m y =>
    simp only [appendTensorPolyShift, AddMonoidHom.comp_apply,
      Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
      Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single,
      appendFamilyTensor_single, appendTensorRightDot_tmul]
    congr 1
    apply Subtype.ext
    change appendPolySum D Sc i n (Finsupp.single m 1) * affineLastDot D Sc i (n + 1) =
      appendPolySum D Sc i n (Finsupp.single (m + 1) 1)
    rw [appendPolySum_mul_lastDot]
    simp [appendPolyShift]

/-- The corner form of `R_t F = F X + j E` on a single left-crossing generator. -/
theorem rightDotCorner_appendLeftSum_single (q : Fin (n + 1) × ℕ) :
    rightDotCorner D Sc i (n + 1)
        (appendFamilyCorner D Sc i n (appendLeftSum D Sc i n)
          (appendLeftSum_mul_appendOne D Sc i n) (Finsupp.single q 1)) =
      Supercategory.koszulSign (D.parity i) (D.parity i) •
          appendFamilyCorner D Sc i n (appendLeftSum D Sc i n)
            (appendLeftSum_mul_appendOne D Sc i n) (Finsupp.single (q.1, q.2 + 1) 1) -
        Supercategory.koszulSign (D.parity i) (D.parity i) •
          op (appendShuffleElement D Sc i (appendRun n q.1) *
              affineLastDot D Sc i n ^ q.2 * appendAlgebra D Sc i n 1) •
            appendFamilyCorner D Sc i n (appendPolySum D Sc i n)
              (appendPolySum_mul_appendOne D Sc i n) (Finsupp.single 0 1) := by
  apply Subtype.ext
  change appendLeftSum D Sc i n (Finsupp.single q 1) * affineLastDot D Sc i (n + 1) =
    Supercategory.koszulSign (D.parity i) (D.parity i) •
        appendLeftSum D Sc i n (Finsupp.single (q.1, q.2 + 1) 1) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (appendPolySum D Sc i n (Finsupp.single 0 1) *
          appendAlgebra D Sc i (n + 1) (appendShuffleElement D Sc i (appendRun n q.1) *
            affineLastDot D Sc i n ^ q.2 * appendAlgebra D Sc i n 1))
  rw [appendLeftSum_mul_lastDot, ← appendPolySum_single_right]
  simp [appendLeftShift, appendLeftDegree]

/-- `R_t F = F X + j E`: the twisted right dot on left-crossing tensors, with
`X = s · appendTensorLeftShift θ` and `E = -s · appendTensorLeftDegree θ`. -/
theorem appendTensorRightDot_leftTensor (f : (Fin (n + 1) × ℕ) →₀ M) :
    appendTensorRightDot D Sc i n M θ hθ (appendLeftTensor D Sc i n M f) =
      Supercategory.koszulSign (D.parity i) (D.parity i) •
          appendLeftTensor D Sc i n M (appendTensorLeftShift n M θ f) -
        Supercategory.koszulSign (D.parity i) (D.parity i) •
          appendPolyTensor D Sc i n M
            (Finsupp.single 0 (appendTensorLeftDegree D Sc i n M θ f)) := by
  suffices key : (appendTensorRightDot D Sc i n M θ hθ).toAddMonoidHom.comp
      (appendLeftTensor D Sc i n M) =
    Supercategory.koszulSign (D.parity i) (D.parity i) •
        (appendLeftTensor D Sc i n M).comp (appendTensorLeftShift n M θ) -
      Supercategory.koszulSign (D.parity i) (D.parity i) •
        (appendPolyTensor D Sc i n M).comp
          ((Finsupp.singleAddHom 0).comp (appendTensorLeftDegree D Sc i n M θ)) from
    DFunLike.congr_fun key f
  refine Finsupp.addHom_ext fun q y => ?_
  have hL := appendFamilyTensor_single D Sc i n M (appendLeftSum D Sc i n)
    (appendLeftSum_mul_appendOne D Sc i n) q y
  have hS : appendTensorLeftShift n M θ (Finsupp.single q y) =
      Finsupp.single (q.1, q.2 + 1) (θ y) := by
    simp [appendTensorLeftShift]
  have hD : appendTensorLeftDegree D Sc i n M θ (Finsupp.single q y) =
      (appendShuffleElement D Sc i (appendRun n q.1) * affineLastDot D Sc i n ^ q.2 *
        appendAlgebra D Sc i n 1) • θ y := by
    simp [appendTensorLeftDegree]
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply,
    LinearMap.toAddMonoidHom_coe, Finsupp.singleAddHom_apply, hS, hD, hL]
  rw [appendTensorRightDot_tmul, rightDotCorner_appendLeftSum_single, appendTensor_sub_tmul,
    appendTensor_zsmul_tmul, appendTensor_zsmul_tmul, InductionAlong.Ind.op_smul_tmul,
    appendFamilyTensor_single, appendFamilyTensor_single]

end OddMath.QuiverHecke
