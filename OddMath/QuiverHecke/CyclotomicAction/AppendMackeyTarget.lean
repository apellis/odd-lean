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

/-- A `MackeyCosets` from its target-side fields and the source-side data. -/
def MackeyCosets.ofTarget {L₁ L₀ L₀' : Type*} [AddCommGroup L₁] [AddCommGroup L₀]
    [AddCommGroup L₀'] (T : MackeyTarget σ L₀ L₀') (P : L₁ →+ L₀) (ρ : L₁ →+ L₁)
    (short : AddSubgroup L₁) (ℓ : (ℕ →₀ B) →+ L₁) (r₁ : B → L₁ →+ L₁)
    (P_ρ : ∀ z, P (ρ z) = T.Rt (P z)) (ρ_short : ∀ z ∈ short, ρ z ∈ short)
    (P_short : ∀ z ∈ short, ∃ u, P z = T.F u) (cover : ∀ z, ∃ v, z - ℓ v ∈ short)
    (ℓ_short : ∀ v, ℓ v ∈ short → v = 0) (ρ_ℓ : ∀ v, ρ (ℓ v) - ℓ (tShift σ v) ∈ short)
    (ℓ_r : ∀ (b : B) v, ℓ (rsmul b v) - r₁ b (ℓ v) ∈ short)
    (P_r : ∀ (b : B) z, P (r₁ b z) = T.r₀ b (P z)) : MackeyCosets σ L₁ L₀ L₀' where
  P := P
  ρ := ρ
  Rt := T.Rt
  F := T.F
  j := T.j
  X := T.X
  E := T.E
  short := short
  ℓ := ℓ
  r₁ := r₁
  r₀ := T.r₀
  P_ρ := P_ρ
  Rt_F := T.Rt_F
  Rt_j := T.Rt_j
  direct := T.direct
  span := T.span
  ρ_short := ρ_short
  P_short := P_short
  cover := cover
  ℓ_short := ℓ_short
  ρ_ℓ := ρ_ℓ
  ℓ_r := ℓ_r
  P_r := P_r
  F_r := T.F_r
  j_r := T.j_r

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

theorem appendTargetF_add_J (u : appendTensorLeftCoordinates D Sc i n B) (f : ℕ →₀ B) :
    appendTargetF D Sc i n B u + appendTargetJ D Sc i n B f =
      appendTensorCornerEquiv D Sc i n B (u, f) :=
  Subtype.ext (by
    rw [AddSubgroup.coe_add, appendTargetF_coe, appendTargetJ_coe, appendTensorCornerEquiv_apply])

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

/-- The crossing-contraction operator `X = s · appendTensorLeftShift σ`. -/
def appendTargetX :
    appendTensorLeftCoordinates D Sc i n B →+ appendTensorLeftCoordinates D Sc i n B :=
  AddMonoidHom.codRestrict
    (Supercategory.koszulSign (D.parity i) (D.parity i) •
      (appendTensorLeftShift n B σ.toAddMonoidHom).comp
        (appendTensorLeftCoordinates D Sc i n B).subtype)
    _ fun u => zsmul_mem (appendTensorLeftShift_mem D Sc i n B _ hσ u.1 u.2) _

/-- The degree-zero operator `E = -s · appendTensorLeftDegree σ`. -/
def appendTargetE : appendTensorLeftCoordinates D Sc i n B →+ B :=
  -(Supercategory.koszulSign (D.parity i) (D.parity i) •
    (appendTensorLeftDegree D Sc i n B σ.toAddMonoidHom).comp
      (appendTensorLeftCoordinates D Sc i n B).subtype)

theorem appendTargetX_coe (u : appendTensorLeftCoordinates D Sc i n B) :
    ((appendTargetX D Sc i n B σ hσ u : appendTensorLeftCoordinates D Sc i n B) :
        (Fin (n + 1) × ℕ) →₀ B) = Supercategory.koszulSign (D.parity i) (D.parity i) •
      appendTensorLeftShift n B σ.toAddMonoidHom u.1 := rfl

theorem appendTargetE_apply (u : appendTensorLeftCoordinates D Sc i n B) :
    appendTargetE D Sc i n B σ u =
      -(Supercategory.koszulSign (D.parity i) (D.parity i) •
        appendTensorLeftDegree D Sc i n B σ.toAddMonoidHom u.1) := rfl

/-- `R_t F = F X + j E` on the `ψ(1)`-fixed part. -/
theorem appendTargetRt_F (u : appendTensorLeftCoordinates D Sc i n B) :
    appendTargetRt D Sc i n B σ hσ (appendTargetF D Sc i n B u) =
      appendTargetF D Sc i n B (appendTargetX D Sc i n B σ hσ u) +
        appendTargetJ D Sc i n B (single 0 (appendTargetE D Sc i n B σ u)) := by
  apply Subtype.ext
  rw [AddSubgroup.coe_add, appendTargetRt_coe, appendTargetF_coe, appendTargetF_coe,
    appendTargetJ_coe]
  refine (appendTensorRightDot_leftTensor D Sc i n B σ.toAddMonoidHom hσ u.1).trans ?_
  have hX := appendTargetX_coe D Sc i n B σ hσ u
  have hE := appendTargetE_apply D Sc i n B σ u
  refine (sub_eq_add_neg _ _).trans (congrArg₂ (· + ·)
    ((map_zsmul (appendLeftTensor D Sc i n B) _ _).symm.trans
      (congrArg (appendLeftTensor D Sc i n B) hX.symm)) ?_)
  refine ((congrArg (fun x => appendPolyTensor D Sc i n B (single 0 x)) hE).trans ?_).symm
  have hs : (single 0 (-(Supercategory.koszulSign (D.parity i) (D.parity i) •
      appendTensorLeftDegree D Sc i n B σ.toAddMonoidHom u.1)) : ℕ →₀ B) =
      -(Supercategory.koszulSign (D.parity i) (D.parity i) •
        single 0 (appendTensorLeftDegree D Sc i n B σ.toAddMonoidHom u.1)) := by
    rw [Finsupp.single_neg, Finsupp.smul_single]
  exact (congrArg (appendPolyTensor D Sc i n B) hs).trans
    ((map_neg (appendPolyTensor D Sc i n B) _).trans
      (congrArg Neg.neg (map_zsmul (appendPolyTensor D Sc i n B) _ _)))

/-- `R_t j = j t` on the `ψ(1)`-fixed part. -/
theorem appendTargetRt_J (f : ℕ →₀ B) :
    appendTargetRt D Sc i n B σ hσ (appendTargetJ D Sc i n B f) =
      appendTargetJ D Sc i n B (tShift σ f) := by
  apply Subtype.ext
  rw [appendTargetRt_coe, appendTargetJ_coe, appendTargetJ_coe,
    appendTensorRightDot_polyTensor]
  rfl

theorem appendFamilyTensor_map {ι : Type*} (Φ : (ι →₀ Hn D Sc (n + 1)) →+ Hn D Sc (n + 1 + 1))
    (hΦ : ∀ x, Φ x * appendAlgebra D Sc i (n + 1) 1 = Φ x) {N : Type w} [AddCommGroup N]
    [Module (Hn D Sc (n + 1)) N] (g : B →ₗ[Hn D Sc (n + 1)] N) (f : ι →₀ B) :
    InductionAlong.Ind.map g (appendFamilyTensor D Sc i n B Φ hΦ f) =
      appendFamilyTensor D Sc i n N Φ hΦ (Finsupp.mapRange g (map_zero g) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' =>
    rw [map_add, LinearMap.map_add, hf, hf', Finsupp.mapRange_add (map_add g), map_add]
  | single q y =>
    rw [Finsupp.mapRange_single, appendFamilyTensor_single, appendFamilyTensor_single,
      InductionAlong.Ind.map_tmul]

/-! ## Right multiplication on the coefficients -/

variable [IsScalarTower (Hn D Sc (n + 1)) B B]

/-- Right multiplication by `b` as a left `Hn (n+1)`-linear map of `B`. -/
def appendCoefficientMulRight (b : B) : B →ₗ[Hn D Sc (n + 1)] B where
  toFun y := y * b
  map_add' y y' := add_mul y y' b
  map_smul' r y := smul_mul_assoc r y b

/-- The right `B`-action on the `ψ(1)`-fixed part. -/
def appendTensorRightMul (b : B) :
    appendTensorFixed D Sc i n B →+ appendTensorFixed D Sc i n B :=
  AddMonoidHom.codRestrict
    ((InductionAlong.Ind.map (appendCoefficientMulRight D Sc n B b)).toAddMonoidHom.comp
      (appendTensorFixed D Sc i n B).subtype)
    _ fun t => by
      change (appendAlgebra D Sc i (n + 1) 1 : Hn D Sc (n + 1 + 1)) • _ = _
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype,
        LinearMap.toAddMonoidHom_coe]
      rw [← LinearMap.map_smul]
      exact congrArg _ t.2

/-- Right multiplication by `b` on left-crossing coordinates. -/
def appendLeftCoordinatesMulRight (b : B) :
    appendTensorLeftCoordinates D Sc i n B →+ appendTensorLeftCoordinates D Sc i n B :=
  AddMonoidHom.codRestrict
    ((Finsupp.mapRange.addMonoidHom (appendCoefficientMulRight D Sc n B b).toAddMonoidHom).comp
      (appendTensorLeftCoordinates D Sc i n B).subtype)
    _ fun u q => by
      change _ • (u.1 q * b) = u.1 q * b
      rw [← smul_mul_assoc, u.2 q]

theorem appendTensorRightMul_F (b : B) (u : appendTensorLeftCoordinates D Sc i n B) :
    appendTensorRightMul D Sc i n B b (appendTargetF D Sc i n B u) =
      appendTargetF D Sc i n B (appendLeftCoordinatesMulRight D Sc i n B b u) := by
  apply Subtype.ext
  change InductionAlong.Ind.map (appendCoefficientMulRight D Sc n B b)
      ((appendTargetF D Sc i n B u : appendTensorFixed D Sc i n B) : T) = _
  rw [appendTargetF_coe, appendTargetF_coe, appendFamilyTensor_map]
  rfl

theorem appendTensorRightMul_J (b : B) (f : ℕ →₀ B) :
    appendTensorRightMul D Sc i n B b (appendTargetJ D Sc i n B f) =
      appendTargetJ D Sc i n B (rsmul b f) := by
  apply Subtype.ext
  change InductionAlong.Ind.map (appendCoefficientMulRight D Sc n B b)
      ((appendTargetJ D Sc i n B f : appendTensorFixed D Sc i n B) : T) = _
  rw [appendTargetJ_coe, appendTargetJ_coe, appendFamilyTensor_map]
  rfl

/-- **The target side of the append-side Mackey boundary.** -/
def appendMackeyTarget :
    MackeyTarget σ (appendTensorFixed D Sc i n B) (appendTensorLeftCoordinates D Sc i n B) where
  Rt := appendTargetRt D Sc i n B σ hσ
  F := appendTargetF D Sc i n B
  j := appendTargetJ D Sc i n B
  X := appendTargetX D Sc i n B σ hσ
  E := appendTargetE D Sc i n B σ
  r₀ := appendTensorRightMul D Sc i n B
  Rt_F := appendTargetRt_F D Sc i n B σ hσ
  Rt_j := appendTargetRt_J D Sc i n B σ hσ
  direct u f h := by
    have h' := (appendTensorCornerEquiv D Sc i n B).injective
      ((appendTargetF_add_J D Sc i n B u f).symm.trans
        (h.trans (appendTensorCornerEquiv D Sc i n B).map_zero.symm))
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  span y := ⟨((appendTensorCornerEquiv D Sc i n B).symm y).1,
    ((appendTensorCornerEquiv D Sc i n B).symm y).2,
    ((appendTensorCornerEquiv D Sc i n B).apply_symm_apply y).symm.trans
      (appendTargetF_add_J D Sc i n B _ _).symm⟩
  F_r b u := ⟨_, appendTensorRightMul_F D Sc i n B b u⟩
  j_r := appendTensorRightMul_J D Sc i n B

end OddMath.QuiverHecke
