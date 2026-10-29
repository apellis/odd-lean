/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentCosets

/-!
# Corrected-rho coordinates of the moving source coset

The ordinary-polynomial specialization of `DeformedMackeyBoundary.md` (6)–(7).
The prescribed full moving shuffle is normalized by the content sign in each
input-dot degree. This supplies compatible lifts for the source of the Mackey
boundary, without assuming an identification of the short image with crossings.
The content corner has old height `n + 1`; `n = 0` is not old height zero.
No restriction on the cyclotomic cutoff is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Categorification.InductionAlong Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
open SKM (zsign)

/-- Degreewise sign normalization, leaving the right coefficient in its original order. -/
def movingSignNormalize {M : Type*} [AddCommGroup M] (p : ZMod 2) :
    (ℕ →₀ M) →+ (ℕ →₀ M) where
  toFun f := Finsupp.onFinset f.support (fun m => (zsign ℤ p) ^ m • f m)
    (fun m h => Finsupp.mem_support_iff.mpr (fun hz => h (by rw [hz, smul_zero])))
  map_zero' := by ext m; simp
  map_add' f g := by ext m; simp [smul_add]

@[simp] theorem movingSignNormalize_apply {M : Type*} [AddCommGroup M]
    (p : ZMod 2) (f : ℕ →₀ M) (m : ℕ) :
    movingSignNormalize p f m = (zsign ℤ p) ^ m • f m := rfl

@[simp] theorem movingSignNormalize_single {M : Type*} [AddCommGroup M]
    (p : ZMod 2) (m : ℕ) (b : M) :
    movingSignNormalize p (Finsupp.single m b) =
      Finsupp.single m ((zsign ℤ p) ^ m • b) := by
  ext l
  by_cases h : m = l
  · subst l; simp
  · simp [h]

/-- The sign correction is its own inverse, including degree zero. -/
@[simp] theorem movingSignNormalize_twice {M : Type*} [AddCommGroup M]
    (p : ZMod 2) (f : ℕ →₀ M) :
    movingSignNormalize p (movingSignNormalize p f) = f := by
  ext m
  simp only [movingSignNormalize_apply, smul_smul, ← mul_pow,
    ← zsign_add_eq, CharTwo.add_self_eq_zero]
  simp [zsign]

/-- Degree raising with the coefficient parity retained. -/
def movingParityRaise {M : Type*} [AddCommGroup M] (θ : M →+ M) :
    (ℕ →₀ M) →+ (ℕ →₀ M) :=
  (Finsupp.embDomain.addMonoidHom ⟨Nat.succ, Nat.succ_injective⟩).comp
    (Finsupp.mapRange.addMonoidHom θ)

@[simp] theorem movingParityRaise_single {M : Type*} [AddCommGroup M]
    (θ : M →+ M) (m : ℕ) (b : M) :
    movingParityRaise θ (Finsupp.single m b) = Finsupp.single (m + 1) (θ b) := by
  simp [movingParityRaise]

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Multiplication by the input dot raises the unit-coefficient PBW term. -/
theorem prependPBWTerm_one_mul_firstDot (i : I) {r : ℕ} (u : PrependShuffle r)
    (m : ℕ) :
    prependPBWTerm D Sc i u m 1 * affineFirstDot D Sc i r =
      prependPBWTerm D Sc i u (m + 1) 1 := by
  unfold prependPBWTerm
  rw [mul_assoc, affineFirstDot_twist_comm, homMatrixTwist_one,
    affineFirstDot_mul_prepend_one, pow_succ]
  simp only [mul_assoc, affineFirstDot_mul_prepend_one]

variable (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I) (i : I)
local notation "B" => CyclotomicContentCorner D Sc a n β
local notation "eps" => appendContentParity D a β i
local notation "p" => D.parity i * Multiset.sum (Multiset.map D.parity β)
local notation "coord" => prependTwistCoordinates D Sc i n eps B

/-- The normalized lift is the full moving PBW lift with its exact degreewise sign. -/
def appendContentRhoLift : (ℕ →₀ B) →+ appendContentSource D Sc a n β i :=
  (appendContentLongLift D Sc a n β i).comp (movingSignNormalize p)

/-- Extraction in the corrected-rho normalization. -/
def appendContentRhoExtract : appendContentSource D Sc a n β i →+ (ℕ →₀ B) :=
  (movingSignNormalize p).comp (appendContentLongExtract D Sc a n β i)

@[simp] theorem appendContentRhoLift_single (m : ℕ) (b : B) :
    (appendContentRhoLift D Sc a n β i (Finsupp.single m b)).1 =
      coord (Finsupp.single (longPrependShuffle (n + 1), m) ((zsign ℤ p) ^ m • b)) := by
  simp only [appendContentRhoLift, AddMonoidHom.comp_apply, movingSignNormalize_single,
    appendContentLongLift_single]

@[simp] theorem appendContentRhoExtract_lift (f : ℕ →₀ B) :
    appendContentRhoExtract D Sc a n β i (appendContentRhoLift D Sc a n β i f) = f := by
  simp [appendContentRhoExtract, appendContentRhoLift, appendContentLongExtract_lift]

/-- The corrected normalization has exactly the already constructed short kernel. -/
theorem appendContentRhoExtract_eq_zero_iff (z : appendContentSource D Sc a n β i) :
    appendContentRhoExtract D Sc a n β i z = 0 ↔ z ∈ appendContentShort D Sc a n β i := by
  change movingSignNormalize p (appendContentLongExtract D Sc a n β i z) = 0 ↔
    appendContentLongExtract D Sc a n β i z = 0
  constructor
  · intro h
    have := congrArg (movingSignNormalize p) h
    simpa using this
  · intro h; rw [h, map_zero]

/-- The normalized prescribed lifts cover the original source modulo short tensors. -/
theorem appendContentRho_cover (z : appendContentSource D Sc a n β i) :
    z - appendContentRhoLift D Sc a n β i (appendContentRhoExtract D Sc a n β i z) ∈
      appendContentShort D Sc a n β i := by
  rw [← appendContentRhoExtract_eq_zero_iff, map_sub, appendContentRhoExtract_lift, sub_self]

variable (ha : CyclotomicPolynomialParity D a)
local notation "θ" => RingHom.toAddMonoidHom (contentCornerParity D Sc a n β i ha)

/-- On every shuffle the actual source dot raises the input degree and twists the coefficient. -/
theorem appendSourceDot_coordinates_single (u : PrependShuffle (n + 1)) (m : ℕ) (b : B) :
    appendSourceDot D Sc i n eps θ (contentCornerParity_smul D Sc a n β i ha)
      (coord (Finsupp.single (u, m) b)) =
      coord (Finsupp.single (u, m + 1) (θ b)) := by
  rw [prependTwistCoordinates_single, appendSourceDot_tmul, prependTwistCoordinates_single]
  congr 1
  apply Subtype.ext
  exact prependPBWTerm_one_mul_firstDot D Sc i u m

/-- The corrected rho acts on the normalized monomials with no residual sign. -/
theorem appendContentRho_lift_single (m : ℕ) (b : B) :
    appendContentRho D Sc a n β i ha
      (appendContentRhoLift D Sc a n β i (Finsupp.single m b)) =
      appendContentRhoLift D Sc a n β i (Finsupp.single (m + 1) (θ b)) := by
  apply Subtype.ext
  change zsign ℤ (appendSourceSign D a i eps) •
    appendSourceDot D Sc i n eps θ (contentCornerParity_smul D Sc a n β i ha)
      (appendContentRhoLift D Sc a n β i (Finsupp.single m b)).1 = _
  rw [appendContentRhoLift_single, appendSourceDot_coordinates_single,
    appendContentRhoLift_single, appendSourceSign_contentParity, map_zsmul,
    ← map_zsmul, Finsupp.smul_single, smul_smul, pow_succ']

/-- The prescribed finite lift intertwines corrected rho with parity-twisted raising. -/
theorem appendContentRho_lift (f : ℕ →₀ B) :
    appendContentRho D Sc a n β i ha (appendContentRhoLift D Sc a n β i f) =
      appendContentRhoLift D Sc a n β i (movingParityRaise θ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b => rw [movingParityRaise_single, appendContentRho_lift_single]

/-- The source dot has no constant input-dot coordinate. -/
theorem appendSourceDot_coordinate_zero
    (f : (PrependShuffle (n + 1) × ℕ) →₀ B) (u : PrependShuffle (n + 1)) :
    (coord).symm (appendSourceDot D Sc i n eps θ
      (contentCornerParity_smul D Sc a n β i ha) (coord f)) (u, 0) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, add_zero]
  | single q b =>
    rw [appendSourceDot_coordinates_single, AddEquiv.symm_apply_apply]
    simp

/-- Successor coordinates of the source dot retain the coefficient parity. -/
theorem appendSourceDot_coordinate_succ
    (f : (PrependShuffle (n + 1) × ℕ) →₀ B) (u : PrependShuffle (n + 1)) (m : ℕ) :
    (coord).symm (appendSourceDot D Sc i n eps θ
      (contentCornerParity_smul D Sc a n β i ha) (coord f)) (u, m + 1) = θ (f (u, m)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]
  | single q b =>
    rw [appendSourceDot_coordinates_single, AddEquiv.symm_apply_apply]
    by_cases h : q = (u, m)
    · subst q; simp
    · have h' : (q.1, q.2 + 1) ≠ (u, m + 1) := by
        intro he
        apply h
        apply Prod.ext
        · have he₁ := congrArg Prod.fst he
          exact he₁
        · have he₂ := congrArg Prod.snd he
          exact Nat.add_right_cancel he₂
      simp [h, h']

/-- The parity raising operator has zero constant term. -/
@[simp] theorem movingParityRaise_zero {M : Type*} [AddCommGroup M]
    (τ : M →+ M) (f : ℕ →₀ M) : movingParityRaise τ f 0 = 0 := by
  exact Finsupp.embDomain_of_notMem_range _ _ _ (by simp)

/-- Its successor coefficient is exactly the parity of the previous coefficient. -/
@[simp] theorem movingParityRaise_succ {M : Type*} [AddCommGroup M]
    (τ : M →+ M) (f : ℕ →₀ M) (m : ℕ) :
    movingParityRaise τ f (m + 1) = τ (f m) :=
  Finsupp.embDomain_apply_self _ _ m

/-- Extraction intertwines the prescribed corrected rho on the entire source, not only lifts. -/
theorem appendContentRhoExtract_rho (z : appendContentSource D Sc a n β i) :
    appendContentRhoExtract D Sc a n β i (appendContentRho D Sc a n β i ha z) =
      movingParityRaise θ (appendContentRhoExtract D Sc a n β i z) := by
  have hz := (coord).apply_symm_apply z.1
  ext m
  change (zsign ℤ p) ^ m • (coord).symm
    (zsign ℤ (appendSourceSign D a i eps) •
      appendSourceDot D Sc i n eps θ (contentCornerParity_smul D Sc a n β i ha) z.1)
      (longPrependShuffle (n + 1), m) = _
  rw [map_zsmul, Finsupp.smul_apply, appendSourceSign_contentParity]
  rw [← hz]
  cases m with
  | zero => rw [appendSourceDot_coordinate_zero]; simp
  | succ m =>
    rw [appendSourceDot_coordinate_succ, movingParityRaise_succ]
    change (zsign ℤ p) ^ (m + 1) • ((zsign ℤ p) • θ (_)) = θ ((zsign ℤ p) ^ m • _)
    rw [map_zsmul, smul_smul, pow_succ, mul_assoc, ← zsign_add_eq,
      CharTwo.add_self_eq_zero]
    simp [zsign, appendContentLongExtract_apply]

/-- Consequently the already specified short subgroup is rho-stable. -/
theorem appendContentShort_rho (z : appendContentSource D Sc a n β i)
    (hz : z ∈ appendContentShort D Sc a n β i) :
    appendContentRho D Sc a n β i ha z ∈ appendContentShort D Sc a n β i := by
  rw [← appendContentRhoExtract_eq_zero_iff] at hz ⊢
  rw [appendContentRhoExtract_rho, hz, map_zero]

/-- The normalized lift is right-linear for the unchanged coefficient action. -/
theorem appendContentRhoLift_rightMul (b : B) (f : ℕ →₀ B) :
    appendContentRhoLift D Sc a n β i (CyclotomicAction.BoundaryPolynomial.rsmul b f) =
      appendContentSourceRightMul D Sc a n β i b (appendContentRhoLift D Sc a n β i f) := by
  change appendContentLongLift D Sc a n β i (movingSignNormalize p
    (CyclotomicAction.BoundaryPolynomial.rsmul b f)) = _
  have h : movingSignNormalize p (CyclotomicAction.BoundaryPolynomial.rsmul b f) =
      CyclotomicAction.BoundaryPolynomial.rsmul b (movingSignNormalize p f) := by
    ext m
    exact (smul_mul_assoc _ _ _).symm
  rw [h, appendContentLongLift_rightMul]
  rfl

/-- The prescribed P carries the normalized recurrence to the target right-dot recurrence. -/
theorem appendContentP_rhoLift (f : ℕ →₀ B) :
    appendContentP D Sc a n β i ha
      (appendContentRhoLift D Sc a n β i (movingParityRaise θ f)) =
      (appendContentMackeyTarget D Sc a n β i ha).Rt
        (appendContentP D Sc a n β i ha (appendContentRhoLift D Sc a n β i f)) := by
  exact (congrArg (appendContentP D Sc a n β i ha)
    (appendContentRho_lift D Sc a n β i ha f).symm).trans
      (appendContentP_rho D Sc a n β i ha _)

end OddMath.QuiverHecke
