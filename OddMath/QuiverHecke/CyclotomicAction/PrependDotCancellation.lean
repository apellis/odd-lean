/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.PrependCoefficientCoordinates
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerSquareDot

/-!
# Moving-dot square cancellation in prepend coordinates

The degree-two raising and cancellation step of `PrependCoordinates.md`,
used in the repeated-colour QP argument. The square of the existing right
dot is conjugated through the additive balanced coordinates; the finite
support proof permits every right cyclotomic coefficient. No flatness,
monicity, even polynomial support, or coefficient-domain hypothesis is used.
This does not identify an odd linear difference with its square or prove QP.
-/

noncomputable section
open Categorification
namespace OddMath.QuiverHecke

/-- Raising the polynomial exponent by two, with all shuffle indices retained. -/
def prependRaiseTwo {J M : Type*} [AddCommGroup M] :
    (J × ℕ →₀ M) →+ (J × ℕ →₀ M) :=
  Finsupp.embDomain.addMonoidHom
    ⟨fun q => (q.1, q.2 + 2), by intro x y h; cases x; cases y; simp_all⟩

@[simp] theorem prependRaiseTwo_single {J M : Type*} [AddCommGroup M]
    (q : J × ℕ) (y : M) :
    prependRaiseTwo (Finsupp.single q y) = Finsupp.single (q.1, q.2 + 2) y :=
  Finsupp.embDomain_single _ _ _

@[simp] theorem prependRaiseTwo_apply {J M : Type*} [AddCommGroup M]
    (f : J × ℕ →₀ M) (j : J) (m : ℕ) :
    prependRaiseTwo f (j, m + 2) = f (j, m) :=
  Finsupp.embDomain_apply_self _ _ (j, m)

/-- A degree-preserving coefficient cannot cancel the top raised coefficient. -/
theorem prependRaiseTwo_eq_pointwise {J M : Type*} [AddCommGroup M]
    (f : J × ℕ →₀ M) (A : M →+ M)
    (h : ∀ q, prependRaiseTwo f q = A (f q)) : f = 0 := by
  classical
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image Prod.snd
    (Finsupp.support_nonempty_iff.mpr hn)
  have hz : f (q.1, q.2 + 2) = 0 := by
    by_contra hm
    have := hmax _ (Finsupp.mem_support_iff.mpr hm)
    omega
  have he := h (q.1, q.2 + 2)
  rw [prependRaiseTwo_apply, hz, map_zero] at he
  exact (Finsupp.mem_support_iff.mp hq) he

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Right multiplication by the first-dot square raises the prescribed PBW exponent. -/
theorem prependPBWTerm_mul_sq (i : I) {n : ℕ} (j : PrependShuffle n)
    (m : ℕ) (b : Hn D Sc n) :
    prependPBWTerm D Sc i j m b * affineFirstDot D Sc i n ^ 2 =
      prependPBWTerm D Sc i j (m + 2) b := by
  unfold prependPBWTerm
  rw [mul_assoc, affineFirstDot_sq_comm, ← mul_assoc, pow_add]
  simp only [mul_assoc]

/-- The squared corner operator is raising on every PBW representative. -/
theorem targetDotCorner_twice_prepend (i : I) {n : ℕ} (j : PrependShuffle n)
    (m : ℕ) (b : Hn D Sc n) :
    targetDotCorner D Sc i n (targetDotCorner D Sc i n (prependPBWCorner D Sc i j m b)) =
      prependPBWCorner D Sc i j (m + 2) b := by
  apply Subtype.ext
  rw [targetDotCorner_twice_val]
  exact prependPBWTerm_mul_sq D Sc i j m b

variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (r : ℕ)
local notation "M" => (StringDiagrams.SuperBimodule.toSVec (qCoefficient D Sc i β a ha r))
local notation "T" => InductionAlong.Ind M (prependAlgebra D Sc i (r+1) :
  Hn D Sc (r+1) →ₙ+* Hn D Sc (r+1+1))

/-- Conjugation of the prescribed moving-dot square, not a coordinate-defined operator. -/
theorem targetRightDot_sq_prepend (f : (PrependShuffle (r+1) × ℕ) →₀ M) :
    (targetRightDot D Sc i β a ha r ^ 2) (qPrependTensorEquiv D Sc i β a ha r f) =
      qPrependTensorEquiv D Sc i β a ha r (prependRaiseTwo f) := by
  induction f using Finsupp.induction with
  | zero => simp
  | @single_add q y f _ _ hf =>
    rw [map_add, map_add, hf, map_add, map_add]
    congr 1
    change (targetRightDot D Sc i β a ha r ^ 2)
      (prependTensorForward D Sc i (r+1) M (Finsupp.single q y)) = _
    rw [prependTensorForward_single, targetRightDot_sq_tmul,
      targetDotCorner_twice_prepend, prependRaiseTwo_single]
    exact (prependTensorForward_single D Sc i (r+1) M (q.1, q.2+2) y).symm

/-- Inverse balanced coordinates identify the square with degree-two raising. -/
theorem qPrependTensorEquiv_symm_sq (t : T) :
    (qPrependTensorEquiv D Sc i β a ha r).symm ((targetRightDot D Sc i β a ha r ^ 2) t) =
      prependRaiseTwo ((qPrependTensorEquiv D Sc i β a ha r).symm t) := by
  apply (qPrependTensorEquiv D Sc i β a ha r).injective
  rw [AddEquiv.apply_symm_apply, ← targetRightDot_sq_prepend, AddEquiv.apply_symm_apply]

/-- Cancellation against any prescribed right cyclotomic coefficient. -/
theorem targetRightDot_sq_eq_coefficient (c : CyclotomicAlgebra D Sc a r) (t : T)
    (h : (targetRightDot D Sc i β a ha r ^ 2) t = targetRightCoefficient D Sc i β a ha r c t) :
    t = 0 := by
  have he : (qPrependTensorEquiv D Sc i β a ha r).symm t = 0 := by
    apply prependRaiseTwo_eq_pointwise _ (targetCoefficientRight D Sc i β a ha r c).toAddMonoidHom
    intro q
    rw [← qPrependTensorEquiv_symm_sq, h, qPrependTensorEquiv_symm_right]
    rfl
  exact (qPrependTensorEquiv D Sc i β a ha r).symm.injective (he.trans (map_zero _).symm)

/-- The monic difference is injective on the prescribed balanced quotient. -/
theorem targetRightDot_sq_sub_coefficient_injective (c : CyclotomicAlgebra D Sc a r) :
    Function.Injective (fun t : T =>
      (targetRightDot D Sc i β a ha r ^ 2) t - targetRightCoefficient D Sc i β a ha r c t) := by
  intro t s h
  apply sub_eq_zero.mp
  apply targetRightDot_sq_eq_coefficient D Sc i β a ha r c (t - s)
  simp only [map_sub]
  exact sub_eq_sub_iff_sub_eq_sub.mp h

/-- In particular the prescribed last-dot square is an allowed right coefficient. -/
theorem targetRightDot_sq_sub_lastDot_sq_injective :
    Function.Injective (fun t : T =>
      (targetRightDot D Sc i β a ha r ^ 2) t -
        targetRightCoefficient D Sc i β a ha r
          (cyclotomicMk D Sc a r (affineLastDot D Sc i r) ^ 2) t) :=
  targetRightDot_sq_sub_coefficient_injective D Sc i β a ha r _

end OddMath.QuiverHecke
