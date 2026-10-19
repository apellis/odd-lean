/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.SerreDeriv
import OddMath.CoveringQuantum.Coefficients
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Lowering operators on the Serre half algebra

The highest-weight action underlying [CHW1] §2.3 uses two skew derivatives.
Here the parameter is that of [BE2], the inverse of the parameter in [CHW1].
The numerator is derived from [CHW1] Proposition 2.2.2(b), rather than the
printed formula in the proof of Lemma 2.3.1.

This file constructs individual operators and their mixed commutation law.
Their positive Serre relations are proved in `VermaSerre`. Neither file asserts
faithfulness or triangular decomposition.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot

open PreF

variable {k I : Type*} [CommRing k] [DecidableEq I]
variable (C : SuperCartanDatum I) (q : kˣ) (π : k)

/-- The parity character associated with a simple generator. -/
def parityTwist (i : I) : PreF k I →ₐ[k] PreF k I :=
  diagTwist fun j ↦ π ^ (C.parity i * C.parity j).val

/-- The inverse quantum weight character. -/
def weightTwist (i : I) : PreF k I →ₐ[k] PreF k I :=
  diagTwist fun j ↦ ((q ^ C.dot i j : kˣ) : k)

/-- The numerator of the highest-weight lowering operator. For a highest
weight pairing `n`, the two scalars are `qᵢ^n` and `πᵢ^n qᵢ^(-n)`. -/
def lowerNumerator (i : I) (a b : k) : Module.End k (PreF k I) :=
  a • ((parityTwist C π i).toLinearMap.comp (rDeriv (C.chi q π) i)) -
    b • ((weightTwist C q i).toLinearMap.comp (lDeriv (C.chi q π) i))

@[simp] theorem lowerNumerator_one (i : I) (a b : k) :
    lowerNumerator C q π i a b 1 = 0 := by
  simp [lowerNumerator]

@[simp] theorem lowerNumerator_θ (i j : I) (a b : k) :
    lowerNumerator C q π i a b (θ k j) = if i = j then (a - b) • (1 : PreF k I) else 0 := by
  simp only [lowerNumerator, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, rDeriv_θ, lDeriv_θ]
  split_ifs <;> simp [sub_smul]

omit [DecidableEq I] in
private theorem weightTwist_twist (i : I) (x : PreF k I) :
    weightTwist C q i (twist (C.chi q π) i x) = parityTwist C π i x := by
  rw [weightTwist, twist, diagTwist_diagTwist]
  have hc : (fun j ↦ ((q ^ C.dot i j : kˣ) : k)) * (fun j ↦ C.chi q π i j) =
      (fun j ↦ π ^ (C.parity i * C.parity j).val) := by
    funext j
    simp only [Pi.mul_apply, SuperCartanDatum.chi_apply, ← mul_assoc,
      ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, one_mul]
  rw [hc]
  rfl

/-- The free lowering numerator has the required mixed supercommutator.
The diagonal terms become a quantum integer on each weight space. -/
theorem lowerNumerator_θ_mul (i j : I) (a b : k) (x : PreF k I) :
    lowerNumerator C q π i a b (θ k j * x) =
      π ^ (C.parity i * C.parity j).val • (θ k j * lowerNumerator C q π i a b x) +
        if i = j then
          a • parityTwist C π i (twist (C.chi q π) i x) - b • weightTwist C q i x
        else 0 := by
  simp only [lowerNumerator, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, rDeriv_mul, lDeriv_mul,
    rDeriv_θ, lDeriv_θ, map_add, map_mul, map_smul, twist_θ]
  have hscale : C.chi q π i j * ((q ^ C.dot i j : kˣ) : k) =
      π ^ (C.parity i * C.parity j).val := by
    simp only [SuperCartanDatum.chi_apply, mul_right_comm, ← Units.val_mul,
      ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_mul]
  simp only [parityTwist, weightTwist, diagTwist_θ, smul_mul_assoc,
    smul_smul, hscale]
  split_ifs <;> simp only [map_one, map_zero, one_mul, zero_mul,
    zero_add, add_zero, smul_add, smul_smul]
  all_goals simp only [mul_sub, mul_smul_comm]
  all_goals module

/-- The denominator of the mixed relation in the [BE2] convention. -/
def vermaDenominator (i : I) : k := (C.qi q i : k) - C.pii π i * ((C.qi q i)⁻¹ : kˣ)

/-- The corrected highest-weight lowering operator on the free half algebra.
The integer `n` is the simple-coroot pairing of the highest weight. -/
def lowerFree (i : I) (n : ℤ) : Module.End k (PreF k I) :=
  Ring.inverse (vermaDenominator C q π i) •
    lowerNumerator C q π i ((C.qi q i ^ n : kˣ) : k)
      (C.pii π i ^ n.natAbs * ((C.qi q i ^ (-n) : kˣ) : k))

@[simp] theorem lowerFree_one (i : I) (n : ℤ) : lowerFree C q π i n 1 = 0 := by
  simp [lowerFree]

/-- The defining commutator on the highest-weight vector. -/
theorem lowerFree_θ_self (hπ : π ^ 2 = 1) (i : I) (n : ℤ)
    (hden : IsUnit (vermaDenominator C q π i)) :
    lowerFree C q π i n (θ k i) = qpInt (C.qi q i) (C.pii π i) n • (1 : PreF k I) := by
  simp only [lowerFree, LinearMap.smul_apply, lowerNumerator_θ, ↓reduceIte, smul_smul]
  congr 1
  have h : vermaDenominator C q π i * qpInt (C.qi q i) (C.pii π i) n =
      ((C.qi q i ^ n : kˣ) : k) - C.pii π i ^ n.natAbs * ((C.qi q i ^ (-n) : kˣ) : k) := by
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · simpa only [vermaDenominator, qpInt_ofNat, zpow_natCast, zpow_neg,
        ← inv_pow, Units.val_pow_eq_pow_val, Int.natAbs_natCast] using
        qpNat_mul_sub (q := C.qi q i) (π := C.pii π i) m
    · simpa only [vermaDenominator, zpow_natCast, zpow_neg, neg_neg,
        ← inv_pow, Units.val_pow_eq_pow_val, Int.natAbs_neg, Int.natAbs_natCast] using
        qpInt_neg_mul_sub (q := C.qi q i) (C.pii_sq π hπ i) m
  rw [← h, ← mul_assoc, Ring.inverse_mul_cancel _ hden, one_mul]

namespace GenericVerma

open Coefficients

variable {I : Type*} [DecidableEq I] (C : SuperCartanDatum I)

omit [DecidableEq I] in
/-- The denominator is a unit in the generic covering ring, without treating
that ring as a field. -/
theorem vermaDenominator_isUnit (i : I) :
    IsUnit (vermaDenominator C Coefficients.q pi i) := by
  have hp := C.pii_sq pi pi_sq i
  have hu : IsUnit (C.pii pi i) := isUnit_of_mul_isUnit_left
    (show IsUnit (C.pii pi i * C.pii pi i) by rw [← pow_two, hp]; exact isUnit_one)
  have hfactor :
      (-(C.pii pi i) * (((C.qi Coefficients.q i)⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring)) *
        (1 - C.pii pi i * ((C.qi Coefficients.q i : Coefficients.Ringˣ) : Coefficients.Ring) ^ 2) =
      vermaDenominator C Coefficients.q pi i := by
    calc
      _ = ((C.qi Coefficients.q i : Coefficients.Ringˣ) : Coefficients.Ring) * C.pii pi i ^ 2 *
          (((C.qi Coefficients.q i : Coefficients.Ringˣ) : Coefficients.Ring) *
            (((C.qi Coefficients.q i)⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring)) -
          C.pii pi i * (((C.qi Coefficients.q i)⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring) := by
            ring
      _ = _ := by simp only [hp, Units.mul_inv, mul_one, vermaDenominator]
  rw [← hfactor]
  exact (hu.neg.mul (C.qi Coefficients.q i)⁻¹.isUnit).mul (denominator_isUnit C i)

/-- Over the generic covering ring, the right skew derivative preserves the
Serre ideal directly, without identifying it with a form radical. -/
theorem rDeriv_mem_serreIdeal (i : I) {x : PreF Coefficients.Ring I}
    (hx : x ∈ C.serreIdeal Coefficients.q pi) :
    rDeriv (C.chi Coefficients.q pi) i x ∈ C.serreIdeal Coefficients.q pi := by
  exact C.rDeriv_mem_serreIdeal Coefficients.q pi pi_sq i hx

theorem lDeriv_mem_serreIdeal (i : I) {x : PreF Coefficients.Ring I}
    (hx : x ∈ C.serreIdeal Coefficients.q pi) :
    lDeriv (C.chi Coefficients.q pi) i x ∈ C.serreIdeal Coefficients.q pi := by
  exact C.lDeriv_mem_serreIdeal Coefficients.q pi pi_sq i hx

/-- The lowering operator preserves the full two-sided Serre ideal, not merely
its displayed generators. -/
theorem lowerFree_mem_serreIdeal (i : I) (n : ℤ) {x : PreF Coefficients.Ring I}
    (hx : x ∈ C.serreIdeal Coefficients.q pi) :
    lowerFree C Coefficients.q pi i n x ∈ C.serreIdeal Coefficients.q pi := by
  apply (C.mem_serreIdeal Coefficients.q pi _).mpr
  have hr := C.diagTwist_mem_serreIdeal Coefficients.q pi
    (fun j ↦ pi ^ (C.parity i * C.parity j).val) (rDeriv_mem_serreIdeal C i hx)
  have hl := C.diagTwist_mem_serreIdeal Coefficients.q pi
    (fun j ↦ ((Coefficients.q ^ C.dot i j : Coefficients.Ringˣ) : Coefficients.Ring))
    (lDeriv_mem_serreIdeal C i hx)
  rw [C.mem_serreIdeal] at hr hl
  simp only [lowerFree, lowerNumerator, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_smul, map_sub,
    parityTwist, weightTwist, hr, hl, smul_zero, sub_zero]

private abbrev halfProjection : PreF Coefficients.Ring I →ₗ[Coefficients.Ring]
    C.serreF Coefficients.q pi := (C.toSerreF Coefficients.q pi).toLinearMap

omit [DecidableEq I] in
private theorem halfProjection_surjective : Function.Surjective (halfProjection C) :=
  C.toSerreF_surjective Coefficients.q pi

/-- The lowering operator on the actual Serre half algebra. Its positive
Serre relations are established in `VermaSerre`. -/
def lower (i : I) (n : ℤ) : Module.End Coefficients.Ring (C.serreF Coefficients.q pi) :=
  let p := halfProjection C
  let f := p.comp (lowerFree C Coefficients.q pi i n)
  ((LinearMap.ker p).liftQ f (by
    intro x hx
    change C.toSerreF Coefficients.q pi (lowerFree C Coefficients.q pi i n x) = 0
    apply (C.mem_serreIdeal Coefficients.q pi _).mp
    apply lowerFree_mem_serreIdeal C i n
    exact (C.mem_serreIdeal Coefficients.q pi x).mpr hx)).comp
    (p.quotKerEquivOfSurjective (halfProjection_surjective C)).symm.toLinearMap

@[simp] theorem lower_mk (i : I) (n : ℤ) (x : PreF Coefficients.Ring I) :
    lower C i n (C.toSerreF Coefficients.q pi x) =
      C.toSerreF Coefficients.q pi (lowerFree C Coefficients.q pi i n x) := by
  simp only [lower, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change (LinearMap.ker (halfProjection C)).liftQ _ _
    (((halfProjection C).quotKerEquivOfSurjective _).symm (halfProjection C x)) = _
  exact congrArg ((LinearMap.ker (halfProjection C)).liftQ _ _)
    ((halfProjection C).quotKerEquivOfSurjective_symm_apply (halfProjection_surjective C) x)

/-- On the actual generic half algebra, lowering a simple generator at weight
pairing `n` gives the required quantum integer times the vacuum. -/
theorem lower_θ_self (i : I) (n : ℤ) :
    lower C i n (C.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
      qpInt (C.qi Coefficients.q i) (C.pii pi i) n • (1 : C.serreF Coefficients.q pi) := by
  rw [lower_mk, lowerFree_θ_self C Coefficients.q pi pi_sq i n
    (vermaDenominator_isUnit C i), map_smul, map_one]

@[simp] theorem lower_one (i : I) (n : ℤ) : lower C i n 1 = 0 := by
  rw [← map_one (C.toSerreF Coefficients.q pi), lower_mk, lowerFree_one, map_zero]

end GenericVerma

end OddMath.CoveringQuantum.UDot
