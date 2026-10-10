import OddMath.CoveringQuantum.UDot.VermaWeights

/-!
# The homogeneous mixed relation

The corrected lowering operator has quantum-integer supercommutator on each
weight projection. This uses the Cartan parity axiom and a unit denominator,
not separation of toral characters.
-/
noncomputable section
namespace OddMath.CoveringQuantum.UDot
open PreF
variable {k I X : Type*} [CommRing k] [AddCommGroup X]
variable (D : RootDatum I X) (q : kˣ) (π : k)

private theorem pii_pow_sub_cartan (hπ : π ^ 2 = 1) (i j : I) (n : ℤ) :
    D.pii π i ^ (n - D.a i j).natAbs = D.pii π i ^ n.natAbs := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (D.parity i) with hp | hp
  · simp [SuperCartanDatum.pii, hp]
  · have he := D.even_of_odd i j hp
    obtain ⟨m, hm⟩ := he
    have hn := Int.natAbs_eq n
    have ha := Int.natAbs_eq (n - D.a i j)
    have heq : (n - D.a i j).natAbs % 2 = n.natAbs % 2 := by
      rcases hn with hn | hn <;> rcases ha with ha | ha <;> omega
    rw [← Nat.div_add_mod (n - D.a i j).natAbs 2,
      ← Nat.div_add_mod n.natAbs 2, pow_add, pow_add, pow_mul, pow_mul,
      D.pii_sq π hπ i, one_pow, one_pow, one_mul, one_mul, heq]

private theorem pii_pow_sub_word (hπ : π ^ 2 = 1) (i : I) (n : ℤ) (w : List I) :
    D.pii π i ^ (n - D.h i (halfWeight D true (wordWeight w))).natAbs =
      D.pii π i ^ n.natAbs := by
  induction w generalizing n with
  | nil => simp
  | cons j w ih =>
    simp only [wordWeight_cons, halfWeight_add, halfWeight_single,
      show halfRoot D true j = D.α j from rfl, map_add, D.h_α, ← sub_sub]
    rw [ih, pii_pow_sub_cartan D π hπ]

private theorem weightTwist_monomial (i : I) (w : List I) :
    weightTwist D.toSuperCartanDatum q i (monomial k w) =
      ((D.qi q i ^ D.h i (halfWeight D true (wordWeight w)) : kˣ) : k) • monomial k w := by
  induction w with
  | nil => simp
  | cons j w ih =>
    rw [monomial_cons, map_mul, ih]
    simp only [weightTwist, diagTwist_θ, wordWeight_cons, halfWeight_add, halfWeight_single,
      show halfRoot D true j = D.α j from rfl, map_add, D.h_α, zpow_add, Units.val_mul,
      smul_mul_smul_comm]
    congr 2
    simp only [SuperCartanDatum.qi, SuperCartanDatum.dot, zpow_mul, zpow_natCast]

private theorem parity_twist_twist' (hπ : π ^ 2 = 1) (i : I) (x : PreF k I) :
    parityTwist D.toSuperCartanDatum π i (twist (D.chi q π) i x) =
      weightTwist D.toSuperCartanDatum q⁻¹ i x := by
  rw [parityTwist, twist, diagTwist_diagTwist]
  have hc : (fun j ↦ π ^ (D.parity i * D.parity j).val) * (fun j ↦ D.chi q π i j) =
      (fun j ↦ ((q⁻¹ ^ D.dot i j : kˣ) : k)) := by
    funext j
    simp only [Pi.mul_apply, SuperCartanDatum.chi_apply, inv_zpow, ← zpow_neg]
    have hp : π ^ (D.parity i * D.parity j).val * π ^ (D.parity i * D.parity j).val = 1 := by
      rw [← pow_two, ← pow_mul, mul_comm _ 2, pow_mul, hπ, one_pow]
    rw [mul_left_comm, hp, mul_one]
  rw [hc]
  rfl

private theorem denominator_qpInt (hπ : π ^ 2 = 1) (i : I) (n : ℤ) :
    vermaDenominator D.toSuperCartanDatum q π i * qpInt (D.qi q i) (D.pii π i) n =
      ((D.qi q i ^ n : kˣ) : k) - D.pii π i ^ n.natAbs * ((D.qi q i ^ (-n) : kˣ) : k) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa only [vermaDenominator, qpInt_ofNat, zpow_natCast, zpow_neg,
      ← inv_pow, Units.val_pow_eq_pow_val, Int.natAbs_natCast] using
      qpNat_mul_sub (q := D.qi q i) (π := D.pii π i) m
  · simpa only [vermaDenominator, zpow_natCast, zpow_neg, neg_neg,
      ← inv_pow, Units.val_pow_eq_pow_val, Int.natAbs_neg, Int.natAbs_natCast] using
      qpInt_neg_mul_sub (q := D.qi q i) (D.pii_sq π hπ i) m

variable [DecidableEq I] [DecidableEq X]

omit [DecidableEq I] [DecidableEq X] in
private theorem mixed_correction_monomial (hπ : π ^ 2 = 1) (i : I) (n : ℤ)
    (hden : IsUnit (vermaDenominator D.toSuperCartanDatum q π i)) (w : List I) :
    Ring.inverse (vermaDenominator D.toSuperCartanDatum q π i) •
      (((D.qi q i ^ n : kˣ) : k) • weightTwist D.toSuperCartanDatum q⁻¹ i (monomial k w) -
        (D.pii π i ^ n.natAbs * ((D.qi q i ^ (-n) : kˣ) : k)) •
          weightTwist D.toSuperCartanDatum q i (monomial k w)) =
      qpInt (D.qi q i) (D.pii π i) (n - D.h i (halfWeight D true (wordWeight w))) •
        monomial k w := by
  rw [weightTwist_monomial, weightTwist_monomial]
  simp only [smul_smul, ← sub_smul]
  congr 1
  have hinv : D.qi q⁻¹ i = (D.qi q i)⁻¹ := by simp [SuperCartanDatum.qi]
  rw [hinv, inv_zpow, ← zpow_neg]
  have he : ((D.qi q i ^ n : kˣ) : k) *
        ((D.qi q i ^ (-D.h i (halfWeight D true (wordWeight w))) : kˣ) : k) -
      (D.pii π i ^ n.natAbs * ((D.qi q i ^ (-n) : kˣ) : k)) *
        ((D.qi q i ^ D.h i (halfWeight D true (wordWeight w)) : kˣ) : k) =
      vermaDenominator D.toSuperCartanDatum q π i *
        qpInt (D.qi q i) (D.pii π i) (n - D.h i (halfWeight D true (wordWeight w))) := by
    rw [denominator_qpInt D q π hπ, pii_pow_sub_word D π hπ]
    simp only [mul_assoc, ← Units.val_mul, ← zpow_add, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm]
  rw [he, ← mul_assoc, Ring.inverse_mul_cancel _ hden, one_mul]

omit [DecidableEq X] in
/-- The mixed relation on a homogeneous free word, in the [BE2] normalization. -/
theorem lowerFree_mixed_monomial (hπ : π ^ 2 = 1) (i j : I) (n : ℤ)
    (hden : IsUnit (vermaDenominator D.toSuperCartanDatum q π i)) (w : List I) :
    lowerFree D.toSuperCartanDatum q π i n (θ k j * monomial k w) =
      π ^ (D.parity i * D.parity j).val •
        (θ k j * lowerFree D.toSuperCartanDatum q π i n (monomial k w)) +
      if i = j then
        qpInt (D.qi q i) (D.pii π i) (n - D.h i (halfWeight D true (wordWeight w))) •
          monomial k w
      else 0 := by
  simp only [lowerFree, LinearMap.smul_apply, lowerNumerator_θ_mul]
  rw [smul_add]
  congr 1
  · rw [mul_smul_comm, smul_comm]
  · by_cases h : i = j
    · simp only [h, ite_true, parity_twist_twist' D q π hπ]
      exact mixed_correction_monomial D q π hπ j n (h ▸ hden) w
    · simp [h]

/-- The mixed quantum-integer relation on each actual free weight projection. -/
theorem lowerFree_mixed_project (hπ : π ^ 2 = 1) (i j : I) (Λ μ : X)
    (hden : IsUnit (vermaDenominator D.toSuperCartanDatum q π i)) (x : PreF k I) :
    lowerFree D.toSuperCartanDatum q π i (D.h i Λ) (θ k j * weightProjectFree D Λ μ x) =
      π ^ (D.parity i * D.parity j).val •
        (θ k j * lowerFree D.toSuperCartanDatum q π i (D.h i Λ) (weightProjectFree D Λ μ x)) +
      if i = j then qpInt (D.qi q i) (D.pii π i) (D.h i μ) • weightProjectFree D Λ μ x else 0 := by
  induction x using induction_monomial with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, mul_add, hx, hy, smul_add]
    split_ifs <;> module
  | smul c x hx =>
    simp only [map_smul, mul_smul_comm, hx]
    split_ifs <;> module
  | word w =>
    rw [weightProjectFree_monomial]
    by_cases h : halfWeight D true (wordWeight w) = Λ - μ
    · rw [ite_eq_left h, lowerFree_mixed_monomial D q π hπ i j (D.h i Λ) hden, h]
      simp only [RootDatum.h, map_sub, sub_sub_cancel]
    · simp [h]

namespace GenericVerma
open Coefficients
variable [Finite I] (hD : D.toSuperCartanDatum.BarConsistent)

/-- The normalized mixed relation on the actual negative Serre quotient weight space. -/
theorem lower_mixed_project (i j : I) (Λ μ : X) (x : D.serreF Coefficients.q pi) :
    lower D.toSuperCartanDatum hD i (D.h i Λ)
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring j) * weightProject D hD Λ μ x) =
      pi ^ (D.parity i * D.parity j).val •
        (D.toSerreF Coefficients.q pi (θ Coefficients.Ring j) *
          lower D.toSuperCartanDatum hD i (D.h i Λ) (weightProject D hD Λ μ x)) +
      if i = j then
        qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i μ) • weightProject D hD Λ μ x else 0 := by
  obtain ⟨y, rfl⟩ := D.toSerreF_surjective Coefficients.q pi x
  rw [weightProject_mk, ← map_mul, lower_mk,
    lowerFree_mixed_project D Coefficients.q pi pi_sq i j Λ μ
      (vermaDenominator_isUnit D.toSuperCartanDatum i)]
  simp only [map_add, map_smul, map_mul, lower_mk]
  split_ifs <;> simp

end GenericVerma
end OddMath.CoveringQuantum.UDot
