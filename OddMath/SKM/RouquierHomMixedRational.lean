import OddMath.SKM.RouquierHomMixedInterchange
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Rational mixed coefficients on a nilpotent component

`SwappedHomInversion.md` §3 (2)–(3): denominator invertibility and the
ordered geometric expansion of the prescribed rational coefficient. Ring
multiplication is functional order (`f * g = g ≫ f` for categorical End).
The exponent is supplied for each AB object separately; assembly from
inputwise local nilpotence is not asserted. No rational square formula is
assumed, and the prescribed swapping entry remains `-J⁻¹ a²`.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.SKM
variable {R : Type*} [Ring R]

/-- The ordinary denominator is a unit; no domain assumption is used. -/
theorem mixedEvenDenominator_isUnit (x : Rˣ) (y : R)
    (h : Commute (x : R) y) (n : ℕ) (hn : y ^ n = 0) :
    IsUnit ((x : R) - y) := by
  simpa only [sub_eq_add_neg] using
    (show IsNilpotent (-y) from (show IsNilpotent y from ⟨n, hn⟩).neg).isUnit_add_left_of_commute
      x.isUnit h.symm.neg_left

/-- The prescribed inverse, rather than a definition by a finite sum. -/
theorem mixedEvenInverse_expansion (x : Rˣ) (y : R)
    (h : Commute (x : R) y) (n : ℕ) (hn : y ^ n = 0) :
    Ring.inverse ((x : R) - y) =
      ∑ r ∈ Finset.range n, (↑x⁻¹ : R) ^ (r + 1) * y ^ r := by
  let z : R := (↑x⁻¹ : R) * y
  have hi : Commute (↑x⁻¹ : R) y := h.units_inv_left
  have hz : z ^ n = 0 := by simp [z, hi.mul_pow, hn]
  have hf : (x : R) - y = (x : R) * (1 - z) := by simp [z, mul_sub, ← mul_assoc]
  have hg : (1 - z) * (∑ r ∈ Finset.range n, z ^ r) = 1 := by
    rw [← neg_sub z 1, neg_mul, mul_geom_sum, hz]
    simp
  have hp : ((x : R) - y) * ((∑ r ∈ Finset.range n, z ^ r) * ↑x⁻¹) = 1 := by
    rw [hf, mul_assoc, ← mul_assoc (1 - z), hg]
    simp
  have he : Ring.inverse ((x : R) - y) = (∑ r ∈ Finset.range n, z ^ r) * ↑x⁻¹ := by
    calc
      Ring.inverse ((x : R) - y) = Ring.inverse ((x : R) - y) * 1 := (mul_one _).symm
      _ = _ := by rw [← hp, ← mul_assoc,
        Ring.inverse_mul_cancel _ (mixedEvenDenominator_isUnit x y h n hn), one_mul]
  rw [he, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [show z ^ r = (↑x⁻¹ : R) ^ r * y ^ r from hi.mul_pow r]
  rw [mul_assoc, ← (hi.pow_right r).eq, ← mul_assoc, ← pow_succ]

private theorem mixedOdd_inverse_exchange (x : Rˣ) (y : R)
    (h : (x : R) * y = -(y * x)) :
    y * (↑x⁻¹ : R) = -((↑x⁻¹ : R) * y) := by
  have ht := congrArg (fun a : R => (↑x⁻¹ : R) * a * ↑x⁻¹) h
  simpa [mul_assoc] using ht

private theorem mixedOdd_square_commute (x y : R) (h : x * y = -(y * x)) :
    Commute x (y ^ 2) := by
  change x * y ^ 2 = y ^ 2 * x
  calc
    x * y ^ 2 = (x * y) * y := by simp [pow_two, mul_assoc]
    _ = (-(y * x)) * y := congrArg (fun a : R => a * y) h
    _ = -(y * (x * y)) := by simp only [neg_mul, mul_assoc]
    _ = y ^ 2 * x := by simp only [h, mul_neg, neg_neg, pow_two, mul_assoc]

/-- The odd square denominator is a unit over any ring. -/
theorem mixedOddDenominator_isUnit (x : Rˣ) (y : R)
    (h : (x : R) * y = -(y * x)) (n : ℕ) (hn : y ^ n = 0) :
    IsUnit ((x : R) ^ 2 - y ^ 2) := by
  have hs : (y ^ 2) ^ n = 0 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hn, zero_pow (by decide : 2 ≠ 0)]
  have hh : Commute (↑(x ^ (2 : ℕ)) : R) (y ^ 2) :=
    (mixedOdd_square_commute (x : R) y h).pow_left 2
  simpa only [Units.val_pow_eq_pow_val] using
    mixedEvenDenominator_isUnit (x ^ (2 : ℕ)) (y ^ 2) hh n hs

/-- Pair even and odd powers without reversing their order. -/
private theorem mixedOdd_paired_sum (x : Rˣ) (y : R)
    (h : (x : R) * y = -(y * x)) (n : ℕ) :
    ((x : R) - y) * (∑ r ∈ Finset.range n, (↑x⁻¹ : R) ^ (2 * (r + 1)) * y ^ (2 * r)) =
      ∑ r ∈ Finset.range (2 * n), (-1 : R) ^ r * (↑x⁻¹ : R) ^ (r + 1) * y ^ r := by
  have hi := mixedOdd_inverse_exchange x y h
  have hc : Commute y ((↑x⁻¹ : R) ^ 2) := mixedOdd_square_commute y _ hi
  have hp (r : ℕ) :
      ((x : R) - y) * ((↑x⁻¹ : R) ^ (2 * (r + 1)) * y ^ (2 * r)) =
        (-1 : R) ^ (2 * r) * (↑x⁻¹ : R) ^ (2 * r + 1) * y ^ (2 * r) +
        (-1 : R) ^ (2 * r + 1) * (↑x⁻¹ : R) ^ (2 * r + 1 + 1) * y ^ (2 * r + 1) := by
    have he : 2 * (r + 1) = 2 * r + 1 + 1 := by omega
    have hm := (hc.pow_right (r + 1)).eq
    rw [← pow_mul] at hm
    have hs : (-1 : R) ^ (2 * r) = 1 := by simp [pow_mul]
    rw [pow_succ (-1 : R), hs, one_mul, one_mul, neg_one_mul]
    rw [sub_mul, ← mul_assoc y, hm, mul_assoc _ y, ← pow_succ' y]
    rw [he, pow_succ' (↑x⁻¹ : R) (2 * r + 1), ← mul_assoc (x : R),
      ← mul_assoc (x : R), x.mul_inv, one_mul]
    rw [show 2 * r + 1 = 1 + 2 * r by omega]
    simp only [sub_eq_add_neg, neg_mul]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, hp]
    have he : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [he, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [add_assoc]

/-- The prescribed odd rational coefficient equals the signed ordered expansion.
The supplied exponent is for this ring component only. -/
theorem mixedOddInverse_expansion (x : Rˣ) (y : R)
    (h : (x : R) * y = -(y * x)) (n : ℕ) (hn : y ^ n = 0) :
    ((x : R) - y) * Ring.inverse ((x : R) ^ 2 - y ^ 2) =
      ∑ r ∈ Finset.range (2 * n), (-1 : R) ^ r * (↑x⁻¹ : R) ^ (r + 1) * y ^ r := by
  have hs : (y ^ 2) ^ n = 0 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hn, zero_pow (by decide : 2 ≠ 0)]
  have he := mixedEvenInverse_expansion (x ^ 2) (y ^ 2)
    ((mixedOdd_square_commute (x : R) y h).pow_left 2) n hs
  simp only [Units.val_pow_eq_pow_val, Units.inv_pow_eq_pow_inv] at he
  rw [he]
  simpa only [← pow_mul] using mixedOdd_paired_sum x y h n
section Components
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T W : RouquierFamily (k := k) (B := B) D) (i : I) (β : I →₀ ℕ)
  {muP nuP muM nuM : X}
  (hT : -nuP + D.α i = -muP) (hW : muM + D.α i = nuM)
  (Z : homWeightSector T.obj W.obj muP muM)

/-- The shifted pre dot on the AB component, in functional multiplication order. -/
abbrev homContentMixedPreDot :
    End ((homContentPostE T.obj W i (β + Finsupp.single i 1) nuP hW).obj
      ((homContentPreE T W.obj i muM hT).obj Z)) :=
  (homContentPostE T.obj W i (β + Finsupp.single i 1) nuP hW).map (T.dot i hT ▷ Z)

/-- The shifted reservoir dot on the same AB component. -/
abbrev homContentMixedReservoirDot :
    End ((homContentPostE T.obj W i (β + Finsupp.single i 1) nuP hW).obj
      ((homContentPreE T W.obj i muM hT).obj Z)) :=
  homContentPostDot T.obj W i (β + Finsupp.single i 1) nuP hW (T.E i hT ≫ Z)

/-- Componentwise even expansion. Invertibility and the nilpotence exponent are
required only on the specified AB object, not uniformly on a weight fibre. -/
theorem homContentMixedRational_even (hp : D.parity i = 0)
    (hx : IsUnit (homContentMixedPreDot T W i β hT hW Z))
    (n : ℕ) (hn : homContentMixedReservoirDot T W i β hT hW Z ^ n = 0) :
    let x := homContentMixedPreDot T W i β hT hW Z
    let y := homContentMixedReservoirDot T W i β hT hW Z
    IsUnit (x - y) ∧ Ring.inverse (x - y) =
      ∑ r ∈ Finset.range n, Ring.inverse x ^ (r + 1) * y ^ r := by
  dsimp only
  have hc : Commute (homContentMixedPreDot T W i β hT hW Z)
      (homContentMixedReservoirDot T W i β hT hW Z) := by
    have ht := homContentMixedDot_exchange T W i β hT hW Z
    simp only [hp, koszulSign_zero_left, one_smul] at ht
    exact ht.symm
  obtain ⟨x, hx⟩ := hx
  rw [← hx] at hc ⊢
  exact ⟨mixedEvenDenominator_isUnit x _ hc n hn,
    by simpa only [Ring.inverse_unit] using mixedEvenInverse_expansion x _ hc n hn⟩

/-- Componentwise odd expansion of the prescribed square-denominator expression.
No locally nilpotent natural-transformation assembly is asserted. -/
theorem homContentMixedRational_odd (hp : D.parity i = 1)
    (hx : IsUnit (homContentMixedPreDot T W i β hT hW Z))
    (n : ℕ) (hn : homContentMixedReservoirDot T W i β hT hW Z ^ n = 0) :
    let x := homContentMixedPreDot T W i β hT hW Z
    let y := homContentMixedReservoirDot T W i β hT hW Z
    IsUnit (x ^ 2 - y ^ 2) ∧ (x - y) * Ring.inverse (x ^ 2 - y ^ 2) =
      ∑ r ∈ Finset.range (2 * n), (-1) ^ r * Ring.inverse x ^ (r + 1) * y ^ r := by
  dsimp only
  have hc : homContentMixedPreDot T W i β hT hW Z *
      homContentMixedReservoirDot T W i β hT hW Z =
      -(homContentMixedReservoirDot T W i β hT hW Z *
        homContentMixedPreDot T W i β hT hW Z) := by
    have ht := homContentMixedDot_exchange T W i β hT hW Z
    simp only [hp, koszulSign_one_one, neg_one_smul] at ht
    exact (neg_eq_iff_eq_neg.mp ht.symm)
  obtain ⟨x, hx⟩ := hx
  rw [← hx] at hc ⊢
  exact ⟨mixedOddDenominator_isUnit x _ hc n hn,
    by simpa only [Ring.inverse_unit] using mixedOddInverse_expansion x _ hc n hn⟩
end Components
end OddMath.SKM
