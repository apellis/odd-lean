import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerMoments
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Ordered odd remainder coefficients on the power vacuum

The parity conversion in `SwappedVacuumNonpositiveBubbles.md`, §2,
relates the actual inverse-row moments to the ordered monic remainder
recurrence. Coefficient order and the top inverse-row sign are retained.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem sign_natCast (n : ℕ) : sign k (n : ZMod 2) = (-1 : k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, sign_add, ih, sign_one, pow_succ]

/-- The parity correction from the actual signed inverse row to the
ordinary coefficient of the top monic remainder, for an odd moving colour. -/
def ordinaryMomentSign (i : I) (n : ℕ) : k :=
  CyclotomicCrossingTensor.inductionUnitDotSign (k := k) 1 (cutoff i - 1) *
    sign k (((cutoff i - 1 : ℕ) : ZMod 2) * ((n + (cutoff i - 1) : ℕ) : ZMod 2))

/-- Ordinary remainder moments obtained from the actual row; they are not
introduced as independently prescribed coefficient values. -/
def ordinaryMoment (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  ordinaryMomentSign (k := k) cutoff i n • rawMoment D Sc cutoff L i hN 1 n

private theorem ordinaryMomentSign_shift (i : I) (j m : ℕ) :
    ordinaryMomentSign (k := k) cutoff i (j + m) =
      ordinaryMomentSign (k := k) cutoff i (cutoff i + m) *
        sign k (((cutoff i - 1 : ℕ) : ZMod 2) * ((cutoff i : ZMod 2) - j)) := by
  unfold ordinaryMomentSign
  rw [mul_assoc, ← sign_add]
  congr 2
  push_cast
  ring_nf
  simp only [ZMod.neg_eq_self_mod_two, show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]

/-- The corrected moments satisfy the literal ordered monic recurrence.
In shifted indexing this is equation (6) of the written reservoir calculation. -/
theorem ordinaryMoment_recurrence (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1),
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (singleCoefficient D cutoff i j) * ordinaryMoment D Sc cutoff L i hN (j.val + m)) = 0 := by
  have h := rawMoment_one_recurrence D Sc cutoff L i hN m
  rw [hi] at h
  simp only [nsmul_eq_mul, mul_one] at h
  have hs := congrArg (fun z : CoefficientPowerQuotient (k := k) D cutoff L =>
    ordinaryMomentSign (k := k) cutoff i (cutoff i + m) • z) h
  rw [smul_zero, Finset.smul_sum] at hs
  calc
    _ = ∑ j : Fin (cutoff i + 1),
        ordinaryMomentSign (k := k) cutoff i (cutoff i + m) •
          (koszulSign (((cutoff i - 1 : ℕ) : ZMod 2)) ((cutoff i : ZMod 2) - j.val) •
            ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
              (singleCoefficient D cutoff i j) * rawMoment D Sc cutoff L i hN 1 (j.val + m))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [ordinaryMoment, mul_smul_comm, ordinaryMomentSign_shift (k := k) cutoff i
        j.val m, mul_smul, koszulSign_smul (R := k)]
    _ = 0 := hs

/-- The corrected row is the ordinary top-coefficient window on all
low monomials, with value one at the top. -/
theorem ordinaryMoment_window (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (n : ℕ) (hn : n < cutoff i) :
    ordinaryMoment D Sc cutoff L i hN n = if n + 1 = cutoff i then 1 else 0 := by
  rw [ordinaryMoment, rawMoment_one_window D Sc cutoff L i hN n hn]
  by_cases ht : n + 1 = cutoff i
  · have he : n = cutoff i - 1 := by omega
    subst n
    have hp : (((cutoff i - 1 : ℕ) : ZMod 2) *
        ((cutoff i - 1 + (cutoff i - 1) : ℕ) : ZMod 2)) = 0 := by
      push_cast
      rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, mul_zero]
    simp only [ordinaryMomentSign, hi, hp, Supercategory.sign_zero, mul_one, ite_eq_left ht,
      smul_smul, inductionUnitDotSign, Supercategory.sign_mul_self, one_smul]
  · simp only [ite_eq_right ht, smul_zero]

/-- The sequence of ordinary top remainders at exponents N−1+l. -/
def remainder (i : I) (hN : 0 < cutoff i) (l : ℕ) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  ordinaryMoment D Sc cutoff L i hN (cutoff i - 1 + l)

theorem remainder_zero (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) :
    remainder D Sc cutoff L i hN 0 = 1 := by
  have h := ordinaryMoment_window D Sc cutoff L i hi hN (cutoff i - 1) (by omega)
  have ht : cutoff i - 1 + 1 = cutoff i := by omega
  simpa only [remainder, Nat.add_zero, ite_eq_left ht] using h

/-- The complete ordered remainder recurrence; terms with a negative
shift are zero by the proved low window, rather than negative dot powers. -/
theorem remainder_recurrence (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (l : ℕ) (hl : 0 < l) :
    (∑ j : Fin (cutoff i + 1),
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (singleCoefficient D cutoff i j) *
          (if cutoff i - j.val ≤ l then remainder D Sc cutoff L i hN (l - (cutoff i - j.val))
           else 0)) = 0 := by
  calc
    _ = ∑ j : Fin (cutoff i + 1),
        (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
          (singleCoefficient D cutoff i j) * ordinaryMoment D Sc cutoff L i hN (j.val + (l - 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      by_cases hj : cutoff i - j.val ≤ l
      · rw [ite_eq_left hj, remainder]
        congr 1
        have hv := j.isLt
        omega
      · rw [ite_eq_right hj]
        have hv := j.isLt
        have he := ordinaryMoment_window D Sc cutoff L i hi hN (j.val + (l - 1)) (by omega)
        have ht : ¬ j.val + (l - 1) + 1 = cutoff i := by omega
        simpa only [ite_eq_right ht] using he.symm
    _ = 0 := ordinaryMoment_recurrence D Sc cutoff L i hi hN (l - 1)

private theorem chi_mem_coefficientIdeal (i : I) (hi : D.parity i = 1)
    (r : ℕ) (hr : cutoff i / 2 < r) :
    SKM.SYM.elvChi D k ⟨i, hi⟩ r ∈ SKM.SYM.elvCoefficientIdeal D k cutoff := by
  have he : r = (r - 1) + 1 := by omega
  rw [he, SKM.SYM.elvChi]
  apply TwoSidedIdeal.subset_span
  apply Or.inl
  refine ⟨i, r - 1, ?_, rfl⟩
  have hzero : ¬ D.parity i = 0 := by rw [hi]; decide
  simp only [SKM.SYM.elvElementaryRank, ite_eq_right hzero]
  omega

/-- Every coefficient beyond the odd cutoff vanishes in literal A/T.
At an even cutoff the first odd tail is the defining δχ relation. -/
theorem odd_coefficient_tail (i : I) (hi : D.parity i = 1)
    (n : ℕ) (hn : cutoff i < n) :
    coefficientPowerQuotientMap (k := k) D cutoff L
      (SKM.SYM.elvCoefficient D k ⟨i, hi⟩ n) = 0 := by
  apply (coefficientPowerQuotientMap_eq_zero_iff D cutoff L _).mpr
  apply TwoSidedIdeal.mem_sup_left
  unfold SKM.SYM.elvCoefficient
  split_ifs with hn2
  · exact chi_mem_coefficientIdeal D cutoff i hi (n / 2) (by omega)
  · by_cases hr : cutoff i / 2 < n / 2
    · exact (SKM.SYM.elvCoefficientIdeal D k cutoff).mul_mem_left _ _
        (chi_mem_coefficientIdeal D cutoff i hi (n / 2) hr)
    · have hN : cutoff i % 2 = 0 := by omega
      have he : n / 2 = cutoff i / 2 := by omega
      rw [he]
      exact TwoSidedIdeal.subset_span (Or.inr ⟨⟨i, hi⟩, hN, rfl⟩)

private theorem coeff_monomial_mul {A : Type u} [Semiring A]
    (n l : ℕ) (a : A) (f : PowerSeries A) :
    PowerSeries.coeff l (PowerSeries.monomial n a * f) =
      if n ≤ l then a * PowerSeries.coeff (l - n) f else 0 := by
  change MvPowerSeries.coeff (Finsupp.single () l)
    (MvPowerSeries.monomial (Finsupp.single () n) a * f) = _
  rw [MvPowerSeries.coeff_monomial_mul]
  simp only [Finsupp.single_le_single, ← Finsupp.single_tsub]
  rfl

/-- The reversed literal monic relation, with its original coefficient
order, as a finite formal series on the actual power quotient. -/
def remainderPolynomial (i : I) : PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  ∑ j : Fin (cutoff i + 1), PowerSeries.monomial (cutoff i - j.val)
    ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (singleCoefficient D cutoff i j))

/-- The complete series of actual ordinary top remainders. -/
def remainderSeries (i : I) (hN : 0 < cutoff i) :
    PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  PowerSeries.mk (remainder D Sc cutoff L i hN)

/-- The ordered monic recurrence is a literal power-series inverse
identity on A/T, at every coefficient. The coefficient ring is not made
commutative and no coefficient is inverted. -/
theorem remainderPolynomial_mul_remainderSeries (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) :
    remainderPolynomial D cutoff L i * remainderSeries D Sc cutoff L i hN = 1 := by
  classical
  apply PowerSeries.ext
  intro l
  simp only [remainderPolynomial, remainderSeries, Finset.sum_mul, map_sum,
    coeff_monomial_mul, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  by_cases hl : l = 0
  · subst l
    rw [ite_eq_left rfl]
    rw [Finset.sum_eq_single (Fin.last (cutoff i))]
    · simp only [Fin.val_last, Nat.sub_self, le_refl, ↓reduceIte,
        singleCoefficient_top, map_one, remainder_zero D Sc cutoff L i hi hN, mul_one]
    · intro j _ hj
      have hne : j.val ≠ cutoff i := by
        intro h
        apply hj
        exact Fin.ext h
      have hv := j.isLt
      rw [ite_eq_right (by omega : ¬ cutoff i - j.val ≤ 0)]
    · simp
  · rw [ite_eq_right hl]
    simpa only [mul_ite, mul_zero] using remainder_recurrence D Sc cutoff L i hi hN l (by omega)

include Sc in
/-- The reversed monic relation has constant coefficient one. -/
theorem remainderPolynomial_constantCoeff (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) :
    PowerSeries.constantCoeff (remainderPolynomial (k := k) D cutoff L i) = 1 := by
  have h := congrArg PowerSeries.constantCoeff
    (remainderPolynomial_mul_remainderSeries D Sc cutoff L i hi hN)
  rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply
    (φ := remainderSeries D Sc cutoff L i hN), remainderSeries, PowerSeries.coeff_mk,
      remainder_zero D Sc cutoff L i hi hN, mul_one, map_one] at h
  exact h

/-- The actual remainder series is the formal inverse with unit constant
coefficient. This is derived from the old relation and the actual inverse row. -/
theorem remainderSeries_eq_invOfUnit (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) :
    remainderSeries D Sc cutoff L i hN =
      PowerSeries.invOfUnit (remainderPolynomial D cutoff L i) 1 := by
  have hC : PowerSeries.constantCoeff (remainderPolynomial (k := k) D cutoff L i) =
      ((1 : (CoefficientPowerQuotient (k := k) D cutoff L)ˣ) : _) :=
    remainderPolynomial_constantCoeff D Sc cutoff L i hi hN
  calc
    _ = (PowerSeries.invOfUnit (remainderPolynomial D cutoff L i) 1 *
        remainderPolynomial D cutoff L i) * remainderSeries D Sc cutoff L i hN := by
      rw [PowerSeries.invOfUnit_mul _ _ hC, one_mul]
    _ = _ := by
      rw [mul_assoc, remainderPolynomial_mul_remainderSeries D Sc cutoff L i hi hN, mul_one]

private theorem choose_two_add (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + a * b + b.choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h1 : (a + b + 1).choose 2 = (a + b) + (a + b).choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ (a + b) 1
    have h2 : (b + 1).choose 2 = b + b.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ b 1
    rw [Nat.add_succ, h1, ih, h2]
    ring

private theorem triangular_ordinary_sign (i : I) (l : ℕ) :
    sign k (((cutoff i - 1 + l).choose 2 : ℕ) : ZMod 2) =
      sign k ((l.choose 2 : ℕ) : ZMod 2) *
        ordinaryMomentSign (k := k) cutoff i (cutoff i - 1 + l) := by
  unfold ordinaryMomentSign
  simp only [inductionUnitDotSign, nsmul_eq_mul, mul_one, ← Supercategory.sign_add]
  congr 1
  rw [choose_two_add]
  push_cast
  ring_nf
  simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]

/-- All higher signed moments have the exact ordinary-remainder sign
in equation (5), including the sign of the extracted odd coefficient. -/
theorem signedMoment_remainder (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (l : ℕ) :
    signedMoment D Sc cutoff L i hN (cutoff i - 1 + l) =
      sign k ((l.choose 2 : ℕ) : ZMod 2) • remainder D Sc cutoff L i hN l := by
  rw [signedMoment_rawMoment]
  simp only [hi, remainder, ordinaryMoment, inductionUnitDotSign,
    nsmul_eq_mul, mul_one, smul_smul]
  rw [triangular_ordinary_sign (k := k) cutoff i l]

end OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
