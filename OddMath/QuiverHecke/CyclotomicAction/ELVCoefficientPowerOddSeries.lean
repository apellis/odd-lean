import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerRemainders
import OddMath.SKM.BubbleSubstitution
import Mathlib.RingTheory.PowerSeries.Expand

/-! # Even and odd series of the literal power-vacuum remainders

The closed series of `SwappedVacuumNonpositiveBubbles.md`, §2 (7),
come from the actual monic remainder series. Polynomial series operations
are performed in the commutative polynomial algebra before mapping to A/T.
The latter retains its original ring and exterior coefficient order.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem sign_natCast (n : ℕ) : sign k (n : ZMod 2) = (-1 : k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, sign_add, ih, sign_one, pow_succ]

private theorem reversed_negative_one_power (N n : ℕ) (hn : n ≤ N) :
    (-1 : k) ^ (N * (N - n + 1)) = (-1 : k) ^ (N * n) := by
  have hp : ((N * (N - n + 1) : ℕ) : ZMod 2) = ((N * n : ℕ) : ZMod 2) := by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hn, Nat.cast_one, Nat.cast_mul]
    rcases parity_eq_zero_or_one (N : ZMod 2) with hN | hN <;> rw [hN] <;>
      rcases parity_eq_zero_or_one (n : ZMod 2) with hn | hn <;> rw [hn] <;> decide
  rw [← sign_natCast, ← sign_natCast, hp]

private theorem odd_reversed_coefficient (i : I) (hi : D.parity i = 1)
    (n : ℕ) (hn : n ≤ cutoff i) :
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (singleCoefficient D cutoff i ⟨cutoff i - n, by omega⟩) =
      (-1 : k) ^ (cutoff i * n) • coefficientPowerQuotientMap (k := k) D cutoff L
        (SKM.SYM.elvCoefficient D k ⟨i, hi⟩ n) := by
  unfold singleCoefficient
  rw [dite_eq_left hi, SKM.SYM.elvMonicCoefficient, map_smul, map_smul]
  rw [show cutoff i - (cutoff i - n) = n by omega,
    reversed_negative_one_power (k := k) (cutoff i) n hn]
  rfl

/-- At every degree the reversed actual monic relation has exactly the
ordered odd coefficient. The proved cutoff tail supplies the large degrees. -/
theorem odd_remainderPolynomial_coeff (i : I) (hi : D.parity i = 1) (n : ℕ) :
    PowerSeries.coeff n (remainderPolynomial (k := k) D cutoff L i) =
      (-1 : k) ^ (cutoff i * n) • coefficientPowerQuotientMap D cutoff L
        (SKM.SYM.elvCoefficient D k ⟨i, hi⟩ n) := by
  classical
  rw [remainderPolynomial, map_sum]
  by_cases hn : n ≤ cutoff i
  · let j : Fin (cutoff i + 1) := ⟨cutoff i - n, by omega⟩
    rw [Finset.sum_eq_single j]
    · rw [PowerSeries.coeff_monomial, ite_eq_left (by dsimp [j]; omega)]
      exact odd_reversed_coefficient D cutoff L i hi n hn
    · intro b _ hb
      rw [PowerSeries.coeff_monomial, ite_eq_right]
      intro he
      apply hb
      apply Fin.ext
      have hv := b.isLt
      dsimp [j]
      omega
    · simp
  · rw [odd_coefficient_tail D cutoff L i hi n (by omega), smul_zero]
    apply Finset.sum_eq_zero
    intro j _
    rw [PowerSeries.coeff_monomial, ite_eq_right (by have hv := j.isLt; omega)]

/-- Polynomial coefficient evaluation in literal A/T. Series expansion
and rescaling are performed before applying this map. -/
def polynomialToPower : MvPolynomial (I × ℕ) k →ₐ[k] CoefficientPowerQuotient (k := k) D cutoff L :=
  (coefficientPowerQuotientMap D cutoff L).comp (SKM.SYM.polynomialInclude D k)

private theorem polynomial_generatorCoeff (i : I) (hi : D.parity i = 1) (n : ℕ) :
    polynomialToPower (k := k) D cutoff L (PowerSeries.coeff n (SKM.SYM.generatorSeries k i)) =
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.elvChi D k ⟨i, hi⟩ n) := by
  cases n with
  | zero => simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff, SKM.SYM.elvChi]
  | succ n =>
    simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff, SKM.SYM.elvChi,
      polynomialToPower, AlgHom.comp_apply]

/-- The even-power elementary series, expanded in the commutative
universal polynomial algebra and then evaluated in literal A/T. -/
def elementaryEvenSeries (i : I) : PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  PowerSeries.map (polynomialToPower D cutoff L).toRingHom
    (PowerSeries.expand 2 (by decide) (SKM.SYM.generatorSeries k i))

/-- Its coefficient formula retains the actual odd elementary coefficients. -/
theorem elementaryEvenSeries_coeff (i : I) (hi : D.parity i = 1) (n : ℕ) :
    PowerSeries.coeff n (elementaryEvenSeries (k := k) D cutoff L i) =
      if n % 2 = 0 then coefficientPowerQuotientMap D cutoff L
        (SKM.SYM.elvChi D k ⟨i, hi⟩ (n / 2)) else 0 := by
  rw [elementaryEvenSeries, PowerSeries.coeff_map, PowerSeries.coeff_expand]
  by_cases hn : n % 2 = 0
  · rw [ite_eq_left ((Nat.dvd_iff_mod_eq_zero).mpr hn), ite_eq_left hn]
    exact polynomial_generatorCoeff D cutoff L i hi (n / 2)
  · rw [ite_eq_right (fun h => hn (Nat.dvd_iff_mod_eq_zero.mp h)), ite_eq_right hn, map_zero]

private theorem coeff_mul_monomial {A : Type u} [Semiring A]
    (n l : ℕ) (a : A) (f : PowerSeries A) :
    PowerSeries.coeff l (f * PowerSeries.monomial n a) =
      if n ≤ l then PowerSeries.coeff (l - n) f * a else 0 := by
  change MvPowerSeries.coeff (Finsupp.single () l)
    (f * MvPowerSeries.monomial (Finsupp.single () n) a) = _
  rw [MvPowerSeries.coeff_mul_monomial]
  simp only [Finsupp.single_le_single, ← Finsupp.single_tsub]
  rfl

private theorem chi_commute_delta (i : I) (hi : D.parity i = 1) (n : ℕ) :
    Commute (coefficientPowerQuotientMap (k := k) D cutoff L (SKM.SYM.elvChi D k ⟨i, hi⟩ n))
      (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) := by
  cases n with
  | zero => simp [SKM.SYM.elvChi]
  | succ n =>
    exact (SKM.SYM.e_commute_all D k i n (SKM.SYM.delta D k ⟨i, hi⟩)).map
      (coefficientPowerQuotientMap D cutoff L).toRingHom

/-- The exact linear exterior factor in the odd reversed monic relation. -/
def oddLinearTerm (i : I) (hi : D.parity i = 1) :
    PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  PowerSeries.monomial 1 (((-1 : k) ^ cutoff i) •
    coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩))

/-- The literal reversed odd monic polynomial factors as C(w²)(1+sδw),
including the even-cutoff top exterior relation through its proved tail. -/
theorem remainderPolynomial_factor (i : I) (hi : D.parity i = 1) :
    remainderPolynomial (k := k) D cutoff L i =
      elementaryEvenSeries D cutoff L i * (1 + oddLinearTerm D cutoff L i hi) := by
  apply PowerSeries.ext
  intro n
  rw [odd_remainderPolynomial_coeff D cutoff L i hi n, mul_add, mul_one, map_add,
    oddLinearTerm, coeff_mul_monomial, elementaryEvenSeries_coeff D cutoff L i hi n]
  by_cases hz : n = 0
  · subst n
    simp [SKM.SYM.elvCoefficient, SKM.SYM.elvChi]
  · rw [ite_eq_left (by omega : 1 ≤ n), elementaryEvenSeries_coeff D cutoff L i hi (n - 1)]
    by_cases hn : n % 2 = 0
    · have hn1 : ¬ (n - 1) % 2 = 0 := by omega
      have hs : (-1 : k) ^ (cutoff i * n) = 1 :=
        ((even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr hn) : Even n).mul_left (cutoff i)).neg_one_pow
      rw [SKM.SYM.elvCoefficient]
      simp only [ite_eq_left hn, ite_eq_right hn1]
      rw [hs, one_smul, zero_mul, add_zero]
    · have hn1 : (n - 1) % 2 = 0 := by omega
      have hodd : Odd n := Nat.odd_iff.mpr (by omega)
      have hs : (-1 : k) ^ (cutoff i * n) = (-1 : k) ^ cutoff i := by
        rw [← sign_natCast, Nat.cast_mul, ZMod.natCast_eq_one_iff_odd.mpr hodd,
          mul_one, sign_natCast]
      have hd : (n - 1) / 2 = n / 2 := by omega
      rw [SKM.SYM.elvCoefficient]
      simp only [ite_eq_right hn, ite_eq_left hn1]
      rw [hd, hs, map_mul, zero_add, mul_smul_comm, (chi_commute_delta D cutoff L i hi (n / 2)).eq]

/-- The exterior linear term squares to zero before any series inversion. -/
theorem oddLinearTerm_mul_self (i : I) (hi : D.parity i = 1) :
    oddLinearTerm (k := k) D cutoff L i hi * oddLinearTerm D cutoff L i hi = 0 := by
  unfold oddLinearTerm
  rw [PowerSeries.monomial_mul_monomial]
  have hz : (((-1 : k) ^ cutoff i) • coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
      (((-1 : k) ^ cutoff i) • coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, ← pow_two, ← map_pow, SKM.SYM.delta_sq,
      map_zero, smul_zero, smul_zero]
  rw [hz, map_zero]

private theorem generatorSeries_constantCoeff (i : I) :
    PowerSeries.constantCoeff (SKM.SYM.generatorSeries k i) =
      ((1 : (MvPolynomial (I × ℕ) k)ˣ) : _) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff]

/-- The inverse elementary even series is constructed over the universal
commutative polynomial algebra before evaluation on literal A/T. -/
def elementaryEvenInverse (i : I) : PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  PowerSeries.map (polynomialToPower D cutoff L).toRingHom
    (PowerSeries.expand 2 (by decide) (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1))

theorem elementaryEvenSeries_mul_inverse (i : I) :
    elementaryEvenSeries (k := k) D cutoff L i * elementaryEvenInverse D cutoff L i = 1 := by
  unfold elementaryEvenSeries elementaryEvenInverse
  rw [← map_mul, ← map_mul, PowerSeries.mul_invOfUnit _ _ (generatorSeries_constantCoeff (k := k) i),
    map_one, map_one]

/-- The complete actual remainder series has its original exterior linear
factor on the left of the mapped inverse elementary series. -/
theorem remainderSeries_factor (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) :
    remainderSeries D Sc cutoff L i hN =
      (1 - oddLinearTerm D cutoff L i hi) * elementaryEvenInverse D cutoff L i := by
  have hlin : (1 + oddLinearTerm (k := k) D cutoff L i hi) *
      (1 - oddLinearTerm D cutoff L i hi) = 1 := by
    simp only [mul_sub, add_mul, mul_one, one_mul, oddLinearTerm_mul_self D cutoff L i hi,
      add_zero, add_sub_cancel_right]
  have hprod : remainderPolynomial (k := k) D cutoff L i *
      ((1 - oddLinearTerm D cutoff L i hi) * elementaryEvenInverse D cutoff L i) = 1 := by
    rw [remainderPolynomial_factor D cutoff L i hi, mul_assoc,
      ← mul_assoc (1 + oddLinearTerm D cutoff L i hi), hlin, one_mul,
      elementaryEvenSeries_mul_inverse D cutoff L i]
  have hC : PowerSeries.constantCoeff (remainderPolynomial (k := k) D cutoff L i) =
      ((1 : (CoefficientPowerQuotient (k := k) D cutoff L)ˣ) : _) :=
    remainderPolynomial_constantCoeff D Sc cutoff L i hi hN
  calc
    _ = remainderSeries D Sc cutoff L i hN *
        (remainderPolynomial D cutoff L i *
          ((1 - oddLinearTerm D cutoff L i hi) * elementaryEvenInverse D cutoff L i)) := by
      rw [hprod, mul_one]
    _ = _ := by
      rw [← mul_assoc, remainderSeries_eq_invOfUnit D Sc cutoff L i hi hN,
        PowerSeries.invOfUnit_mul _ _ hC, one_mul]

private theorem elementaryEvenInverse_even (i : I) (r : ℕ) :
    PowerSeries.coeff (2 * r) (elementaryEvenInverse (k := k) D cutoff L i) =
      polynomialToPower D cutoff L (PowerSeries.coeff r
        (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1)) := by
  rw [elementaryEvenInverse, PowerSeries.coeff_map, PowerSeries.coeff_expand_mul]
  rfl

private theorem elementaryEvenInverse_odd (i : I) (r : ℕ) :
    PowerSeries.coeff (2 * r + 1) (elementaryEvenInverse (k := k) D cutoff L i) = 0 := by
  have hn : ¬ 2 ∣ 2 * r + 1 := by
    intro h
    have hm := Nat.dvd_iff_mod_eq_zero.mp h
    omega
  rw [elementaryEvenInverse, PowerSeries.coeff_map,
    PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ hn, map_zero]

private theorem coeff_monomial_mul {A : Type u} [Semiring A]
    (n l : ℕ) (a : A) (f : PowerSeries A) :
    PowerSeries.coeff l (PowerSeries.monomial n a * f) =
      if n ≤ l then a * PowerSeries.coeff (l - n) f else 0 := by
  change MvPowerSeries.coeff (Finsupp.single () l)
    (MvPowerSeries.monomial (Finsupp.single () n) a * f) = _
  rw [MvPowerSeries.coeff_monomial_mul]
  simp only [Finsupp.single_le_single, ← Finsupp.single_tsub]
  rfl

private theorem oddLinearTerm_mul_coeff_succ (i : I) (hi : D.parity i = 1) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      (oddLinearTerm (k := k) D cutoff L i hi * elementaryEvenInverse D cutoff L i) =
      (((-1 : k) ^ cutoff i) • coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
        PowerSeries.coeff n (elementaryEvenInverse D cutoff L i) := by
  rw [oddLinearTerm, coeff_monomial_mul, ite_eq_left (by omega : 1 ≤ n + 1), Nat.add_sub_cancel]

private theorem oddLinearTerm_mul_even (i : I) (hi : D.parity i = 1) (r : ℕ) :
    PowerSeries.coeff (2 * r)
      (oddLinearTerm (k := k) D cutoff L i hi * elementaryEvenInverse D cutoff L i) = 0 := by
  cases r with
  | zero => rw [mul_zero, oddLinearTerm, coeff_monomial_mul, ite_eq_right (by decide : ¬ 1 ≤ 0)]
  | succ r =>
    rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega,
      oddLinearTerm_mul_coeff_succ, elementaryEvenInverse_odd, mul_zero]

/-- Even ordinary remainder coefficients are the mapped coefficients of
1/C(w²). The statement concerns the constructed inverse-row remainder. -/
theorem remainder_even (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    remainder D Sc cutoff L i hN (2 * r) =
      polynomialToPower (k := k) D cutoff L (PowerSeries.coeff r
        (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1)) := by
  have h := congrArg (PowerSeries.coeff (2 * r)) (remainderSeries_factor D Sc cutoff L i hi hN)
  rw [remainderSeries, PowerSeries.coeff_mk, sub_mul, one_mul, map_sub,
    elementaryEvenInverse_even, oddLinearTerm_mul_even, sub_zero] at h
  exact h

/-- Odd ordinary remainder coefficients retain the original left exterior
factor and the sign (−1)^(N+1). -/
theorem remainder_odd (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    remainder D Sc cutoff L i hN (2 * r + 1) =
      (-1 : k) ^ (cutoff i + 1) •
        (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
          polynomialToPower D cutoff L (PowerSeries.coeff r
            (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1))) := by
  have h := congrArg (PowerSeries.coeff (2 * r + 1)) (remainderSeries_factor D Sc cutoff L i hi hN)
  rw [remainderSeries, PowerSeries.coeff_mk, sub_mul, one_mul, map_sub,
    elementaryEvenInverse_odd, oddLinearTerm_mul_coeff_succ, elementaryEvenInverse_even,
    zero_sub, smul_mul_assoc] at h
  rw [pow_succ, mul_neg, mul_one]
  exact h.trans (neg_smul ((-1 : k) ^ cutoff i)
    (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
      polynomialToPower D cutoff L (PowerSeries.coeff r
        (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1)))).symm

private theorem rescale_inverse (i : I) :
    PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k)
      (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1) =
      PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1 := by
  let A := PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k) (SKM.SYM.generatorSeries k i)
  let B := PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k)
    (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1)
  have hAB : A * B = 1 := by
    change PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k) _ *
      PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k) _ = 1
    rw [← map_mul, PowerSeries.mul_invOfUnit _ _ (generatorSeries_constantCoeff (k := k) i), map_one]
  have hA : PowerSeries.constantCoeff A = ((1 : (MvPolynomial (I × ℕ) k)ˣ) : _) := by
    change PowerSeries.constantCoeff (PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k) _) = _
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, generatorSeries_constantCoeff]
  calc
    B = (PowerSeries.invOfUnit A 1 * A) * B := by rw [PowerSeries.invOfUnit_mul _ _ hA, one_mul]
    _ = PowerSeries.invOfUnit A 1 := by rw [mul_assoc, hAB, mul_one]

/-- The literal coefficient of 1/C(−z), formed in the commutative
polynomial algebra and then mapped to the actual coefficient power quotient. -/
def completeCoefficient (i : I) (r : ℕ) : CoefficientPowerQuotient (k := k) D cutoff L :=
  polynomialToPower D cutoff L (PowerSeries.coeff r (PowerSeries.invOfUnit
    (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1))

private theorem completeCoefficient_eq (i : I) (r : ℕ) :
    completeCoefficient (k := k) D cutoff L i r =
      (-1 : k) ^ r • polynomialToPower D cutoff L
        (PowerSeries.coeff r (PowerSeries.invOfUnit (SKM.SYM.generatorSeries k i) 1)) := by
  rw [completeCoefficient, ← rescale_inverse (k := k) i, PowerSeries.coeff_rescale]
  have hs : (-1 : MvPolynomial (I × ℕ) k) ^ r =
      (-1 : k) ^ r • (1 : MvPolynomial (I × ℕ) k) := by
    rw [Algebra.smul_def, mul_one, map_pow, map_neg, map_one]
  rw [hs, smul_mul_assoc, one_mul, map_smul]

private theorem choose_even_parity (r : ℕ) :
    (((2 * r).choose 2 : ℕ) : ZMod 2) = (r : ZMod 2) := by
  by_cases hr : r = 0
  · subst r
    simp
  · have he : (2 * r).choose 2 = r * (2 * r - 1) := by
      rw [Nat.choose_two_right]
      rw [show 2 * r * (2 * r - 1) = (r * (2 * r - 1)) * 2 by ring, Nat.mul_div_cancel]
      omega
    rw [he, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * r), Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
    simp only [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_sub,
      show -(1 : ZMod 2) = 1 from rfl, mul_one]

private theorem choose_odd_parity (r : ℕ) :
    (((2 * r + 1).choose 2 : ℕ) : ZMod 2) = (r : ZMod 2) := by
  have h : (2 * r + 1).choose 2 = 2 * r + (2 * r).choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ (2 * r) 1
  rw [h, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, choose_even_parity]
  simp only [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]

/-- Every even-index normalized reservoir moment is the actual mapped
coefficient of 1/C(−z), as in equation (7) of the written proof. -/
theorem signedMoment_even (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    signedMoment D Sc cutoff L i hN (cutoff i - 1 + 2 * r) =
      completeCoefficient D cutoff L i r := by
  rw [signedMoment_remainder D Sc cutoff L i hi hN, choose_even_parity,
    remainder_even D Sc cutoff L i hi hN, sign_natCast]
  exact (completeCoefficient_eq D cutoff L i r).symm

/-- Every odd-index normalized reservoir moment retains its independent
exterior generator on the left, with the prescribed sign (−1)^(N+1). -/
theorem signedMoment_odd (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    signedMoment D Sc cutoff L i hN (cutoff i - 1 + (2 * r + 1)) =
      (-1 : k) ^ (cutoff i + 1) •
        (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
          completeCoefficient D cutoff L i r) := by
  rw [signedMoment_remainder D Sc cutoff L i hi hN, choose_odd_parity,
    remainder_odd D Sc cutoff L i hi hN, sign_natCast, completeCoefficient_eq]
  simp only [mul_smul_comm, smul_smul]
  rw [mul_comm ((-1 : k) ^ r) ((-1 : k) ^ (cutoff i + 1))]

end OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
