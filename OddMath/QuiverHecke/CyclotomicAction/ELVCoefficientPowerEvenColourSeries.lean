import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerOddSeries

/-! # Reservoir moments of an even moving colour on the power vacuum

The even-colour counterpart of `ELVCoefficientPowerOddSeries`
(`SwappedVacuumNonpositiveBubbles.md`, §2). For `D.parity i = 0` the signed
and raw moments agree, the actual one-strand relation is the reversed series
`E(-w) = Σₙ (-1)ⁿ eₙ wⁿ` (truncated by the cutoff relations of A/T), and the
higher reservoir moments are the coefficients of `1/E(-w)`:
`signedMoment (N - 1 + r) = completeCoefficient r`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem coeff_monomial_mul_even {A : Type u} [Semiring A]
    (n l : ℕ) (a : A) (f : PowerSeries A) :
    PowerSeries.coeff l (PowerSeries.monomial n a * f) =
      if n ≤ l then a * PowerSeries.coeff (l - n) f else 0 := by
  change MvPowerSeries.coeff (Finsupp.single () l)
    (MvPowerSeries.monomial (Finsupp.single () n) a * f) = _
  rw [MvPowerSeries.coeff_monomial_mul]
  simp only [Finsupp.single_le_single, ← Finsupp.single_tsub]
  rfl

/-- For an even colour the triangular dot sign is trivial. -/
theorem even_signedMoment_rawMoment (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) (n : ℕ) :
    signedMoment D Sc cutoff L i hN n = rawMoment D Sc cutoff L i hN 1 n := by
  rw [signedMoment_rawMoment, hi]
  simp only [inductionUnitDotSign, smul_zero, Supercategory.sign_zero, one_smul]

/-- The actual one-strand relation, with no Koszul sign for an even colour. -/
theorem even_rawMoment_recurrence (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1),
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (singleCoefficient D cutoff i j) * rawMoment D Sc cutoff L i hN 1 (j.val + m)) = 0 := by
  have h := rawMoment_one_recurrence D Sc cutoff L i hN m
  rw [hi] at h
  simpa only [smul_zero, mul_zero, sub_zero, koszulSign_zero_left, one_smul] using h

/-- The low window of the actual even inverse row. -/
theorem even_rawMoment_window (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i)
    (n : ℕ) (hn : n < cutoff i) :
    rawMoment D Sc cutoff L i hN 1 n = if n + 1 = cutoff i then 1 else 0 := by
  rw [rawMoment_one_window D Sc cutoff L i hN n hn, hi]
  simp only [inductionUnitDotSign, smul_zero, Supercategory.sign_zero, one_smul]

/-- The even-colour top remainders at exponents N−1+l. -/
def evenRemainder (i : I) (hN : 0 < cutoff i) (l : ℕ) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  rawMoment D Sc cutoff L i hN 1 (cutoff i - 1 + l)

/-- Their complete series. -/
def evenRemainderSeries (i : I) (hN : 0 < cutoff i) :
    PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  PowerSeries.mk (evenRemainder D Sc cutoff L i hN)

theorem evenRemainder_zero (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) :
    evenRemainder D Sc cutoff L i hN 0 = 1 := by
  have h := even_rawMoment_window D Sc cutoff L i hi hN (cutoff i - 1) (by omega)
  have ht : cutoff i - 1 + 1 = cutoff i := by omega
  simpa only [evenRemainder, Nat.add_zero, ite_eq_left ht] using h

theorem evenRemainder_recurrence (i : I) (hi : D.parity i = 0)
    (hN : 0 < cutoff i) (l : ℕ) (hl : 0 < l) :
    (∑ j : Fin (cutoff i + 1),
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (singleCoefficient D cutoff i j) *
          (if cutoff i - j.val ≤ l then evenRemainder D Sc cutoff L i hN (l - (cutoff i - j.val))
           else 0)) = 0 := by
  calc
    _ = ∑ j : Fin (cutoff i + 1),
        (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
          (singleCoefficient D cutoff i j) * rawMoment D Sc cutoff L i hN 1 (j.val + (l - 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      by_cases hj : cutoff i - j.val ≤ l
      · rw [ite_eq_left hj, evenRemainder]
        congr 1
        have hv := j.isLt
        omega
      · rw [ite_eq_right hj]
        have hv := j.isLt
        have he := even_rawMoment_window D Sc cutoff L i hi hN (j.val + (l - 1)) (by omega)
        have ht : ¬ j.val + (l - 1) + 1 = cutoff i := by omega
        simpa only [ite_eq_right ht] using he.symm
    _ = 0 := even_rawMoment_recurrence D Sc cutoff L i hi hN (l - 1)

/-- The reversed monic relation inverts the actual even remainder series. -/
theorem remainderPolynomial_mul_evenRemainderSeries (i : I) (hi : D.parity i = 0)
    (hN : 0 < cutoff i) :
    remainderPolynomial D cutoff L i * evenRemainderSeries D Sc cutoff L i hN = 1 := by
  classical
  apply PowerSeries.ext
  intro l
  simp only [remainderPolynomial, evenRemainderSeries, Finset.sum_mul, map_sum,
    coeff_monomial_mul_even, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  by_cases hl : l = 0
  · subst l
    rw [ite_eq_left rfl]
    rw [Finset.sum_eq_single (Fin.last (cutoff i))]
    · simp only [Fin.val_last, Nat.sub_self, le_refl, ↓reduceIte,
        singleCoefficient_top, map_one, evenRemainder_zero D Sc cutoff L i hi hN, mul_one]
    · intro j _ hj
      have hne : j.val ≠ cutoff i := by
        intro h
        apply hj
        exact Fin.ext h
      have hv := j.isLt
      rw [ite_eq_right (by omega : ¬ cutoff i - j.val ≤ 0)]
    · simp
  · rw [ite_eq_right hl]
    simpa only [mul_ite, mul_zero] using evenRemainder_recurrence D Sc cutoff L i hi hN l (by omega)

private theorem even_reversed_coefficient (i : I) (hi : D.parity i = 0)
    (n : ℕ) (hn : n ≤ cutoff i) :
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (singleCoefficient D cutoff i ⟨cutoff i - n, by omega⟩) =
      (-1 : k) ^ n • coefficientPowerQuotientMap (k := k) D cutoff L
        (SKM.SYM.evenCyclotomicCoefficient D k i n) := by
  have h1 : ¬ D.parity i = 1 := by rw [hi]; decide
  unfold singleCoefficient
  rw [dite_eq_right h1, SKM.SYM.evenMonicCoefficient, map_smul, map_smul]
  rw [show cutoff i - (cutoff i - n) = n by omega]
  rfl

private theorem even_coefficient_tail (i : I) (hi : D.parity i = 0)
    (n : ℕ) (hn : cutoff i < n) :
    coefficientPowerQuotientMap (k := k) D cutoff L
      (SKM.SYM.evenCyclotomicCoefficient D k i n) = 0 := by
  apply (coefficientPowerQuotientMap_eq_zero_iff D cutoff L _).mpr
  apply TwoSidedIdeal.mem_sup_left
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  apply TwoSidedIdeal.subset_span
  refine Or.inl ⟨i, r, ?_, rfl⟩
  rw [SKM.SYM.elvElementaryRank, ite_eq_left hi]
  omega

private theorem polynomial_generatorCoeff_even (i : I) (n : ℕ) :
    polynomialToPower (k := k) D cutoff L (PowerSeries.coeff n (SKM.SYM.generatorSeries k i)) =
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.evenCyclotomicCoefficient D k i n) := by
  cases n with
  | zero =>
    simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff, SKM.SYM.evenCyclotomicCoefficient]
  | succ n =>
    simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff, SKM.SYM.evenCyclotomicCoefficient,
      polynomialToPower, AlgHom.comp_apply]

/-- For an even colour the reversed actual monic relation is the mapped
series `E(-w)` of the commutative polynomial algebra; the coefficients beyond
the cutoff vanish by the defining relations of A/T. -/
theorem even_remainderPolynomial (i : I) (hi : D.parity i = 0) :
    remainderPolynomial (k := k) D cutoff L i =
      PowerSeries.map (polynomialToPower D cutoff L).toRingHom
        (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) := by
  classical
  apply PowerSeries.ext
  intro n
  have hs : (-1 : MvPolynomial (I × ℕ) k) ^ n =
      (-1 : k) ^ n • (1 : MvPolynomial (I × ℕ) k) := by
    rw [Algebra.smul_def, mul_one, map_pow, map_neg, map_one]
  have hr : PowerSeries.coeff n (PowerSeries.map (polynomialToPower (k := k) D cutoff L).toRingHom
      (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i))) =
      (-1 : k) ^ n • coefficientPowerQuotientMap D cutoff L
        (SKM.SYM.evenCyclotomicCoefficient D k i n) := by
    rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, hs, smul_mul_assoc, one_mul]
    change polynomialToPower (k := k) D cutoff L _ = _
    rw [map_smul, polynomial_generatorCoeff_even]
  rw [hr, remainderPolynomial, map_sum]
  by_cases hn : n ≤ cutoff i
  · let j : Fin (cutoff i + 1) := ⟨cutoff i - n, by omega⟩
    rw [Finset.sum_eq_single j]
    · rw [PowerSeries.coeff_monomial, ite_eq_left (by dsimp [j]; omega)]
      exact even_reversed_coefficient D cutoff L i hi n hn
    · intro b _ hb
      rw [PowerSeries.coeff_monomial, ite_eq_right]
      intro he
      apply hb
      apply Fin.ext
      have hv := b.isLt
      dsimp [j]
      omega
    · simp
  · rw [even_coefficient_tail D cutoff L i hi n (by omega), smul_zero]
    apply Finset.sum_eq_zero
    intro j _
    rw [PowerSeries.coeff_monomial, ite_eq_right (by have hv := j.isLt; omega)]

private theorem rescaled_generator_constantCoeff (i : I) :
    PowerSeries.constantCoeff (PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k)
      (SKM.SYM.generatorSeries k i)) = ((1 : (MvPolynomial (I × ℕ) k)ˣ) : _) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
    one_mul]
  simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff]

/-- The actual even remainder series is the mapped inverse of `E(-w)`. -/
theorem evenRemainderSeries_eq (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) :
    evenRemainderSeries D Sc cutoff L i hN =
      PowerSeries.map (polynomialToPower D cutoff L).toRingHom
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1) := by
  have hQP : PowerSeries.map (polynomialToPower (k := k) D cutoff L).toRingHom
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1) *
      remainderPolynomial D cutoff L i = 1 := by
    rw [even_remainderPolynomial D cutoff L i hi, ← map_mul,
      PowerSeries.invOfUnit_mul _ _ (rescaled_generator_constantCoeff (k := k) i), map_one]
  calc
    _ = (PowerSeries.map (polynomialToPower (k := k) D cutoff L).toRingHom
          (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1) *
        remainderPolynomial D cutoff L i) * evenRemainderSeries D Sc cutoff L i hN := by
      rw [hQP, one_mul]
    _ = _ := by
      rw [mul_assoc, remainderPolynomial_mul_evenRemainderSeries D Sc cutoff L i hi hN, mul_one]

/-- Every higher reservoir moment of an even colour is the actual mapped
coefficient of `1/E(-z)`. -/
theorem even_colour_signedMoment (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) (r : ℕ) :
    signedMoment D Sc cutoff L i hN (cutoff i - 1 + r) =
      completeCoefficient D cutoff L i r := by
  rw [even_signedMoment_rawMoment D Sc cutoff L i hi hN]
  have h := congrArg (PowerSeries.coeff r) (evenRemainderSeries_eq D Sc cutoff L i hi hN)
  rw [evenRemainderSeries, PowerSeries.coeff_mk, PowerSeries.coeff_map] at h
  exact h

end OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
