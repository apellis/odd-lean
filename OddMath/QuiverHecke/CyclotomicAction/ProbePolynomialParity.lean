import OddMath.QuiverHecke.CyclotomicAction.ProbeFirstDot
import OddMath.QuiverHecke.CyclotomicAction.Parity
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Parity of the actual cofinal probe polynomials

Odd-colour probes have support in even exponents. This gives the exact
polynomial-parity input of the existing cyclotomic supermodule construction,
over an arbitrary commutative ring, including the zero polynomial/ring cases.
-/
noncomputable section
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k]

/-- The cofinal binomial probe is a polynomial expansion. -/
theorem probePolynomial_eq_expand (e m : I → ℕ) (i : I) :
    (probePolynomial e m i : Polynomial k) =
      Polynomial.expand k (e i) ((Polynomial.X - 1) ^ m i) := by
  simp only [probePolynomial, map_pow, map_sub, Polynomial.expand_X, map_one]

/-- Every nonzero coefficient has exponent divisible by the chosen probe step. -/
theorem probePolynomial_support_dvd (e m : I → ℕ) (i : I)
    (he : 0 < e i) {n : ℕ}
    (hn : (probePolynomial e m i : Polynomial k).coeff n ≠ 0) :
    e i ∣ n := by
  by_contra hd
  apply hn
  rw [probePolynomial_eq_expand, Polynomial.coeff_expand he, ite_eq_right hd]

private theorem probe_parity_cases (p : ZMod 2) : p = 0 ∨ p = 1 := by
  fin_cases p
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The prescribed odd/even cofinal probes supply the actual supermodule
polynomial-parity premise, without a nontriviality or finite-colour hypothesis. -/
theorem probePolynomial_parity (D : SKM.Datum I X) (m : I → ℕ) :
    CyclotomicPolynomialParity (k := k) D
      (probePolynomial (probeDotExponent D) m) := by
  intro i n hn
  rcases probe_parity_cases (D.parity i) with hi | hi
  · simp only [hi, nsmul_zero]
  · have he : probeDotExponent D i = 2 := by simp [probeDotExponent, hi]
    have hd : 2 ∣ n := by
      simpa only [he] using
        (probePolynomial_support_dvd (probeDotExponent D) m i
          (by rw [he]; decide) hn)
    rw [probePolynomial_eq_expand, Polynomial.natDegree_expand, hi, he]
    obtain ⟨r, rfl⟩ := hd
    have hz : (2 : ℕ) • (1 : ZMod 2) = 0 := by decide
    simp only [Nat.mul_comm 2 r, mul_smul, hz, smul_zero]

end OddMath.QuiverHecke
