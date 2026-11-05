import OddMath.QuiverHecke.CyclotomicAction.ELVScalarPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ProbeFirstDot
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Coeff

/-! # Binomial scalar specialization of ELV cyclotomic coefficients
This gives the prescribed colourwise probe specialization of
InvertibleDotProbe.md Section 1: odd exterior parameters vanish, and the
elementary parameters specialize to binomial coefficients. The literal
source first-dot polynomials become the prescribed probes in both parities.
-/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.SKM.SYM
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ)

/-- The colourwise degree of the prescribed probe polynomial. -/
def probeCutoff (i : I) : ℕ := probeDotExponent D i * m i

/-- Elementary coefficient values giving the odd/even binomial probes. -/
def probeScalarValues (p : I × ℕ) : k :=
  if D.parity p.1 = 1 then
    (-1 : k) ^ (p.2 + 1) * (Nat.choose (m p.1) (p.2 + 1) : k)
  else (Nat.choose (m p.1) (p.2 + 1) : k)

theorem probeCutoff_elementaryRank (i : I) :
    elvElementaryRank D (probeCutoff D m) i = m i := by
  rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · simp [elvElementaryRank, probeCutoff, probeDotExponent, hi]
  · simp [elvElementaryRank, probeCutoff, probeDotExponent, hi, Nat.mul_comm]

theorem probeScalarValues_vanish (i : I) (r : ℕ)
    (hr : elvElementaryRank D (probeCutoff D m) i ≤ r) :
    probeScalarValues (k := k) D m (i,r) = 0 := by
  rw [probeCutoff_elementaryRank] at hr
  have hc : Nat.choose (m i) (r+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [probeScalarValues, hc]

theorem scalarEvaluation_probe_elvChi (i : {i : I // D.parity i = 1}) (r : ℕ) :
    scalarEvaluation D (probeScalarValues (k := k) D m) (elvChi D k i r) =
      (-1 : k)^r * (Nat.choose (m i.1) r : k) := by
  cases r with
  | zero => simp [elvChi]
  | succ r => simp [elvChi, probeScalarValues, i.property]

theorem scalarEvaluation_probe_evenCoefficient (i : I) (hi : D.parity i = 0) (r : ℕ) :
    scalarEvaluation D (probeScalarValues (k := k) D m) (evenCyclotomicCoefficient D k i r) =
      (Nat.choose (m i) r : k) := by
  cases r with
  | zero => simp [evenCyclotomicCoefficient]
  | succ r => simp [evenCyclotomicCoefficient, probeScalarValues, hi]

private theorem binomial_probe_coeff (N r : ℕ) :
    ((Polynomial.X - 1 : Polynomial k)^N).coeff r =
      (-1 : k)^(N-r) * (Nat.choose N r : k) := by
  simpa only [Polynomial.C_neg, Polynomial.C_1, sub_eq_add_neg] using
    Polynomial.coeff_X_add_C_pow (-1 : k) N r

private theorem odd_binomial_probe_coeff (N r : ℕ) :
    ((Polynomial.X^2 - 1 : Polynomial k)^N).coeff r =
      if 2 ∣ r then (-1 : k)^(N-r/2) * (Nat.choose N (r/2) : k) else 0 := by
  have he : (Polynomial.X^2 - 1 : Polynomial k)^N =
      Polynomial.expand k 2 ((Polynomial.X - 1)^N) := by
    simp only [map_pow, map_sub, Polynomial.expand_X, map_one]
  rw [he, Polynomial.coeff_expand (by decide)]
  simp only [binomial_probe_coeff]

private theorem scalarCoefficientPolynomial_coeff_fin (values : I × ℕ → k)
    (N : ℕ) (c : Fin (N+1) → SKM.SYM D k) (j : Fin (N+1)) :
    (scalarCoefficientPolynomial D values N c).coeff j.val = scalarEvaluation D values (c j) := by
  simp only [scalarCoefficientPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro z _ hz
    have hjz : j.val ≠ z.val := fun he => hz (Fin.ext he.symm)
    simp [hjz]
  · simp

private theorem scalarCoefficientPolynomial_coeff_large (values : I × ℕ → k)
    (N : ℕ) (c : Fin (N+1) → SKM.SYM D k) (r : ℕ) (hr : N < r) :
    (scalarCoefficientPolynomial D values N c).coeff r = 0 := by
  simp only [scalarCoefficientPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  apply Finset.sum_eq_zero
  intro j _
  have hjr : r ≠ j.val := by have := j.isLt; omega
  simp [hjr]

/-- Even source coefficients specialize to the prescribed binomial probe. -/
theorem scalarCoefficientPolynomial_probe_even (i : I) (hi : D.parity i = 0) :
    scalarCoefficientPolynomial D (probeScalarValues (k := k) D m) (m i)
      (evenMonicCoefficient D k i (m i)) = (Polynomial.X - 1)^m i := by
  apply Polynomial.ext
  intro r
  by_cases hr : r ≤ m i
  · let j : Fin (m i+1) := ⟨r, by omega⟩
    rw [show r = j.val from rfl, scalarCoefficientPolynomial_coeff_fin,
      binomial_probe_coeff]
    simp only [evenMonicCoefficient, map_smul, scalarEvaluation_probe_evenCoefficient D m i hi]
    change (-1 : k)^(m i-j.val) * (Nat.choose (m i) (m i-j.val) : k) = _
    rw [Nat.choose_symm hr]
  · rw [scalarCoefficientPolynomial_coeff_large D _ _ _ r (by omega), binomial_probe_coeff,
      Nat.choose_eq_zero_of_lt (by omega : m i < r), Nat.cast_zero, mul_zero]

private theorem probe_half_sub (N r : ℕ) (hr : r ≤ 2*N) (he : r % 2 = 0) :
    (2*N-r)/2 = N-r/2 := by omega

/-- Odd source coefficients specialize to the prescribed even-exponent binomial probe. -/
theorem scalarCoefficientPolynomial_probe_odd (i : {i : I // D.parity i = 1}) :
    scalarCoefficientPolynomial D (probeScalarValues (k := k) D m) (2*m i.1)
      (elvMonicCoefficient D k i (2*m i.1)) = (Polynomial.X^2 - 1)^m i.1 := by
  apply Polynomial.ext
  intro r
  by_cases hr : r ≤ 2*m i.1
  · let j : Fin (2*m i.1+1) := ⟨r, by omega⟩
    rw [show r = j.val from rfl, scalarCoefficientPolynomial_coeff_fin, odd_binomial_probe_coeff]
    have he : Even (2*m i.1*(j.val+1)) := ⟨m i.1*(j.val+1), by ring⟩
    simp only [elvMonicCoefficient, he.neg_one_pow, one_smul]
    by_cases hj : j.val % 2 = 0
    · have hrem : (2*m i.1-j.val) % 2 = 0 := by change r % 2 = 0 at hj; dsimp [j]; omega
      have hdiv : (2*m i.1-j.val)/2 = m i.1-j.val/2 :=
        probe_half_sub (m i.1) j.val (by change r ≤ 2*m i.1; exact hr) hj
      have hle : j.val/2 ≤ m i.1 := by dsimp [j]; omega
      rw [elvCoefficient, ite_eq_left hrem, scalarEvaluation_probe_elvChi, hdiv,
        ite_eq_left (Nat.dvd_of_mod_eq_zero hj), Nat.choose_symm hle]
    · have hrem : (2*m i.1-j.val) % 2 ≠ 0 := by dsimp [j] at *; omega
      have hnd : ¬ 2 ∣ j.val := fun hd => hj (Nat.mod_eq_zero_of_dvd hd)
      simp [elvCoefficient, hrem, hnd]
  · rw [scalarCoefficientPolynomial_coeff_large D _ _ _ r (by omega), odd_binomial_probe_coeff]
    split_ifs with hd
    · have hrem : r % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
      have hlt : m i.1 < r/2 := by omega
      rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]
    · rfl

/-- The actual monic coefficient family at the prescribed probe cutoff. -/
def probeMonicCoefficient (i : I) (j : Fin (probeCutoff D m i+1)) : SKM.SYM D k :=
  if hi : D.parity i = 1 then elvMonicCoefficient D k ⟨i,hi⟩ (probeCutoff D m i) j
  else evenMonicCoefficient D k i (probeCutoff D m i) j

private theorem scalarCoefficientPolynomial_reindex {N M : ℕ} (hNM : N = M)
    (values : I × ℕ → k) (c : Fin (N+1) → SKM.SYM D k) (d : Fin (M+1) → SKM.SYM D k)
    (hcd : ∀ j, c j = d (Fin.cast (congrArg (fun n => n+1) hNM) j)) :
    scalarCoefficientPolynomial D values N c = scalarCoefficientPolynomial D values M d := by
  subst M
  congr 1
  funext j
  simpa only [Fin.cast_refl, id_eq] using hcd j

theorem scalarCoefficientPolynomial_probe (i : I) :
    scalarCoefficientPolynomial D (probeScalarValues (k := k) D m) (probeCutoff D m i)
      (probeMonicCoefficient (k := k) D m i) = probePolynomial (k := k) (probeDotExponent D) m i := by
  rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · have hcut : probeCutoff D m i = m i := by simp [probeCutoff, probeDotExponent, hi]
    have hc : ∀ j : Fin (probeCutoff D m i+1), probeMonicCoefficient (k := k) D m i j =
        evenMonicCoefficient D k i (m i) (Fin.cast (congrArg (fun n => n+1) hcut) j) := by
      intro j
      unfold probeMonicCoefficient
      simp only [hi, zero_ne_one, ↓reduceDIte]
      unfold evenMonicCoefficient
      simp only [Fin.val_cast, hcut]
    rw [scalarCoefficientPolynomial_reindex D hcut _ _ _ hc,
      scalarCoefficientPolynomial_probe_even D m i hi]
    simp [probePolynomial, probeDotExponent, hi]
  · have hcut : probeCutoff D m i = 2*m i := by simp [probeCutoff, probeDotExponent, hi]
    have hc : ∀ j : Fin (probeCutoff D m i+1), probeMonicCoefficient (k := k) D m i j =
        elvMonicCoefficient D k ⟨i,hi⟩ (2*m i) (Fin.cast (congrArg (fun n => n+1) hcut) j) := by
      intro j
      unfold probeMonicCoefficient
      simp only [hi, ↓reduceDIte]
      unfold elvMonicCoefficient
      simp only [Fin.val_cast, hcut]
    rw [scalarCoefficientPolynomial_reindex D hcut _ _ _ hc,
      scalarCoefficientPolynomial_probe_odd D m ⟨i,hi⟩]
    simp [probePolynomial, probeDotExponent, hi]

variable (Sc : SKM.Scalars D k)

/-- The existing signed Hom specialization at the prescribed binomial values. -/
abbrev elvProbeAffineSpecialization :=
  elvAffineScalarSpecialization D Sc (probeCutoff D m) (probeScalarValues (k := k) D m)
    (probeScalarValues_vanish D m)

end OddMath.QuiverHecke
