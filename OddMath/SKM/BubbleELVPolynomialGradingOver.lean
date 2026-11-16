/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleELVPolynomialGrading
import OddMath.SKM.BubbleCoefficientGradedBase

/-!
# Degrees of the cyclotomic coefficients over a graded base ring

The coefficients of the first-position cyclotomic relations have the same degrees for the
coefficientwise grading `coefficientDegreePartOver` of `SYM D R` over a graded base ring as for
`coefficientDegreePart` over a ring: the generators are basis vectors, and the monic
normalization only changes signs. For `K = R` with the trivial grading these are the statements
of `OddMath.SKM.BubbleELVPolynomialGrading`.
-/

noncomputable section

namespace OddMath.SKM.SYM

universe u

variable {I : Type u} {X : Type u} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]

attribute [local instance] coefficientDegreeGradedAlgebraOver

theorem one_mem_coefficientDegreePartOver : (1 : SYM D R) ∈ coefficientDegreePartOver D sy 𝒜 0 :=
  SetLike.GradedOne.one_mem

theorem delta_mem_coefficientDegreePartOver (i : {i : I // D.parity i = 1}) :
    delta D R i ∈ coefficientDegreePartOver D sy 𝒜 (2 * sy.d i.1) := by
  have h := coefficientBasis_mem_over (sy := sy) (𝒜 := 𝒜) ((0, {i}) : CoefficientIndex D)
  rw [coefficientBasis_delta] at h
  simpa [coefficientDegree] using h

theorem elementary_mem_coefficientDegreePartOver (i : I) (r : ℕ) :
    e D R i r ∈ coefficientDegreePartOver D sy 𝒜 (2 * sy.d i * elementaryWeight D (i, r)) := by
  have h := coefficientBasis_mem_over (sy := sy) (𝒜 := 𝒜)
    ((Finsupp.single (i, r) 1, ∅) : CoefficientIndex D)
  rw [coefficientBasis_elementary] at h
  simpa [coefficientDegree] using h

omit [GradedAlgebra 𝒜] in
/-- A sign does not change the degree. -/
theorem neg_one_pow_smul_mem_coefficientDegreePartOver {n : ℤ} {x : SYM D R}
    (hx : x ∈ coefficientDegreePartOver D sy 𝒜 n) (m : ℕ) :
    (-1 : R) ^ m • x ∈ coefficientDegreePartOver D sy 𝒜 n := by
  rcases neg_one_pow_eq_or R m with h | h
  · simpa [h] using hx
  · rw [h, neg_one_smul R x]
    exact Submodule.neg_mem _ hx

theorem elvChi_mem_coefficientDegreePartOver (i : {i : I // D.parity i = 1}) (r : ℕ) :
    elvChi D R i r ∈ coefficientDegreePartOver D sy 𝒜 (2 * sy.d i.1 * ((2 * r : ℕ) : ℤ)) := by
  cases r with
  | zero => simpa [elvChi] using one_mem_coefficientDegreePartOver D sy 𝒜
  | succ r =>
    simpa [elvChi, elementaryWeight, i.property] using
      elementary_mem_coefficientDegreePartOver D sy 𝒜 i.1 r

theorem elvCoefficient_mem_coefficientDegreePartOver (i : {i : I // D.parity i = 1}) (n : ℕ) :
    elvCoefficient D R i n ∈ coefficientDegreePartOver D sy 𝒜 (2 * sy.d i.1 * (n : ℤ)) := by
  unfold elvCoefficient
  split_ifs with he
  · have hn : 2 * (n / 2) = n := by omega
    simpa only [hn] using elvChi_mem_coefficientDegreePartOver D sy 𝒜 i (n / 2)
  · have hn : 1 + 2 * (n / 2) = n := by omega
    have hdegree : 2 * sy.d i.1 + 2 * sy.d i.1 * ((2 * (n / 2) : ℕ) : ℤ) =
        2 * sy.d i.1 * (n : ℤ) := by
      calc
        _ = 2 * sy.d i.1 * ((1 + 2 * (n / 2) : ℕ) : ℤ) := by push_cast; ring
        _ = _ := by rw [hn]
    simpa only [hdegree] using coefficientDegreePartOver_mul
      (delta_mem_coefficientDegreePartOver D sy 𝒜 i)
      (elvChi_mem_coefficientDegreePartOver D sy 𝒜 i (n / 2))

/-- The odd monic coefficient of the `a`-th dot power has the complementary degree. -/
theorem elvMonicCoefficient_mem_coefficientDegreePartOver (i : {i : I // D.parity i = 1})
    (N : ℕ) (a : Fin (N + 1)) :
    elvMonicCoefficient D R i N a ∈ coefficientDegreePartOver D sy 𝒜
      (2 * sy.d i.1 * ((N : ℤ) - (a.val : ℤ))) := by
  have ha : a.val ≤ N := Nat.le_of_lt_succ a.isLt
  have h := neg_one_pow_smul_mem_coefficientDegreePartOver D sy 𝒜
    (elvCoefficient_mem_coefficientDegreePartOver D sy 𝒜 i (N - a.val)) (N * (a.val + 1))
  simpa only [elvMonicCoefficient, Nat.cast_sub ha] using h

theorem evenCyclotomicCoefficient_mem_coefficientDegreePartOver (i : I) (hi : D.parity i = 0)
    (n : ℕ) :
    evenCyclotomicCoefficient D R i n ∈ coefficientDegreePartOver D sy 𝒜 (2 * sy.d i * (n : ℤ)) := by
  cases n with
  | zero => simpa [evenCyclotomicCoefficient] using one_mem_coefficientDegreePartOver D sy 𝒜
  | succ r =>
    simpa [evenCyclotomicCoefficient, elementaryWeight, hi] using
      elementary_mem_coefficientDegreePartOver D sy 𝒜 i r

/-- The even monic coefficient of the `a`-th dot power has the complementary degree. -/
theorem evenMonicCoefficient_mem_coefficientDegreePartOver (i : I) (hi : D.parity i = 0)
    (N : ℕ) (a : Fin (N + 1)) :
    evenMonicCoefficient D R i N a ∈ coefficientDegreePartOver D sy 𝒜
      (2 * sy.d i * ((N : ℤ) - (a.val : ℤ))) := by
  have ha : a.val ≤ N := Nat.le_of_lt_succ a.isLt
  have h := neg_one_pow_smul_mem_coefficientDegreePartOver D sy 𝒜
    (evenCyclotomicCoefficient_mem_coefficientDegreePartOver D sy 𝒜 i hi (N - a.val)) (N - a.val)
  simpa only [evenMonicCoefficient, Nat.cast_sub ha] using h

end OddMath.SKM.SYM
