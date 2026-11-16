/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleCoefficientGrading

/-! # Integer degrees of the ELV monic coefficients

Supporting the integer-graded coefficient action of `DeformedGradedAction.md` §1,
we compute the symmetrizer degrees of the polynomial coefficients defined in
`BubbleELVCoefficients`. These are integer degrees, independent of super parity.
-/

noncomputable section
open scoped Classical
namespace OddMath.SKM.SYM

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k] (sy : Symmetrizer D)

/-- The odd-colour elementary coefficient `chi_r` has dot weight `2r`. -/
theorem elvChi_mem_coefficientDegreePart
    (i : {i : I // D.parity i = 1}) (r : ℕ) :
    elvChi D k i r ∈ coefficientDegreePart D k sy
      (2 * sy.d i.1 * ((2 * r : ℕ) : ℤ)) := by
  cases r with
  | zero =>
    simpa [elvChi] using
      (SetLike.GradedOne.one_mem : (1 : SYM D k) ∈ coefficientDegreePart D k sy 0)
  | succ r =>
    simpa [elvChi, elementaryWeight, i.property] using
      elementary_mem_coefficientDegreePart D k sy i.1 r

/-- Both even and odd indices have the degree given by their dot weight. -/
theorem elvCoefficient_mem_coefficientDegreePart
    (i : {i : I // D.parity i = 1}) (n : ℕ) :
    elvCoefficient D k i n ∈ coefficientDegreePart D k sy (2 * sy.d i.1 * (n : ℤ)) := by
  unfold elvCoefficient
  split_ifs with he
  · have hn : 2 * (n / 2) = n := by omega
    simpa only [hn] using elvChi_mem_coefficientDegreePart D k sy i (n / 2)
  · have hn : 1 + 2 * (n / 2) = n := by omega
    have hdegree : 2 * sy.d i.1 + 2 * sy.d i.1 * ((2 * (n / 2) : ℕ) : ℤ) =
        2 * sy.d i.1 * (n : ℤ) := by
      calc
        _ = 2 * sy.d i.1 * ((1 + 2 * (n / 2) : ℕ) : ℤ) := by push_cast; ring
        _ = _ := by rw [hn]
    simpa only [hdegree] using coefficientDegreePart_mul D k sy
      (delta_mem_coefficientDegreePart D k sy i)
      (elvChi_mem_coefficientDegreePart D k sy i (n / 2))

/-- The coefficient of the `a`-th dot power has the complementary integer degree.
The scalar sign used in monic normalization does not change that degree. -/
theorem elvMonicCoefficient_mem_coefficientDegreePart
    (i : {i : I // D.parity i = 1}) (N : ℕ) (a : Fin (N + 1)) :
    elvMonicCoefficient D k i N a ∈ coefficientDegreePart D k sy
      (2 * sy.d i.1 * ((N : ℤ) - (a.val : ℤ))) := by
  have ha : a.val ≤ N := Nat.le_of_lt_succ a.isLt
  have h := Submodule.smul_mem (coefficientDegreePart D k sy
      (2 * sy.d i.1 * ((N - a.val : ℕ) : ℤ)))
    ((-1 : k) ^ (N * (a.val + 1)))
    (elvCoefficient_mem_coefficientDegreePart D k sy i (N - a.val))
  simpa only [elvMonicCoefficient, Nat.cast_sub ha] using h

/-- Ordinary elementary coefficients have their usual dot weight at an even colour. -/
theorem evenCyclotomicCoefficient_mem_coefficientDegreePart
    (i : I) (hi : D.parity i = 0) (n : ℕ) :
    evenCyclotomicCoefficient D k i n ∈ coefficientDegreePart D k sy
      (2 * sy.d i * (n : ℤ)) := by
  cases n with
  | zero =>
    simpa [evenCyclotomicCoefficient] using
      (SetLike.GradedOne.one_mem : (1 : SYM D k) ∈ coefficientDegreePart D k sy 0)
  | succ r =>
    simpa [evenCyclotomicCoefficient, elementaryWeight, hi] using
      elementary_mem_coefficientDegreePart D k sy i r

/-- Even monic coefficients have the complementary integer degree. -/
theorem evenMonicCoefficient_mem_coefficientDegreePart
    (i : I) (hi : D.parity i = 0) (N : ℕ) (a : Fin (N + 1)) :
    evenMonicCoefficient D k i N a ∈ coefficientDegreePart D k sy
      (2 * sy.d i * ((N : ℤ) - (a.val : ℤ))) := by
  have ha : a.val ≤ N := Nat.le_of_lt_succ a.isLt
  have h := Submodule.smul_mem (coefficientDegreePart D k sy
      (2 * sy.d i * ((N - a.val : ℕ) : ℤ)))
    ((-1 : k) ^ (N - a.val))
    (evenCyclotomicCoefficient_mem_coefficientDegreePart D k sy i hi (N - a.val))
  simpa only [evenMonicCoefficient, Nat.cast_sub ha] using h

end OddMath.SKM.SYM
