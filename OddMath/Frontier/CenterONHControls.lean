import OddMath.Frontier.NilHeckeCenter
import OddMath.Frontier.ElementaryGeneration

/-!
Hand-checked controls on the actual carrier `SkewPolynomial`, written before the
all-rank center theorem `CenterONH`.

* Rank two (`N = 2`, `n = 0`): the tilde elementary polynomials are
  `e₁ = x₀ - x₁`, `e₂ = -(x₀ x₁)`, both in the kernel, and the first variable is a
  root of the left relation `x₀² - e₁ x₀ - e₂ = 0` used in `CenterONH`
  (coefficients `c₀ = 1, c₁ = -1, c₂ = -1`).
* Rank two: `x₀² + x₁²` lies in the kernel and in the center of `Pol₂`
  (a nonzero element of the candidate `S₂`).
* Rank two: `x₀ x₁` lies in the kernel but is not central in `Pol₂`
  (so the center of the kernel is a proper sub-object; inherited control).
* Rank three: the volume `x₀ x₁ x₂` is central in the kernel AND in `Pol₃`
  but is not a polynomial in the squares (the odd summand `V·S₃`; inherited).
-/

namespace OddMath.Frontier.CenterONHControls
open OddMath.SkewPolynomial (SkewPolynomial generator generator_anticommute)
open OddMath.Frontier.AllRankDivided OddMath.Frontier.OddSymmetricKernel
open OddMath.Frontier.FiniteCompleteElementary OddMath.Frontier.PlacticEvaluation

private theorem anti01 :
    (generator (0 : Fin 2) : SkewPolynomial 2) * generator 1 =
      -(generator 1 * generator 0) :=
  generator_anticommute 0 1 (by decide)

theorem tilde_zero_rankTwo : tildeGenerator (0 : Fin 2) = generator 0 := by
  simp [tildeGenerator]

theorem tilde_one_rankTwo : tildeGenerator (1 : Fin 2) = -generator 1 := by
  simp [tildeGenerator]

theorem e1_rankTwo : elementaryPoly 2 1 = generator 0 - generator 1 := by
  rw [elementaryPoly_eq_strictSum, FiniteWords.strictSum_succ,
    FiniteWords.strictSum_succ (fun i : Fin 1 => tildeGenerator i.succ)]
  simp [tildeGenerator, sub_eq_add_neg]

theorem e2_rankTwo : elementaryPoly 2 2 = -(generator 0 * generator 1) := by
  rw [elementaryPoly_eq_strictSum, FiniteWords.strictSum_succ,
    FiniteWords.strictSum_succ (fun i : Fin 1 => tildeGenerator i.succ)]
  simp [tildeGenerator, FiniteWords.strictSum_succ]

theorem e1_rankTwo_kernel : generator 0 - generator 1 ∈ kernelSubring 0 := by
  rw [← e1_rankTwo]; exact elementary_mem 0 1

theorem e2_rankTwo_kernel : -(generator 0 * generator 1) ∈ kernelSubring 0 := by
  rw [← e2_rankTwo]; exact elementary_mem 0 2

/-- The rank-two instance of the left root relation `Σ c_r e_r x₀^{N-r} = 0`. -/
theorem root_relation_rankTwo :
    (generator 0 : SkewPolynomial 2) ^ 2 - elementaryPoly 2 1 * generator 0
      - elementaryPoly 2 2 = 0 := by
  rw [e1_rankTwo, e2_rankTwo, pow_two, sub_mul, anti01]
  noncomm_ring

theorem sumSquares_kernel :
    (generator 0 : SkewPolynomial 2) ^ 2 + generator 1 ^ 2 ∈ kernelSubring 0 := by
  rw [mem_kernelSubring]
  intro i
  fin_cases i
  simp only [pow_two, map_add]
  have h0 := divided_mul_left (0 : Fin 1) (generator 0)
  have h1 := divided_mul_right (0 : Fin 1) (generator 1)
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, divided_generator, s_generator] at h0 h1
  simp only [Fin.zero_eta, Fin.isValue, Fin.castSucc_zero, Fin.succ_zero_eq_one] at *
  rw [h0, h1]
  simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  abel

theorem sumSquares_central (f : SkewPolynomial 2) :
    ((generator 0 : SkewPolynomial 2) ^ 2 + generator 1 ^ 2) * f =
      f * (generator 0 ^ 2 + generator 1 ^ 2) := by
  rw [add_mul, mul_add, ElementaryGeneration.square_comm, ElementaryGeneration.square_comm]

theorem rankTwo_kernel_not_central :
    generator (0 : Fin 2) * generator 1 ∈ kernelSubring 0 ∧
    (generator (0 : Fin 2) * generator 1) * generator 0 ≠
      generator 0 * (generator 0 * generator 1) :=
  ⟨NilHeckeCenter.rankTwo_kernel, NilHeckeCenter.rankTwo_not_central⟩

theorem rankThree_volume_central :
    NilHeckeCenter.volume ∈ kernelSubring 1 ∧
    NilHeckeCenter.volume ∈ Subring.center (SkewPolynomial 3) :=
  ⟨NilHeckeCenter.volume_kernel, NilHeckeCenter.volume_central⟩

theorem rankThree_kernel_center_not_squared :
    ∃ z : kernelSubring 1, z ∈ Subring.center (kernelSubring 1) ∧
      (z : SkewPolynomial 3) ∉ NilHeckeCenter.squaredVariableRing :=
  NilHeckeCenter.kernel_center_counterexample

end OddMath.Frontier.CenterONHControls
