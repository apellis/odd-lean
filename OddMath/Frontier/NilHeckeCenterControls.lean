import OddMath.Frontier.NilHeckeCenter

namespace OddMath.Frontier.NilHeckeCenterControls
open NilHeckeCenter NilHeckeAction AllRankDivided OddSymmetricKernel
open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
noncomputable section

-- Direct arbitrary-element consumers; no assertion only on generators.
theorem arbitrary_nilHecke (a : Presented 1) : a * dotVolume = dotVolume * a :=
  (dotVolume_commutes a).symm

theorem arbitrary_kernel (p : kernelSubring 1) : p * kernelVolume = kernelVolume * p :=
  Subring.mem_center_iff.mp kernelVolume_central p

theorem arbitrary_squared_image (p : SkewPolynomial 3) (hp : p ∈ squaredVariableRing) :
    polynomialInclusion p ≠ dotVolume := dotVolume_not_squared_image p hp

theorem natural_action_consumer (p f : SkewPolynomial 3) :
    action 1 (polynomialInclusion p) f = p*f := polynomialInclusion_action p f

-- Rank two has nonzero squares and skew, not exterior, multiplication.
theorem rankTwo_square_survives : generator (0 : Fin 2) ^ 2 ≠ 0 := by
  rw [pow_two]
  exact OddMath.SkewPolynomial.generator_square_ne_zero (0 : Fin 2)

theorem rankTwo_distinct_odd_anticommute :
    generator (0 : Fin 2) * generator 1 = -(generator 1 * generator 0) :=
  OddMath.PbwL1.rel_anticommute 0 1 (by decide)

theorem rankTwo_kernel_not_ordinary_central :
    generator (0 : Fin 2) * generator 1 ∈ kernelSubring 0 ∧
    generator (0 : Fin 2) * generator 1 ∉ Subring.center (SkewPolynomial 2) := by
  refine ⟨rankTwo_kernel, ?_⟩
  intro h
  exact rankTwo_not_central (Subring.mem_center_iff.mp h (generator 0)).symm

-- Hand-derived: x0*x1*x2*x0 = x0^2*x1*x2, coefficient +1.
theorem volume_times_x0 : volume * generator 0 = monomial ![2,1,1] 1 := by
  simp only [volume, generator, mm]
  norm_num [OddMath.skewSign, OddMath.crossingCount, expSingle,
    Fin.sum_univ_three, Finset.sum_filter, Fin.ext_iff, Pi.add_apply]
  congr 1
  funext j
  fin_cases j <;> decide

/-- Degree-three volume and degree-one x0 are both odd in the source's
halved-degree parity. Ordinary commutation is NOT the super sign rule. -/
theorem volume_not_odd_supercentral : volume * generator 0 ≠ -(generator 0 * volume) := by
  intro h
  rw [← volume_commutes_generators 0, volume_times_x0] at h
  have he := congrArg (fun p : SkewPolynomial 3 => p ![2,1,1]) h
  norm_num [monomial] at he

theorem dotVolume_not_odd_supercentral : dotVolume * dot 1 0 ≠ -(dot 1 0 * dotVolume) := by
  intro h
  have he := congrArg (fun a : Presented 1 => action 1 a 1) h
  simp only [map_neg, LinearMap.neg_apply, action_mul_apply,
    dotVolume_action, action_dot_apply, mul_one] at he
  exact volume_not_odd_supercentral he

/-- Formal negation of the first squared-variable inference, with no parity
or even-rank premise quietly added to the printed statement. -/
theorem source_first_claim_false :
    ¬ (∀ p : SkewPolynomial 3, p ∈ Subring.center (SkewPolynomial 3) →
      p ∈ squaredVariableRing) := by
  intro h
  exact volume_not_squared (h volume volume_central)

theorem source_kernel_claim_false :
    ¬ (∀ p : kernelSubring 1, p ∈ Subring.center (kernelSubring 1) →
      (p : SkewPolynomial 3) ∈ squaredVariableRing) := by
  intro h
  exact volume_not_squared (h kernelVolume kernelVolume_central)

theorem source_nilHecke_claim_false :
    ¬ (∀ a : Presented 1, a ∈ Subring.center (Presented 1) → a ∈ squaredDotRing) := by
  intro h
  exact dotVolume_not_squared (h dotVolume dotVolume_central)

end
end OddMath.Frontier.NilHeckeCenterControls
