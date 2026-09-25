import OddMath.Frontier.LongestReversal

namespace OddMath.Frontier.LongestReversalControls
open OddMath.SkewPolynomial (SkewPolynomial generator)
open LongestDivided LongestElementary SignedPermutation AllRankDivided

-- Controls recorded before production: literal signs, not theorem specializations.
theorem rank_two_left : skewAction (longest 2) (D 2 (generator 0)) = 1 := by
  change skewAction (longest 2) (divided (0 : Fin 1) (generator 0)) = 1
  simp [divided_generator]

theorem rank_two_right : D 2 (skewAction (longest 2) (generator 0)) = -1 := by
  rw [action_generator, epsilon_longest]
  change divided (0 : Fin 1) ((-1 : ℤ)^1 • generator 1) = -1
  simp [divided_generator]

theorem missing_sign_rejected :
    skewAction (longest 2) (D 2 (generator 0)) ≠
      D 2 (skewAction (longest 2) (generator 0)) := by
  rw [rank_two_left, rank_two_right]
  intro h
  have hh := congrArg (fun f : SkewPolynomial 2 => f 0) h
  change (Finsupp.single (0 : Fin 2 → ℕ) (1 : ℤ)) 0 =
    (- (Finsupp.single (0 : Fin 2 → ℕ) (1 : ℤ))) 0 at hh
  norm_num at hh

theorem rank_three_left : D 3 (generator 0 ^ 2 * generator 1) = -1 := by
  change divided (0 : Fin 2) (divided 1 (divided 0 _)) = -1
  simp [pow_two, divided_mul, divided_generator, s_generator, Equiv.swap_apply_def]

theorem rank_three_right :
    D 3 (skewAction (longest 3) (generator 0 ^ 2 * generator 1)) = 1 := by
  simp only [map_mul, map_pow, action_generator, epsilon_longest]
  change divided (0 : Fin 2) (divided 1 (divided 0
    (((-1 : ℤ)^3 • generator 2)^2 * ((-1 : ℤ)^3 • generator 1)))) = 1
  norm_num [pow_two, divided_mul, divided_generator, s_generator, Equiv.swap_apply_def,
    Fin.ext_iff]

example (f : SkewPolynomial 0) : D 0 f = f := rfl
example (f : SkewPolynomial 1) : D 1 f = f := rfl
example : coxeterWord 4 = [0,1,0,2,1,0] := rfl
example : (coxeterWord 4).map (fun i => 2-i) = [2,1,2,0,1,2] := rfl

-- Positive all-input edge cases are not zero-ring/vacuous fixtures.
theorem rank_zero (f : SkewPolynomial 0) :
    skewAction (longest 0) (D 0 f) = D 0 (skewAction (longest 0) f) := rfl

theorem rank_one (f : SkewPolynomial 1) :
    skewAction (longest 1) (D 1 f) = D 1 (skewAction (longest 1) f) := rfl

-- A nonsymmetric input lies outside the kernel, so the test would reject a
-- restriction of the theorem to kernel inputs.
theorem rank_two_input_not_kernel :
    generator (0 : Fin 2) ∉ OddSymmetricKernel.kernelSubring 0 := by
  intro h
  have hz := (OddSymmetricKernel.mem_kernelSubring _).mp h (0 : Fin 1)
  simp only [divided_generator, Fin.castSucc_zero, true_or, if_true] at hz
  have hc := congrArg (fun f : SkewPolynomial 2 => f 0) hz
  change (Finsupp.single (0 : Fin 2 → ℕ) (1 : ℤ)) 0 = 0 at hc
  norm_num at hc

-- The exact all-rank source theorem, no extra hypothesis.
example (N : ℕ) (f : SkewPolynomial N) :
    skewAction (longest N) (D N f) =
      (-1 : ℤ)^(N.choose 2) • D N (skewAction (longest N) f) :=
  LongestReversal.action_D N f

example (N : ℕ) : D N (skewAction (longest N) (staircase N)) =
    (-1 : ℤ)^((N+1).choose 3) • (1 : SkewPolynomial N) :=
  LongestReversal.D_reversed_staircase N

-- Arbitrary actual kernel coefficient and arbitrary actual polynomial, LEFT side.
example (n : ℕ) (c : OddSymmetricKernel.kernelSubring n) (g : SkewPolynomial (n+2)) :
    skewAction (longest (n+2)) (D (n+2) ((c : SkewPolynomial (n+2))*g)) =
      (c : SkewPolynomial (n+2)) * skewAction (longest (n+2)) (D (n+2) g) :=
  LongestReversal.action_D_left_kernel n c g c.property

-- The mirrored literal triangle is EXACTLY equal, not an existential ± comparison.
example (n : ℕ) (f : SkewPolynomial (n+2)) :
    D (n+2) f = LongestReversal.triangle n 1 (n+1) (LongestReversal.up n 0 (n+1) f) := by
  rw [D_eq_actNat, ← LongestReversal.triangle_source,
    LongestReversal.triangle_other n 0 (n+1) (by omega)]
  rfl

end OddMath.Frontier.LongestReversalControls
