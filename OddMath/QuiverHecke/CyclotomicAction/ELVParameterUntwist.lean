/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightMixedCornerSquare

/-!
# Evaluation of the parameter involution

The coefficient calculation of `docs/Nondegeneracy/DeformedActionAssembly.md`,
§6, equation (9), for the mixed quadratic relation. The ground ring is
commutative; the algebra in which the ordered dot monomials are evaluated need
not be commutative. In particular this calculation does not specialize the
odd coefficient algebra to its even quotient.

`elvOrderedDotExponent` records the two successive signed powers, first the
j-dot and then the i-dot, with total input parity h. Its formula is the one
proved for signed powers in `heightTwoColourRightMul_pow_apply`; the parity
of the intermediate vector is h + q |j|. The support conditions remove this
input parity, not an assumption that the input or its coefficients are even.

`pairQuadPoly_parameterTwist_eval` cancels the crossing-square sign against
the parameter involution, including the single disconnected constant.
`parameterTwist_s_reversed_eval` retains the reversed (j,i) algebra labels
and the ordered product A^q B^p. These are coefficient/evaluation identities,
not a construction of an ELV module category or its tensor contractions.
-/

noncomputable section
namespace OddMath.QuiverHecke

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X]
  (D : SKM.Datum I X) [CommRing k] (Sc : SKM.Scalars D k)

/-- Sign exponent of the chronological j-dot and then i-dot powers. -/
def elvOrderedDotExponent (i j : I) (p q : ℕ) (h : ZMod 2) : ZMod 2 :=
  D.parity j * ((q : ZMod 2) * h + (q / 2 : ℕ)) +
    D.parity i * ((p : ZMod 2) * (h + (q : ZMod 2) * D.parity j) + (p / 2 : ℕ))

/-- The signed composition loses its input-parity dependence on admissible support.
No dots or odd coefficients are commuted in this identity. -/
theorem elvOrderedDotExponent_of_support (i j : I) (p q : ℕ) (h : ZMod 2)
    (hp : (p : ZMod 2) * D.parity i = 0)
    (hq : (q : ZMod 2) * D.parity j = 0) :
    elvOrderedDotExponent D i j p q h =
      D.parity i * (p / 2 : ℕ) + D.parity j * (q / 2 : ℕ) := by
  unfold elvOrderedDotExponent
  linear_combination (h + (q : ZMod 2) * D.parity j) * hp + h * hq

/-- The two separate support restrictions for a nonzero interior coefficient. -/
theorem elvParameter_support {i j : I} {p q : ℕ} (hs : Sc.s i j p q ≠ 0) :
    (p : ZMod 2) * D.parity i = 0 ∧ (q : ZMod 2) * D.parity j = 0 := by
  have hz (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide
  constructor
  · rcases hz ((p : ZMod 2) * D.parity i) with h | h
    · exact h
    · exact False.elim (hs (Sc.s_eq_zero i j p q h))
  · rcases hz ((q : ZMod 2) * D.parity j) with h | h
    · exact h
    · exact False.elim (hs (by rw [Sc.s_symm]; exact Sc.s_eq_zero j i q p h))

/-- Cancellation of the crossing-square sign with the coefficient transport.
The remaining exponent is the two signed dot powers, with arbitrary total
input parity. -/
theorem parameterSignExponent_untwist (i j : I) (p q : ℕ) (h : ZMod 2)
    (hp : (p : ZMod 2) * D.parity i = 0)
    (hq : (q : ZMod 2) * D.parity j = 0) :
    SKM.zsign k (D.parity i * D.parity j) *
        SKM.zsign k (parameterSignExponent D i j p q) =
      SKM.zsign k (elvOrderedDotExponent D i j p q h) := by
  rw [elvOrderedDotExponent_of_support D i j p q h hp hq]
  unfold parameterSignExponent
  rw [add_assoc, SKM.zsign_add, ← mul_assoc, zsign_mul_self, one_mul]

/-- Interior coefficient cancellation in reversed algebra coordinates.
Here A is the j-dot and B the i-dot; their order is not interchanged. -/
theorem parameterTwist_s_reversed_eval {R : Type*} [Ring R] [Algebra k R]
    (i j : I) (p q : ℕ) (h : ZMod 2) (z A B : R) :
    SKM.zsign k (D.parity i * D.parity j) •
        ((parameterTwist D Sc).s j i q p • (z * (A ^ q * B ^ p))) =
      Sc.s i j p q • (SKM.zsign k (elvOrderedDotExponent D i j p q h) •
        (z * (A ^ q * B ^ p))) := by
  by_cases hs : Sc.s i j p q = 0
  · simp [parameterTwist, Sc.s_symm j i q p, hs]
  · obtain ⟨hp, hq⟩ := elvParameter_support D Sc hs
    rw [CyclotomicAction.parameterTwist_s, Sc.s_symm j i q p,
      parameterSignExponent_swap D j i q p]
    simp only [smul_smul]
    rw [← mul_assoc, parameterSignExponent_untwist D i j p q h hp hq, mul_comm]

/-- Leading coefficient cancellation, for every permitted Cartan exponent. -/
theorem parameterTwist_t_eval {R : Type*} [Ring R] [Algebra k R]
    {i j : I} (hij : i ≠ j) (h : ZMod 2) (z B : R) :
    SKM.zsign k (D.parity i * D.parity j) •
        (((parameterTwist D Sc).t i j : k) • (z * B ^ D.dn i j)) =
      (Sc.t i j : k) •
        (SKM.zsign k (elvOrderedDotExponent D i j (D.dn i j) 0 h) •
          (z * B ^ D.dn i j)) := by
  rw [CyclotomicAction.parameterTwist_t_of_ne D Sc hij]
  simp only [smul_smul]
  rw [← mul_assoc, parameterSignExponent_untwist D i j (D.dn i j) 0 h
    (CyclotomicAction.dn_cast_mul_parity D hij) (by simp), mul_comm]

/-- Evaluation of the signed dot polynomial, in algebra-position order.
This is an ordered noncommutative evaluation, not a substitution into a
commutative polynomial ring. The disconnected branch has one constant. -/
def elvSignedPairQuadEval {R : Type*} [Ring R] [Algebra k R]
    (i j : I) (A B : R) : R :=
  if D.d i j = 0 then (Sc.t i j : k) • 1 else
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      (SKM.zsign k (D.parity i * (p / 2 : ℕ) + D.parity j * (q / 2 : ℕ)) *
        Sc.s i j p q) • (A ^ p * B ^ q) +
      ((SKM.zsign k (D.parity i * (D.dn i j / 2 : ℕ)) * (Sc.t i j : k)) •
        A ^ D.dn i j +
       (SKM.zsign k (D.parity j * (D.dn j i / 2 : ℕ)) * (Sc.t j i : k)) •
        B ^ D.dn j i)

/-- The complete ordered quadratic evaluation with the specified coefficients
Sc, starting from the affine algebra parameters `parameterTwist D Sc`.
No commutativity hypothesis on the target algebra is used. -/
theorem pairQuadPoly_parameterTwist_eval {R : Type*} [Ring R] [Algebra k R]
    {i j : I} (hij : i ≠ j) (A B : R) :
    SKM.zsign k (D.parity i * D.parity j) •
        pairQuadPoly D (parameterTwist D Sc) i j A B =
      elvSignedPairQuadEval D Sc i j A B := by
  have hcancel (p q : ℕ) :
      SKM.zsign k (D.parity i * D.parity j) *
          SKM.zsign k (parameterSignExponent D i j p q) =
        SKM.zsign k (D.parity i * (p / 2 : ℕ) + D.parity j * (q / 2 : ℕ)) := by
    unfold parameterSignExponent
    rw [add_assoc, SKM.zsign_add, ← mul_assoc, zsign_mul_self, one_mul]
  unfold pairQuadPoly elvSignedPairQuadEval
  split_ifs with hd
  · have hn : D.dn i j = 0 := by simp [SKM.Datum.dn, hd]
    rw [CyclotomicAction.parameterTwist_t_of_ne D Sc hij]
    simp only [smul_smul, ← mul_assoc, hcancel, hn, Nat.zero_div, Nat.cast_zero,
      mul_zero, add_zero]
    simp [SKM.zsign]
  · simp only [smul_add, Finset.smul_sum, smul_smul,
      CyclotomicAction.parameterTwist_s,
      CyclotomicAction.parameterTwist_t_of_ne D Sc hij,
      CyclotomicAction.parameterTwist_t_of_ne D Sc hij.symm]
    have hswap : parameterSignExponent D j i (D.dn j i) 0 =
        parameterSignExponent D i j 0 (D.dn j i) :=
      parameterSignExponent_swap D j i (D.dn j i) 0
    rw [hswap]
    simp only [← mul_assoc, hcancel, Nat.zero_div, Nat.cast_zero,
      mul_zero, add_zero, zero_add]

/-- The affine quadratic API uses the reversed tuple (j,i). Its crossing-square
sign evaluates to the same ordered signed polynomial, without commuting dots. -/
theorem pairQuadPoly_parameterTwist_reversed_eval {R : Type*} [Ring R] [Algebra k R]
    {i j : I} (hij : i ≠ j) (A B : R) :
    SKM.zsign k (D.parity i * D.parity j) •
        pairQuadPoly D (parameterTwist D Sc) j i A B =
      elvSignedPairQuadEval D Sc j i A B := by
  simpa only [mul_comm (D.parity i) (D.parity j)] using
    pairQuadPoly_parameterTwist_eval D Sc hij.symm A B

/-- Apply the actual affine mixed quadratic relation, then untwist its
coefficients. The algebra map may be a coefficient-extension map or a quotient
map; the target remains an arbitrary, possibly noncommutative k-algebra. -/
theorem affineLastCrossing_parameterUntwist_eval [Fintype I]
    {R : Type*} [Ring R] [Algebra k R] {i j : I} (hij : i ≠ j) (n : ℕ)
    (f : Hn D (parameterTwist D Sc) (n + 1 + 1) →ₐ[k] R) :
    SKM.zsign k (D.parity i * D.parity j) •
      (f (affineLastCrossing D (parameterTwist D Sc) i j n) *
        f (affineLastCrossing D (parameterTwist D Sc) j i n)) =
      f (appendAlgebra D (parameterTwist D Sc) i (n + 1)
        (appendAlgebra D (parameterTwist D Sc) j n 1)) *
      elvSignedPairQuadEval D Sc j i
        (f (appendAlgebra D (parameterTwist D Sc) i (n + 1)
          (affineLastDot D (parameterTwist D Sc) j n)))
        (f (affineLastDot D (parameterTwist D Sc) i (n + 1))) := by
  rw [← map_mul, affineLastCrossing_mul_mixed D (parameterTwist D Sc) n hij,
    map_mul, map_pairQuadPoly, ← mul_smul_comm,
    pairQuadPoly_parameterTwist_reversed_eval D Sc hij]

/-- Evaluation remains valid on every left module over the target algebra.
The arbitrary left factor z may contain odd coefficients. No flatness,
projectivity, or commutativity of that algebra is required. -/
theorem pairQuadPoly_parameterTwist_module {R M : Type*} [Ring R] [Algebra k R]
    [AddCommGroup M] [Module R M] {i j : I} (hij : i ≠ j) (z A B : R) (m : M) :
    (z * (SKM.zsign k (D.parity i * D.parity j) •
      pairQuadPoly D (parameterTwist D Sc) j i A B)) • m =
      (z * elvSignedPairQuadEval D Sc j i A B) • m := by
  rw [pairQuadPoly_parameterTwist_reversed_eval D Sc hij]

end OddMath.QuiverHecke
