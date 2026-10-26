/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.PairCoordinates
import OddMath.QuiverHecke.CyclotomicAction.BraidOperators
import OddMath.QuiverHecke.CyclotomicAction.ConcreteRelationExamples

/-!
# The asymmetric transported quadratic as an actual operator identity

Ports a concrete signed parameter-comparison consumer of
`Categorification/KLR/CyclotomicAction/Square.lean` and
`Categorification/KLR/CyclotomicAction/MixedComparison.lean`.
For the all-odd Cartan matrix `[[2,-2],[-4,2]]`, the actual cyclotomic algebra
with polynomial `u²-v⁴` acts by signed right multiplication with the target
operator relation `U²+V⁴`. No abstract quadratic operator is assumed. The
operators are on the existing graded regular module, before the full
superinduction and Mackey comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u
section Regular
variable {k A : Type u} [CommRing k] [Ring A] [Algebra k A]
  (G : ZMod 2 → Submodule k A) [GradedAlgebra G]

/-- Two signed homogeneous right multipliers, with the exact Koszul factor. -/
theorem regularSignedRight_pair_apply {p q s : ZMod 2} {a b x : A}
    (ha : a ∈ G p) (hx : x ∈ G s) :
    regularSignedRight G q b (regularSignedRight G p a x) =
      (koszulSign (s + p) q * koszulSign s p) • (x * (a * b)) := by
  rw [regularSignedRight_apply G q b _ (regularSignedRight_apply_mem G ha hx),
    regularSignedRight_apply G p a x hx]
  simp only [smul_mul_assoc, smul_smul, mul_assoc]

/-- The square sign depends only on the multiplier degree. -/
theorem regularSignedRight_square_apply {p s : ZMod 2} {a x : A}
    (ha : a ∈ G p) (hx : x ∈ G s) :
    regularSignedRight G p a (regularSignedRight G p a x) =
      koszulSign p p • (x * a ^ 2) := by
  simpa only [crossing_square_sign, pow_two] using regularSignedRight_pair_apply G ha hx

/-- Fourth powers of signed homogeneous right multipliers have positive sign. -/
theorem regularSignedRight_fourth_apply {p s : ZMod 2} {a x : A}
    (ha : a ∈ G p) (hx : x ∈ G s) :
    regularSignedRight G p a (regularSignedRight G p a
      (regularSignedRight G p a (regularSignedRight G p a x))) = x * a ^ 4 := by
  rw [regularSignedRight_square_apply G ha
    (regularSignedRight_apply_mem G ha (regularSignedRight_apply_mem G ha hx)),
    regularSignedRight_square_apply G ha hx]
  change koszulSign p p • ((koszulSign p p • (x * a ^ 2)) * a ^ 2) = x * a ^ 4
  rw [smul_mul_assoc, smul_smul, koszulSign_mul_self, one_smul, mul_assoc, ← pow_add]
  rfl

end Regular
namespace CyclotomicAction.TransportedOperatorExamples
open AsymmetricParameters ConcreteRelationExamples

/-- The transported polynomial is evaluated at the actual two affine pair-dot elements. -/
theorem affine_square_at_pair_dots (n : ℕ) :
    affineLastCrossing datum transportedScalars true false n *
        affineLastCrossing datum transportedScalars false true n =
      affinePairDotLeft datum transportedScalars false true n ^ 2 -
        affinePairDotRight datum transportedScalars false true n ^ 4 := by
  let L : ∀ w : Word Bool n,
      End (wordObj datum transportedScalars (appendWord true (appendWord false w))) :=
    fun w => dotE datum transportedScalars (appendWord true (appendWord false w)).1 w.1.length
  let R : ∀ w : Word Bool n,
      End (wordObj datum transportedScalars (appendWord true (appendWord false w))) :=
    fun w => dotE datum transportedScalars (appendWord true (appendWord false w)).1 (w.1.length + 1)
  have h := transported_affine_square n
  change _ = pairEndMap datum transportedScalars false true n (L ^ 2 - R ^ 4) at h
  rw [h]
  change pairEndMap datum transportedScalars false true n (L ^ 2 - R ^ 4) =
    pairEndMap datum transportedScalars false true n L ^ 2 -
      pairEndMap datum transportedScalars false true n R ^ 4
  simp only [pow_succ, pow_zero, mul_one, map_sub, map_mul]

/-- The same equality at the actual two cyclotomic pair-dot elements. -/
theorem cyclotomic_square_at_pair_dots (a : Bool → _root_.Polynomial ℚ) (n : ℕ) :
    cyclotomicLastCrossing datum transportedScalars true false a n *
        cyclotomicLastCrossing datum transportedScalars false true a n =
      cyclotomicPairDotLeft datum transportedScalars false true a n ^ 2 -
        cyclotomicPairDotRight datum transportedScalars false true a n ^ 4 := by
  simp only [cyclotomicLastCrossing, cyclotomicPairDotLeft, cyclotomicPairDotRight,
    ← map_mul, ← map_pow, ← map_sub]
  exact congrArg (cyclotomicMk datum transportedScalars a (n + 1 + 1))
    (affine_square_at_pair_dots (n + 1))

/-- The transported algebra realizes the target sum of the signed dot square and fourth power. -/
theorem transported_operator_square (a : Bool → _root_.Polynomial ℚ)
    (ha : CyclotomicPolynomialParity datum a) (n : ℕ) {s : ZMod 2}
    (x : CyclotomicAlgebra datum transportedScalars a (n + 1 + 1))
    (hx : x ∈ cyclotomicParity datum transportedScalars a ha (n + 1 + 1) s) :
    let G := cyclotomicParity datum transportedScalars a ha (n + 1 + 1)
    let U := regularSignedRight G 1 (cyclotomicPairDotLeft datum transportedScalars false true a n)
    let V := regularSignedRight G 1 (cyclotomicPairDotRight datum transportedScalars false true a n)
    regularSignedRight G 1 (cyclotomicLastCrossing datum transportedScalars false true a n)
        (regularSignedRight G 1 (cyclotomicLastCrossing datum transportedScalars true false a n) x) =
      U (U x) + V (V (V (V x))) := by
  dsimp only
  have hc := cyclotomicLastCrossing_parity datum transportedScalars true false a ha n
  have hL := cyclotomicPairDotLeft_parity datum transportedScalars false true a ha n
  have hR := cyclotomicPairDotRight_parity datum transportedScalars false true a ha n
  rw [regularSignedRight_pair_apply _ hc hx, regularSignedRight_square_apply _ hL hx,
    regularSignedRight_fourth_apply _ hR hx, crossing_square_sign]
  change (-1 : ℤ) • (x * (cyclotomicLastCrossing datum transportedScalars true false a n *
      cyclotomicLastCrossing datum transportedScalars false true a n)) =
    (-1 : ℤ) • (x * cyclotomicPairDotLeft datum transportedScalars false true a n ^ 2) +
      x * cyclotomicPairDotRight datum transportedScalars false true a n ^ 4
  rw [cyclotomic_square_at_pair_dots]
  simp only [neg_one_zsmul, mul_sub, neg_sub, sub_eq_add_neg, add_comm]

end CyclotomicAction.TransportedOperatorExamples
end OddMath.QuiverHecke
