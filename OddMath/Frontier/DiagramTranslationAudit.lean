import OddMath.Frontier.DiagramTranslation

/-!
# Scope/gap audit for the even → odd translation dictionary

Compiled audit of `OddMath/Frontier/DiagramTranslation.lean`. Everything claimed as covered is re-stated below and
closed by the dictionary's own theorems; every gap is stated explicitly.

## Covered (compiled: `covered`)
1. Object map on every even boundary `Fin n`: arity `n`, carrier
   `SkewPolynomial n`, endpoint `j` ↦ generator `x_{j+1}` (`boundaryVariable`).
2. Crossing map on every crossing `Expr.swap k i`: the existing `symm1` on the
   rank-two subalgebra of strands `i, i+1` (via `VariableEmbedding.embed`
   along `crossingStrands k i`); a signed-swap monomial operator whose sign is
   the generator negations times the exact ambient crossing-count sign; the
   even denotation exchanges exactly those two strands.
3. The single worked example `swap 0 0 : Expr 2 2`: dictionary entry equal to
   `symm1`, monomial coherence with `denote`, involution on all of
   `SkewPolynomial 2` (consumer of `SignedSwap.symm1_involute`), and the
   square's coherence with `denote (Expr.id 2)`.

## Design check (compiled: `target_is_signed_swap_not_divided_difference`)
The even crossing is translated to the signed swap `s₁` (odd symmetric-group
action), not to the odd nilHecke crossing `d₁`: the even square is the identity
and so is the translated square, whereas the existing sample
`div1_sq_x1sq` gives `d₁²(x₁²) = 0` with `x₁² ≠ 0`.

## First missing piece for the next crossing (compiled witness:
`spectator_outside_local_domain`)
A crossing's dictionary entry is only defined on its own rank-two subalgebra.
For the next crossings `swap 1 0`, `swap 1 1` on three strands, translating a
composite such as `seq (swap 1 0) (swap 1 1)` requires applying the entry of
`swap 1 0` to polynomials involving the spectator generator `x₃`, which is
outside that entry's domain. The first missing inference is therefore the
extension of `crossingOp k i` to all of `SkewPolynomial (k+2)`, i.e. the
rank-`(k+2)` signed transposition of EKL (2.2) as a ring endomorphism of the
ambient model. Besides the local signed swap on strands `i, i+1`, it negates
every spectator generator (EKL (2.2), case "otherwise": `s(x_j) = -x_j`), so on
a normal-ordered monomial it carries the extra factor
`(-1)^(sum of spectator exponents)`; the Koszul re-sorting stays inside the
adjacent pair and crosses no spectator. Neither this extension nor its
multiplicativity is defined or proved here: that is the all-rank odd action,
an explicit non-goal of this module. Only after it exists can the translated
`seq`, and then the even relations (cancellation, braid) for translated
operators, be stated.

## Explicit non-goals (claimed nowhere in these two files)
- no all-rank odd action; no translation of `seq` beyond the single example;
- no braid/crossing soundness and no faithfulness;
- no odd-symmetric quotient descent and no kernel membership;
- no Schur/LR content; no second example; no umbrella/import expansion;
- no legacy-base migration (root PbwL2..L6 boundary stands).
-/

namespace OddMath.Frontier.DiagramTranslationAudit

open OddMath.Diagrammatics.Even OddMath.SkewPolynomial OddMath.DividedDifferences
open OddMath.Frontier.VariableEmbedding OddMath.Frontier.DiagramTranslation

/-- Exactly what the dictionary covers, closed by its own theorems. -/
theorem covered :
    (∀ n : ℕ, Fintype.card (Fin n) = arity n) ∧
    (∀ (k : ℕ) (i : Fin (k + 1)) (j : Fin 2),
      denote (Expr.swap k i) (crossingStrands k i j) = crossingStrands k i (swapFin j)) ∧
    (∀ (k : ℕ) (i : Fin (k + 1)) (e : Fin 2 → ℕ) (r : ℤ),
      crossingOp k i (monomial e r) =
        monomial (expEmbed (crossingStrands k i) (swapExp e)) (r * swapSign e)) ∧
    (∀ (k : ℕ) (i : Fin (k + 1)) (e : Fin 2 → ℕ),
      swapSign e = (-1 : ℤ) ^ (e 0 + e 1) *
        OddMath.skewSign (expEmbed (crossingStrands k i) ![0, e 0])
          (expEmbed (crossingStrands k i) ![e 1, 0])) ∧
    (∀ f : SkewPolynomial 2, exampleOp f = symm1 f) ∧
    Function.Involutive exampleOp ∧
    (denote exampleSquare = denote (Expr.id 2) ∧
      ∀ f : SkewPolynomial 2, exampleSquareOp f = f) :=
  ⟨card_boundary, denote_swap_crossingStrands, crossingOp_monomial,
    swapSign_eq_generator_mul_crossing, exampleOp_eq, example_involutive,
    example_denotation_coherence⟩

/-- Design check on the example crossing: the translated square fixes `x₁²`,
whereas the odd nilHecke crossing squares to zero on it (`d₁²(x₁²) = 0`),
and `x₁² ≠ 0`. So the even crossing must go to `s₁`, not to `d₁`. -/
theorem target_is_signed_swap_not_divided_difference :
    exampleSquareOp (monomial ![2, 0] 1) = monomial ![2, 0] 1 ∧
      div1 (div1 (monomial ![2, 0] 1)) = 0 ∧
      (monomial ![2, 0] 1 : SkewPolynomial 2) ≠ 0 :=
  ⟨exampleSquareOp_eq _, div1_sq_x1sq, Finsupp.single_ne_zero.mpr one_ne_zero⟩

/-- On three strands, the strands of the next crossing `swap 1 0` are `0, 1`;
endpoint `2` (paper strand 3) is a spectator. -/
theorem spectator_not_in_strands (j : Fin 2) : crossingStrands 1 0 j ≠ 2 := by
  revert j
  exact Fin.forall_fin_two.mpr ⟨by decide, by decide⟩

/-- First missing piece, formally: the spectator generator `x₃` is not in the
domain (the image of `embed (crossingStrands 1 0)`) of the local dictionary
entry of the next crossing `swap 1 0`. -/
theorem spectator_outside_local_domain (g : SkewPolynomial 2) :
    embed (crossingStrands 1 0) g ≠ generator 2 := by
  intro h
  have hnot : expSingle (2 : Fin (1 + 2)) ∉ Set.range (expEmbed (crossingStrands 1 0)) := by
    rintro ⟨a, ha⟩
    have h2 : expEmbed (crossingStrands 1 0) a 2 = 0 :=
      expEmbed_not_mem_range _ a 2 (by
        rintro ⟨j, hj⟩
        exact spectator_not_in_strands j hj)
    rw [ha] at h2
    exact absurd h2 (by decide)
  have h0 : (embed (crossingStrands 1 0) g) (expSingle 2) = 0 :=
    Finsupp.embDomain_notin_range
      ⟨expEmbed (crossingStrands 1 0), expEmbed_injective _⟩ g (expSingle 2) hnot
  rw [h] at h0
  have h1 : (generator (2 : Fin (1 + 2))) (expSingle 2) = 1 := Finsupp.single_eq_same
  rw [h1] at h0
  exact one_ne_zero h0

end OddMath.Frontier.DiagramTranslationAudit
