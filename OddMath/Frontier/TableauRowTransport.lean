import OddMath.Frontier.TableauRowRecursion

/-!
# Raw signed transport through the installed recursive row algorithm

Iterate RowBump.row_bump (Ellis arXiv:1111.3932v1, Proposition 3.7)
inside the actual odd plactic quotient. Rows are traversed top-down and
read bottom-up. The sign is the computed crossing count, not a shape sign.
No output-tableau geometry or insertion bijection is asserted.
-/
namespace OddMath.Frontier.TableauRowTransport

open TableauSign TableauEvaluation TableauRowRecursion

private theorem readRows_cons {n : ℕ} (w : List (Fin n)) (ws : List (List (Fin n))) :
    readRows (w :: ws) = readRows ws ++ w := by
  simp [readRows, List.reverse_cons, List.flatten_append]

/-- Recursive quotient transport; the only row hypothesis is weak sorting. -/
theorem runRows_word (n : ℕ) (rs : List (List (Fin n))) (a : Fin n)
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·)) :
    OddPlactic.word n (readRows rs ++ [a]) =
      (-1 : ℤ) ^ (runRows n rs a).crossings •
        OddPlactic.word n (readRows (runRows n rs a).output) := by
  induction rs generalizing a with
  | nil => simp [runRows, readRows]
  | cons w ws ih =>
    have hw := hs w (by simp)
    have ht := fun z hz => hs z (List.mem_cons_of_mem w hz)
    simp only [runRows]
    split
    · simp only [readRows_cons, pow_zero, one_smul, List.append_assoc]
    · rename_i u b v hsplit hu hab hdecision
      have hlocal := RowBump.row_bump n u v a b (hsplit ▸ hw) hu hab
      have hrec := ih b ht
      simp only [readRows_cons]
      rw [hsplit, List.append_assoc, OddPlactic.word_append, hlocal, mul_smul_comm]
      have hrearrange :
          OddPlactic.word n (readRows ws) * OddPlactic.word n (b :: (u ++ (a :: v))) =
            OddPlactic.word n (readRows ws ++ [b]) * OddPlactic.word n (u ++ (a :: v)) := by
        simp only [OddPlactic.word_append, OddPlactic.word_cons,
          OddPlactic.word_nil, mul_one, mul_assoc]
      rw [hrearrange, hrec, smul_mul_assoc, smul_smul, ← pow_add,
        ← OddPlactic.word_append]

/-- Arbitrary surrounding words, including any changed upper-row suffix. -/
theorem runRows_word_context (n : ℕ) (rs : List (List (Fin n))) (a : Fin n)
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·)) (l z : List (Fin n)) :
    OddPlactic.word n (l ++ ((readRows rs ++ [a]) ++ z)) =
      (-1 : ℤ) ^ (runRows n rs a).crossings •
        OddPlactic.word n (l ++ (readRows (runRows n rs a).output ++ z)) := by
  have h := congrArg (fun x => OddPlactic.word n l * (x * OddPlactic.word n z))
    (runRows_word n rs a hs)
  simpa only [OddPlactic.word_append, smul_mul_assoc, mul_smul_comm] using h

/-- Actual tableau input, with order and sorting obtained internally. -/
theorem tableau_word (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (a : Fin n) :
    OddPlactic.word n (rowFinWord n T hT ++ [a]) =
      (-1 : ℤ) ^ (runRows n (rows n T hT) a).crossings •
        OddPlactic.word n (readRows (runRows n (rows n T hT) a).output) := by
  simpa only [readRows_rows] using
    runRows_word n (rows n T hT) a (rows_sorted n μ T hT)

/-- Forward evaluation only; no reflection through the noninjective map. -/
theorem tableau_polynomial (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (a : Fin n) :
    rowPolynomial n T hT * PlacticEvaluation.tildeGenerator a =
      (-1 : ℤ) ^ (runRows n (rows n T hT) a).crossings •
        PlacticEvaluation.toSkew n
          (OddPlactic.word n (readRows (runRows n (rows n T hT) a).output)) := by
  have h := congrArg (PlacticEvaluation.toSkew n) (tableau_word n μ T hT a)
  simpa only [OddPlactic.word_append, OddPlactic.word_cons, OddPlactic.word_nil,
    mul_one, map_mul, PlacticEvaluation.toSkew_q, rowPolynomial, map_zsmul] using h

end OddMath.Frontier.TableauRowTransport
