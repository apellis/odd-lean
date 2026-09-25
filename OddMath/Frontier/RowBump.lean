import OddMath.Frontier.OddPlactic
import OddMath.Frontier.TableauEvaluation

/-!
# Signed single-row bumping

Ellis, arXiv:1111.3932v1, Proposition 3.7 proof: a bump across a row
of length r contributes (-1)^(r-1). The two inductions below use exactly
the signed Knuth relations, including their weak endpoints. This is a
quotient identity, not a consequence reflected through skew evaluation.
No whole-tableau insertion or column-preservation theorem is asserted.
-/

namespace OddMath.Frontier.RowBump

open OddPlactic

/-- Move the insertion letter through the larger sorted tail using K′. -/
private theorem bump_tail (n : ℕ) (v : List (Fin n)) (a b : Fin n)
    (hs : (b :: v).Sorted (· ≤ ·)) (hab : a < b) :
    word n ((b :: v) ++ [a]) =
      (-1 : ℤ) ^ v.length • word n (b :: a :: v) := by
  induction v generalizing b with
  | nil => simp
  | cons c v ih =>
    have hbc := (List.pairwise_cons.mp hs).1 c (by simp)
    have hcv := (List.pairwise_cons.mp hs).2
    have hi := ih c hcv (hab.trans_le hbc)
    have hk := word_knuth_left n [] v a b c hab hbc
    simp only [List.nil_append, List.cons_append, List.nil_append] at hk
    calc
      word n ((b :: c :: v) ++ [a]) =
          q n b * word n ((c :: v) ++ [a]) := rfl
      _ = (-1 : ℤ) ^ v.length • word n (b :: c :: a :: v) := by
        rw [hi, mul_smul_comm]
        rfl
      _ = (-1 : ℤ) ^ v.length • (-word n (b :: a :: c :: v)) := by rw [hk]
      _ = (-1 : ℤ) ^ (c :: v).length • word n (b :: a :: c :: v) := by
        simp [pow_succ, mul_smul]

/-- Move the bumped letter through the smaller sorted prefix using K′′. -/
private theorem bump_prefix (n : ℕ) (u : List (Fin n)) (a b : Fin n)
    (hs : u.Sorted (· ≤ ·)) (hu : ∀ x ∈ u, x ≤ a) (hab : a < b) :
    word n (u ++ [b, a]) =
      (-1 : ℤ) ^ u.length • word n (b :: (u ++ [a])) := by
  induction u generalizing a with
  | nil => simp
  | cons x u ih =>
    have hx : x ≤ a := hu x (by simp)
    have hsu := (List.pairwise_cons.mp hs).2
    have huu : ∀ y ∈ u, y ≤ a := fun y hy => hu y (by simp [hy])
    have hi := ih a hsu huu hab
    have hk : word n (x :: b :: (u ++ [a])) =
        -word n (b :: x :: (u ++ [a])) := by
      cases u with
      | nil =>
        simpa using word_knuth_right n [] [] x a b hx hab
      | cons y t =>
        have hxy : x ≤ y := (List.pairwise_cons.mp hs).1 y (by simp)
        have hyb : y < b := (huu y (by simp)).trans_lt hab
        simpa using word_knuth_right n [] (t ++ [a]) x y b hxy hyb
    calc
      word n ((x :: u) ++ [b, a]) = q n x * word n (u ++ [b, a]) := rfl
      _ = (-1 : ℤ) ^ u.length • word n (x :: b :: (u ++ [a])) := by
        rw [hi, mul_smul_comm]
        rfl
      _ = (-1 : ℤ) ^ u.length • (-word n (b :: x :: (u ++ [a]))) := by rw [hk]
      _ = (-1 : ℤ) ^ (x :: u).length • word n (b :: ((x :: u) ++ [a])) := by
        simp [pow_succ, mul_smul]

/-- The arbitrary-length first-greater split law in the actual plactic quotient. -/
theorem row_bump (n : ℕ) (u v : List (Fin n)) (a b : Fin n)
    (hs : (u ++ (b :: v)).Sorted (· ≤ ·))
    (hu : ∀ x ∈ u, x ≤ a) (hab : a < b) :
    word n ((u ++ (b :: v)) ++ [a]) =
      (-1 : ℤ) ^ (u.length + v.length) • word n (b :: (u ++ (a :: v))) := by
  have hp := List.pairwise_append.mp hs
  have ht := bump_tail n v a b hp.2.1 hab
  have hu' := bump_prefix n u a b hp.1 hu hab
  calc
    word n ((u ++ (b :: v)) ++ [a]) = word n u * word n ((b :: v) ++ [a]) := by
      rw [List.append_assoc, word_append]
    _ = (-1 : ℤ) ^ v.length • (word n u * word n (b :: a :: v)) := by
      rw [ht, mul_smul_comm]
    _ = (-1 : ℤ) ^ v.length • (word n (u ++ [b, a]) * word n v) := by
      simp only [word_append, word_cons, word_nil, mul_one, mul_assoc]
    _ = (-1 : ℤ) ^ (u.length + v.length) • word n (b :: (u ++ (a :: v))) := by
      rw [hu', smul_mul_assoc, smul_smul, mul_comm, ← pow_add]
      congr 1
      simp only [word_append, word_cons, word_nil, mul_one, mul_assoc]

/-- Replacing the first greater letter preserves weak row order. -/
theorem row_bump_sorted (n : ℕ) (u v : List (Fin n)) (a b : Fin n)
    (hs : (u ++ (b :: v)).Sorted (· ≤ ·))
    (hu : ∀ x ∈ u, x ≤ a) (hab : a < b) :
    (u ++ (a :: v)).Sorted (· ≤ ·) := by
  have hp := List.pairwise_append.mp hs
  have hv := List.pairwise_cons.mp hp.2.1
  apply List.pairwise_append.mpr
  refine ⟨hp.1, List.pairwise_cons.mpr ⟨?_, hv.2⟩, ?_⟩
  · intro y hy
    exact hab.le.trans (hv.1 y hy)
  · intro x hx y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hu x hx
    · exact (hu x hx).trans (hab.le.trans (hv.1 y hy))

/-- Substitute the row identity in arbitrary literal contexts. -/
theorem row_bump_context (n : ℕ) (l r u v : List (Fin n)) (a b : Fin n)
    (hs : (u ++ (b :: v)).Sorted (· ≤ ·))
    (hu : ∀ x ∈ u, x ≤ a) (hab : a < b) :
    word n (l ++ (((u ++ (b :: v)) ++ [a]) ++ r)) =
      (-1 : ℤ) ^ (u.length + v.length) • word n (l ++ ((b :: (u ++ (a :: v))) ++ r)) := by
  have h := congrArg (fun z => word n l * (z * word n r))
    (row_bump n u v a b hs hu hab)
  simpa only [word_append, smul_mul_assoc, mul_smul_comm] using h

/-- Forward transport along the existing plactic-to-skew ring map. -/
theorem row_bump_toSkew (n : ℕ) (l r u v : List (Fin n)) (a b : Fin n)
    (hs : (u ++ (b :: v)).Sorted (· ≤ ·))
    (hu : ∀ x ∈ u, x ≤ a) (hab : a < b) :
    PlacticEvaluation.toSkew n (word n (l ++ (((u ++ (b :: v)) ++ [a]) ++ r))) =
      (-1 : ℤ) ^ (u.length + v.length) •
        PlacticEvaluation.toSkew n (word n (l ++ ((b :: (u ++ (a :: v))) ++ r))) := by
  rw [row_bump_context n l r u v a b hs hu hab, map_zsmul]

/-- Actual tableau polynomial consumer; the output is an evaluated word,
not an assertion of a valid inserted tableau. -/
theorem rowPolynomial_bump (n : ℕ) (μ : YoungDiagram)
    (T : TableauSign.PositiveTableau μ) (hT : TableauEvaluation.InAlphabet n T)
    (l u v : List (Fin n)) (a b : Fin n)
    (hsplit : TableauEvaluation.rowFinWord n T hT = l ++ (u ++ (b :: v)))
    (hs : (u ++ (b :: v)).Sorted (· ≤ ·))
    (hu : ∀ x ∈ u, x ≤ a) (hab : a < b) :
    TableauEvaluation.rowPolynomial n T hT * PlacticEvaluation.tildeGenerator a =
      (-1 : ℤ) ^ (u.length + v.length) •
        PlacticEvaluation.toSkew n (word n (l ++ (b :: (u ++ (a :: v))))) := by
  have h := row_bump_toSkew n l [] u v a b hs hu hab
  simp only [List.append_nil] at h
  rw [TableauEvaluation.rowPolynomial, hsplit, ← PlacticEvaluation.toSkew_q n a,
    ← map_mul, ← h]
  congr 1
  simp only [word_append, word_cons, word_nil, mul_one, mul_assoc]

/-- No-bump append has coefficient +1, even for an empty row. -/
theorem row_append (n : Nat) (w : List (Fin n)) (a : Fin n) :
    word n (w ++ [a]) = word n w * q n a := by simp

theorem row_append_sorted (n : Nat) (w : List (Fin n)) (a : Fin n)
    (hs : w.Sorted (· ≤ ·)) (ha : ∀ x ∈ w, x ≤ a) :
    (w ++ [a]).Sorted (· ≤ ·) := by
  apply List.pairwise_append.mpr
  refine ⟨hs, by simp, ?_⟩
  intro x hx y hy
  simpa only [List.mem_singleton.mp hy] using ha x hx

end OddMath.Frontier.RowBump
