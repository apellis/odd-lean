import OddMath.Diagrammatics.OddDots

/-!
# Arbitrary-rank odd dots and contextual signed exchange

Source: Ellis–Khovanov–Lauda, arXiv:1111.1320v1, §2.1.1, (2.1), p.3:
distinct generators anticommute over ℤ. The source's dot Z-degree
is 2 (p.5) and super parity is 1 (p.22); these are separate data here, as in
`Diagrammatics.OddDots`. Locked conventions: the sign convention and
the translation table, increasing-index monomials and Koszul signs.

Words are chronological, bottom-first; each dot acts by LEFT multiplication
on the existing `SkewPolynomial n`. All ranks, word lengths, contexts and
input polynomials are quantified. We prove soundness of dot exchange, not a
presentation equivalence, faithfulness, crossings, or braid relations.
-/

namespace OddMath.Frontier.DotContexts

open OddMath.SkewPolynomial

abbrev Dot (n : ℕ) := Fin n
abbrev DotSeq (n : ℕ) := List (Dot n)

def dotParity {n : ℕ} (_ : Dot n) : ℕ := 1
def dotDegree {n : ℕ} (_ : Dot n) : ℕ := 2

theorem dotParity_eq {n : ℕ} (i : Dot n) : dotParity i = 1 := rfl
theorem dotDegree_eq {n : ℕ} (i : Dot n) : dotDegree i = 2 := rfl

/-- Bottom dot first; later dots multiply on the left of its output. -/
noncomputable def denote {n : ℕ} : DotSeq n → SkewPolynomial n → SkewPolynomial n
  | [], f => f
  | i :: rest, f => denote rest (mul (generator i) f)

noncomputable def denoteValue {n : ℕ} (word : DotSeq n) : SkewPolynomial n :=
  denote word one

theorem denote_nil {n : ℕ} (f : SkewPolynomial n) : denote [] f = f := rfl

theorem denote_cons {n : ℕ} (i : Dot n) (rest : DotSeq n) (f : SkewPolynomial n) :
    denote (i :: rest) f = denote rest (mul (generator i) f) := rfl

theorem denote_singleton {n : ℕ} (i : Dot n) (f : SkewPolynomial n) :
    denote [i] f = mul (generator i) f := rfl

theorem denote_zero {n : ℕ} (word : DotSeq n) : denote word 0 = 0 := by
  induction word with
  | nil => rfl
  | cons i rest ih => rw [denote_cons, mul_zero, ih]

theorem denote_add {n : ℕ} (word : DotSeq n) (f g : SkewPolynomial n) :
    denote word (f + g) = denote word f + denote word g := by
  induction word generalizing f g with
  | nil => rfl
  | cons i rest ih =>
      rw [denote_cons, denote_cons, denote_cons, mul_add, ih]

/-- The integral additive interpretation; no multiplication instance is invented. -/
noncomputable def denoteAddHom {n : ℕ} (word : DotSeq n) :
    SkewPolynomial n →+ SkewPolynomial n where
  toFun := denote word
  map_zero' := denote_zero word
  map_add' := denote_add word

theorem denote_neg {n : ℕ} (word : DotSeq n) (f : SkewPolynomial n) :
    denote word (-f) = -denote word f :=
  (denoteAddHom word).map_neg f

theorem denote_zsmul {n : ℕ} (word : DotSeq n) (z : ℤ) (f : SkewPolynomial n) :
    denote word (z • f) = z • denote word f :=
  (denoteAddHom word).map_zsmul f z

/-- Vertical composition: below is applied before above. -/
theorem denote_append {n : ℕ} (below above : DotSeq n) (f : SkewPolynomial n) :
    denote (below ++ above) f = denote above (denote below f) := by
  induction below generalizing f with
  | nil => rfl
  | cons i rest ih =>
      exact ih (mul (generator i) f)

/-- Local exchange on any input, directly from the actual multiplication laws. -/
theorem signed_exchange_operator {n : ℕ} (i j : Dot n) (h : i ≠ j)
    (f : SkewPolynomial n) :
    denote [i, j] f + denote [j, i] f = 0 := by
  show mul (generator j) (mul (generator i) f) +
    mul (generator i) (mul (generator j) f) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul,
    generator_anticommute j i (Ne.symm h), neg_add_cancel, zero_mul]

/-- Distinct adjacent dots signed-commute in arbitrary chronological context. -/
theorem signed_exchange_context {n : ℕ} (pre post : DotSeq n) (i j : Dot n)
    (h : i ≠ j) (f : SkewPolynomial n) :
    denote (pre ++ [i, j] ++ post) f +
      denote (pre ++ [j, i] ++ post) f = 0 := by
  simp only [denote_append]
  rw [← denote_add, signed_exchange_operator i j h, denote_zero]

theorem signed_exchange_context_neg {n : ℕ} (pre post : DotSeq n) (i j : Dot n)
    (h : i ≠ j) (f : SkewPolynomial n) :
    denote (pre ++ [i, j] ++ post) f = -denote (pre ++ [j, i] ++ post) f :=
  eq_neg_of_add_eq_zero_left (signed_exchange_context pre post i j h f)

/-- Pointwise contextual exchange is also equality of operators. -/
theorem signed_exchange_context_fun {n : ℕ} (pre post : DotSeq n) (i j : Dot n)
    (h : i ≠ j) :
    denote (pre ++ [i, j] ++ post) = -denote (pre ++ [j, i] ++ post) := by
  funext f
  exact signed_exchange_context_neg pre post i j h f

/-- The new semantics specializes exactly to the inherited rank-two semantics. -/
theorem denote_rank_two (word : DotSeq 2) (f : SkewPolynomial 2) :
    denote word f = OddMath.Diagrammatics.OddDots.denote word f := by
  induction word generalizing f with
  | nil => rfl
  | cons i rest ih => exact ih (mul (generator i) f)

/-- Repeated dots retain their nonzero square: no exterior relation is imposed. -/
theorem denoteValue_same {n : ℕ} (i : Dot n) :
    denoteValue [i, i] = monomial (expSingle i + expSingle i) 1 := by
  change mul (generator i) (mul (generator i) one) = _
  rw [mul_one, generator_square]

theorem denoteValue_same_ne_zero {n : ℕ} (i : Dot n) :
    denoteValue [i, i] ≠ 0 := by
  rw [denoteValue_same]
  exact Finsupp.single_ne_zero.mpr one_ne_zero

end OddMath.Frontier.DotContexts
