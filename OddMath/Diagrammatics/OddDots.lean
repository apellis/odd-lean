import OddMath.SkewPolynomial

/-!
# Rank-two odd-dot bridge: diagram syntax denoted in the skew-polynomial model

Source: Ellis-Khovanov-Lauda, arXiv:1111.1320v1, §2.1.1, (2.1), p.3 (distinct
generators anticommute; local text-layer copy
an unpublished note). Convention
authority: the sign convention (increasing-index canonical order, Koszul
reorder signs) and the translation table.

A rank-two dot diagram is a chronological list of dots, bottom-first: `DotSeq`
is `List (Fin 2)` where `0` is strand 1 (`x₁`) and `1` is strand 2 (`x₂`).
`denote` sends a diagram to an operator on `SkewPolynomial 2` — the bottom dot
is applied first, matching the `seq below above = above ∘ below` direction of
`OddMath.Diagrammatics.Even` — and `denoteValue` evaluates on the vacuum `one`.

Each dot is left multiplication by the corresponding generator, so all
statements below are proved from the actual published algebra interface
(`mul_monomial`, `mul_assoc`, `mul_add`, `mul_zero`, `mul_one`,
`generator_anticommute`, `generator_square`): no quotient theorem is assumed,
no bare-word identification is used (every rewrite passes through monomial
values and evaluated coordinates), and the signed exchange acts on the linear
envelope.

Dots carry super parity `1`, stored separately from the homological degree `2`
(EKL p.22: parity is half the Z-degree).

This is ONLY the rank-two diagram-to-algebra bridge. It is not a quotient
presentation, not a PBW theorem, and not the odd nilHecke relations.
-/

namespace OddMath.Diagrammatics.OddDots

open OddMath.SkewPolynomial

set_option linter.dupNamespace false

/-- Rank-two dot positions: `0` is strand 1, `1` is strand 2. -/
abbrev Dot := Fin 2

/-- A dot diagram: chronological list of dots, bottom-first. -/
abbrev DotSeq := List Dot

/-- Super parity of an odd dot: `1`, stored separately from the degree. -/
def dotParity (_ : Dot) : ℕ := 1

/-- Homological degree of an odd dot: `2` (EKL p.22). -/
def dotDegree (_ : Dot) : ℕ := 2

theorem dotParity_eq (d : Dot) : dotParity d = 1 := rfl

theorem dotDegree_eq (d : Dot) : dotDegree d = 2 := rfl

/-- Diagram denotation as operators: the bottom dot is applied first, the rest
on top of its output. -/
noncomputable def denote : DotSeq → SkewPolynomial 2 → SkewPolynomial 2
  | [], f => f
  | i :: is, f => denote is (mul (generator i) f)

/-- Diagram value: denotation applied to the vacuum `one`. -/
noncomputable def denoteValue (l : DotSeq) : SkewPolynomial 2 := denote l one

/-! ## Structural interface: composition and linearity -/

theorem denote_nil (f : SkewPolynomial 2) : denote [] f = f := rfl

theorem denote_cons (i : Dot) (l : DotSeq) (f : SkewPolynomial 2) :
    denote (i :: l) f = denote l (mul (generator i) f) := rfl

theorem denote_singleton (i : Dot) (f : SkewPolynomial 2) :
    denote [i] f = mul (generator i) f := rfl

theorem denote_zero (l : DotSeq) : denote l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons i is ih => rw [denote_cons, mul_zero, ih]

theorem denote_add (l : DotSeq) (f g : SkewPolynomial 2) :
    denote l (f + g) = denote l f + denote l g := by
  induction l generalizing f g with
  | nil => rfl
  | cons i is ih =>
      rw [denote_cons, denote_cons, denote_cons, mul_add, ih]

/-- Vertical composition: `l₁ ++ l₂` denotes `denote l₂ ∘ denote l₁`
(`seq below above = above ∘ below`). -/
theorem denote_append (l₁ l₂ : DotSeq) (f : SkewPolynomial 2) :
    denote (l₁ ++ l₂) f = denote l₂ (denote l₁ f) := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons i t ih =>
      show denote (t ++ l₂) (mul (generator i) f)
        = denote l₂ (denote t (mul (generator i) f))
      exact ih _

/-! ## Fixture values F1 (the two dot orders) -/

/-- F1a `[d0,d1] = x₂x₁ = -x₁x₂`: one crossing. -/
theorem denoteValue_pair_neg :
    denoteValue [0, 1] = monomial ![1, 1] (-1) := by
  show mul (generator (1 : Fin 2)) (mul (generator (0 : Fin 2)) one)
    = monomial ![1, 1] (-1)
  rw [mul_one, mul_generator]
  have hexp : expSingle (1 : Fin 2) + expSingle 0 = ![1, 1] := by decide
  have hsign : OddMath.skewSign (expSingle (1 : Fin 2)) (expSingle 0) = -1 := by
    decide
  rw [hexp, hsign]

/-- F1b `[d1,d0] = x₁x₂`: zero crossings. -/
theorem denoteValue_pair_pos :
    denoteValue [1, 0] = monomial ![1, 1] 1 := by
  show mul (generator (0 : Fin 2)) (mul (generator (1 : Fin 2)) one)
    = monomial ![1, 1] 1
  rw [mul_one, mul_generator]
  have hexp : expSingle (0 : Fin 2) + expSingle 1 = ![1, 1] := by decide
  have hsign : OddMath.skewSign (expSingle (0 : Fin 2)) (expSingle 1) = 1 := by
    decide
  rw [hexp, hsign]

theorem denoteValue_ordered_coordinate :
    denoteValue [0, 1] ![1, 1] = -1 := by
  rw [denoteValue_pair_neg]
  exact Finsupp.single_eq_same

theorem denoteValue_reversed_coordinate :
    denoteValue [1, 0] ![1, 1] = 1 := by
  rw [denoteValue_pair_pos]
  exact Finsupp.single_eq_same

/-! ## F2: signed exchange is sound (operators and values) -/

/-- F2 operator form: distinct dots signed-commute as operators on every input,
via associativity and generator anticommutation. -/
theorem signed_exchange_operator (i j : Dot) (h : i ≠ j) (f : SkewPolynomial 2) :
    denote [i, j] f + denote [j, i] f = 0 := by
  show mul (generator j) (mul (generator i) f)
    + mul (generator i) (mul (generator j) f) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul]
  have hanti : mul (generator j) (generator i)
      = -mul (generator i) (generator j) :=
    generator_anticommute j i (Ne.symm h)
  rw [hanti, neg_add_cancel, zero_mul]

/-- F2 value form on the vacuum. -/
theorem signed_exchange_value :
    denoteValue [0, 1] + denoteValue [1, 0] = 0 :=
  signed_exchange_operator 0 1 (by decide) one

/-! ## F3: the unsigned difference (proved non-equality) -/

theorem monomial_single_add (a : Fin 2 → ℕ) (r s : ℤ) :
    monomial a r + monomial a s = monomial a (r + s) :=
  (Finsupp.single_add a r s).symm

/-- F3a: the unsigned difference is the doubled monomial `-2x₁x₂`. -/
theorem unsigned_difference_value :
    denoteValue [0, 1] - denoteValue [1, 0] = monomial ![1, 1] (-2) := by
  have hcoeff : (-1 : ℤ) + (-1) = -2 := by decide
  rw [denoteValue_pair_neg, denoteValue_pair_pos, sub_eq_add_neg, ← monomial_neg,
    monomial_single_add, hcoeff]

/-- F3b: the unsigned difference does not vanish. -/
theorem unsigned_difference_ne_zero :
    denoteValue [0, 1] - denoteValue [1, 0] ≠ 0 := by
  rw [unsigned_difference_value]
  exact Finsupp.single_ne_zero.mpr (by decide : (-2 : ℤ) ≠ 0)

/-- F3c: evaluated coordinate of the unsigned difference. -/
theorem unsigned_difference_coordinate :
    (denoteValue [0, 1] - denoteValue [1, 0]) ![1, 1] = -2 := by
  rw [unsigned_difference_value]
  exact Finsupp.single_eq_same

/-! ## F4: same-strand dots do not vanish -/

/-- F4a: a doubled dot is the doubled-exponent monomial (no exterior law). -/
theorem denoteValue_same (i : Dot) :
    denoteValue [i, i] = monomial (expSingle i + expSingle i) 1 := by
  show mul (generator i) (mul (generator i) one) = _
  rw [mul_one]
  exact generator_square i

/-- F4b: `[d0,d0] = x₁²`. -/
theorem denoteValue_same_zero : denoteValue [0, 0] = monomial ![2, 0] 1 := by
  rw [denoteValue_same]
  have hexp : expSingle (0 : Fin 2) + expSingle 0 = ![2, 0] := by decide
  rw [hexp]

theorem denoteValue_same_zero_ne : denoteValue [0, 0] ≠ 0 := by
  rw [denoteValue_same_zero]
  exact Finsupp.single_ne_zero.mpr one_ne_zero

theorem denoteValue_same_zero_coordinate :
    denoteValue [0, 0] ![2, 0] = 1 := by
  rw [denoteValue_same_zero]
  exact Finsupp.single_eq_same

/-! ## F5: the length-three stack -/

/-- Generators are unit-coefficient monomials, definitionally. -/
theorem generator_eq_monomial (i : Fin 2) :
    generator i = monomial (expSingle i) 1 := rfl

/-- F5: `[d0,d1,d0] = x₁x₂x₁ = -x₁²x₂`. -/
theorem denoteValue_triple :
    denoteValue [0, 1, 0] = monomial ![2, 1] (-1) := by
  have h1 : denote [0, 1, 0] (one : SkewPolynomial 2)
      = mul (generator (0 : Fin 2))
        (mul (generator (1 : Fin 2)) (generator (0 : Fin 2))) := by
    calc denote [0, 1, 0] (one : SkewPolynomial 2)
        = denote [1, 0] (mul (generator (0 : Fin 2)) one) := rfl
      _ = denote [1, 0] (generator (0 : Fin 2)) := by rw [mul_one]
      _ = mul (generator (0 : Fin 2))
            (mul (generator (1 : Fin 2)) (generator (0 : Fin 2))) := rfl
  show denote [0, 1, 0] one = _
  rw [h1, ← mul_assoc, mul_generator, generator_eq_monomial, mul_monomial]
  congr 1; decide

end OddMath.Diagrammatics.OddDots
