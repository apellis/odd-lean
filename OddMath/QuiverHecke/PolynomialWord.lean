/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Basic
import OddMath.QuiverHecke.Polynomial

/-!
# Polynomial coefficients attached to a quiver Hecke word

The wordwise coefficient module in Hill–Wang, arXiv:1202.2769v2,
Proposition 4.5. Positions use the left-to-right order of `QuiverHecke.ob`;
BE2 numbers its strands in the opposite order. Dot multiplication has exactly
the interchange sign of the existing quiver Hecke presentation. Crossings and
descent to `Hn` are not constructed here.
-/

noncomputable section
namespace OddMath.QuiverHecke
variable {I X R : Type*} [AddCommGroup X] [CommRing R] (D : SKM.Datum I X)

/-- The parities of a colour word in left-to-right order. -/
def wordParity (w : List I) : Fin w.length → Bool := fun r => decide (D.parity (w.get r) = 1)

/-- The mixed polynomial coefficient algebra at a colour word. -/
abbrev WordPolynomial (w : List I) := Polynomial R w.length (wordParity D w)

/-- Multiplication by the variable at the indicated position. -/
def wordDot (w : List I) (r : Fin w.length) : Module.End R (WordPolynomial (R := R) D w) :=
  Polynomial.leftRegular (wordParity D w) (Polynomial.X (wordParity D w) r)

/-- The dot operators satisfy the BE2 super interchange relation. -/
theorem wordDot_mul_swap (w : List I) (r s : Fin w.length) (h : r ≠ s) :
    wordDot (R := R) D w r * wordDot D w s =
      SKM.zsign R (D.parity (w.get r) * D.parity (w.get s)) •
        (wordDot D w s * wordDot D w r) := by
  have hp := Polynomial.X_mul_X_swap (R := R) (wordParity D w) r s h
  have hs : (if wordParity D w r = true ∧ wordParity D w s = true
      then (-1 : R) else 1) = SKM.zsign R (D.parity (w.get r) * D.parity (w.get s)) := by
    simp only [wordParity, decide_eq_true_eq, SKM.zsign]
    generalize D.parity (w.get r) = a
    generalize D.parity (w.get s) = b
    fin_cases a <;> fin_cases b <;> rfl
  rw [hs] at hp
  have hm := congrArg (Polynomial.leftRegular (R := R) (wordParity D w)) hp
  simpa only [map_mul, map_smul, wordDot] using hm

/-- An odd-coloured dot does not acquire an exterior square relation. -/
theorem wordDot_sq_ne_zero [Nontrivial R] (w : List I) (r : Fin w.length) :
    wordDot (R := R) D w r ^ 2 ≠ 0 := by
  rw [wordDot, ← map_pow]
  intro h
  apply Polynomial.X_sq_ne_zero (R := R) (wordParity D w) r
  apply Polynomial.leftRegular_injective (wordParity D w)
  simpa using h

end OddMath.QuiverHecke
