/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# The Clifford factor in distant quiver Hecke crossings

Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, Theorem 3.13, proof (a),
after (3.19), multiplies an even crossing by a Clifford difference when
both colours are odd. This file proves the resulting distant sign from
its four Clifford anticommutation relations and the even crossing
commutations. It does not assume the desired distant crossing relation.

This is a local algebra calculation, not yet a representation of `Hn`.
-/

namespace OddMath.QuiverHecke.CliffordExchange
variable {A : Type*} [Ring A]

/-- Clifford differences on disjoint pairs anticommute. -/
theorem difference_anticommute (a b c d : A)
    (hac : a * c = -(c * a)) (had : a * d = -(d * a))
    (hbc : b * c = -(c * b)) (hbd : b * d = -(d * b)) :
    (a - b) * (c - d) = -((c - d) * (a - b)) := by
  simp only [sub_mul, mul_sub, hac, had, hbc, hbd]
  noncomm_ring

/-- Dressing commuting even crossings by anticommuting remote factors
produces the required odd distant supercommutation. -/
theorem dressed_anticommute (a b s t : A) (hab : a * b = -(b * a))
    (hsb : Commute s b) (hta : Commute t a) (hst : Commute s t) :
    (a * s) * (b * t) = -((b * t) * (a * s)) := by
  calc
    (a * s) * (b * t) = a * (s * b) * t := by noncomm_ring
    _ = a * (b * s) * t := by rw [hsb.eq]
    _ = (a * b) * (s * t) := by noncomm_ring
    _ = -(b * a) * (t * s) := by rw [hab, hst.eq]
    _ = -(b * (a * t) * s) := by noncomm_ring
    _ = -(b * (t * a) * s) := by rw [hta.eq]
    _ = -((b * t) * (a * s)) := by noncomm_ring

/-- The Clifford part is present precisely for an odd–odd pair. -/
def factor (a b : A) (p : Bool) : A := if p then a - b else 1

/-- KKT's distant supercommutation calculation, for every pair of crossing parities.
The hypotheses are individual Clifford and even-crossing relations; there is no
hypothesis about the composite dressed crossings. -/
theorem distant (a b c d s t : A) (p q : Bool)
    (hac : a * c = -(c * a)) (had : a * d = -(d * a))
    (hbc : b * c = -(c * b)) (hbd : b * d = -(d * b))
    (hsc : Commute s c) (hsd : Commute s d)
    (hta : Commute t a) (htb : Commute t b) (hst : Commute s t) :
    (factor a b p * s) * (factor c d q * t) =
      (if p && q then -1 else 1) * ((factor c d q * t) * (factor a b p * s)) := by
  have hsdiff : Commute s (c - d) := hsc.sub_right hsd
  have htdiff : Commute t (a - b) := hta.sub_right htb
  cases p <;> cases q <;> simp only [factor, Bool.false_eq_true, ite_false,
    ite_true, Bool.false_and, Bool.true_and, one_mul, neg_one_mul]
  · exact hst.eq
  · calc
      s * ((c - d) * t) = (c - d) * (s * t) := by rw [← mul_assoc, hsdiff.eq, mul_assoc]
      _ = (c - d) * (t * s) := by rw [hst.eq]
      _ = ((c - d) * t) * s := by rw [mul_assoc]
  · calc
      ((a - b) * s) * t = (a - b) * (t * s) := by rw [mul_assoc, hst.eq]
      _ = t * ((a - b) * s) := by rw [← mul_assoc, ← htdiff.eq, mul_assoc]
  · exact dressed_anticommute (a - b) (c - d) s t
      (difference_anticommute a b c d hac had hbc hbd) hsdiff htdiff hst

end OddMath.QuiverHecke.CliffordExchange
