import OddMath
import Categorification.Algebra.NilHeckeSplitting

/-! Concrete integral consumers of the classical nilHecke dependency for the even-colour
input to BE2 Lemma 11.1. These are polynomial-operator identities, not yet a comparison
with the same-colour corner of `H_n`. -/

open Categorification.NilHecke

example : IsIdempotentElem (idemNH ℤ 0) := isIdempotentElem_idemNH
example : IsIdempotentElem (idemNH ℤ 1) := isIdempotentElem_idemNH
example : IsIdempotentElem (idemNH ℤ 2) := isIdempotentElem_idemNH

example : nhB ℤ 1 0 * nhA ℤ 1 0 = idemNH ℤ 2 := by
  simpa using (nhB_mul_nhA (k := ℤ) (n := 1) (i := 0) (j := 0)
    (by decide) (by decide))

example : nhB ℤ 1 0 * nhA ℤ 1 1 = 0 := by
  simpa using (nhB_mul_nhA (k := ℤ) (n := 1) (i := 0) (j := 1)
    (by decide) (by decide))

example : ∑ j : Fin 2, nhA ℤ 1 j * nhB ℤ 1 j = nhE' ℤ 1 :=
  sum_nhA_mul_nhB

example : (1 : MvPolynomial (Fin 2) ℤ) ≠ 0 := one_ne_zero

#print axioms Categorification.NilHecke.isIdempotentElem_idemNH
#print axioms Categorification.NilHecke.nhB_mul_nhA
#print axioms Categorification.NilHecke.sum_nhA_mul_nhB
