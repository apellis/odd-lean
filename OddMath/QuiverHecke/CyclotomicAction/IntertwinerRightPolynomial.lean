/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightCoefficient
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Finite right polynomial operators for the moving-strand map

For KKO I, arXiv:1206.5933v2, Proposition 8.4, evaluate ordered finite
polynomials `∑ t^m ⊗ c_m` on the existing source and target quotients.
The order is dot first, coefficient second; composition reverses products.
For homogeneous `b` of degree `q`, multiplying the monomials `t^r ⊗ b`
and `t^s ⊗ c` contributes `(-1)^(s p(i) q)`. All natural exponents
are retained, with no square-zero relation on an odd variable.

This module proves finite-sum equivariance and the signed monomial action
law. The coefficient family is a finitely supported function, not yet a
bundled supertensor algebra. Its multiplication and comparison with the
source's `k[t_i]` supertensor cyclotomic algebra remain to be supplied.
Mathlib's `SkewPolynomial` uses the alternative order `c t^m`.
The finite-colour, positive-height and polynomial-parity restrictions remain.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

private theorem dot_pow_coefficient {V : Type*} [AddCommGroup V] [Module k V]
    (T C : Module.End k V) (e : k) (h : T * C = e • (C * T)) (s : ℕ) :
    T ^ s * C = e ^ s • (C * T ^ s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, h,
      smul_mul_assoc, smul_smul, ← pow_succ', mul_assoc, ← pow_succ]
    rw [← pow_succ']

end OddMath.QuiverHecke
