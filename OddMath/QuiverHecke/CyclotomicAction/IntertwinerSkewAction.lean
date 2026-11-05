/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightPolynomial
import Mathlib.Algebra.SkewPolynomial.Basic

/-!
# Parity-skew polynomials on the induced quotients

The right polynomial action in KKO I, Proposition 8.4. Coefficients are
written first: `c X^m` applies the coefficient and then the dots. Thus the
representation takes values in the ordinary opposite endomorphism ring,
not the super-opposite. The relation is `X c = φ(c) X`, where
`φ(c) = (-1)^(p(i)|c|) c`; no square-zero relation is imposed on `X`.
The coefficient action on the target retains its existing parity shift.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The parity sign is a ring endomorphism of the existing coefficient algebra. -/
def coefficientParityHom (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (p : ZMod 2) :
    CyclotomicAlgebra D Sc a n →+* CyclotomicAlgebra D Sc a n where
  toFun := (cyclotomicSuperspace D Sc a ha n).sgn p
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [SVec.sgn_apply_of_mem p (show (1 : CyclotomicAlgebra D Sc a n) ∈
      cyclotomicParity D Sc a ha n 0 from SetLike.GradedOne.one_mem)]
    simp
  map_mul' b c := by
    induction b using SuperBimodule.alg_induction_on (cyclotomicParity D Sc a ha n) with
    | zero => simp
    | add b b' hb hb' => simp only [add_mul, map_add, hb, hb']
    | hom q b hb =>
      induction c using SuperBimodule.alg_induction_on (cyclotomicParity D Sc a ha n) with
      | zero => simp
      | add c c' hc hc' => simp only [mul_add, map_add, hc, hc']
      | hom r c hc =>
        have hbc : b * c ∈ cyclotomicParity D Sc a ha n (q + r) :=
          SetLike.GradedMul.mul_mem hb hc
        rw [SVec.sgn_apply_of_mem p hbc,
          SVec.sgn_apply_of_mem p hb, SVec.sgn_apply_of_mem p hc]
        simp only [add_mul, sign_add, smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [mul_comm (sign k (q * p))]

/-- Powers of the parity twist, as the action required by Mathlib skew polynomials. -/
@[instance_reducible] def coefficientParityAction (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    MulSemiringAction (Multiplicative ℕ) (CyclotomicAlgebra D Sc a n) where
  smul m := coefficientParityHom D Sc a ha n ((m.toAdd : ZMod 2) * D.parity i)
  smul_zero m := map_zero _
  smul_add m := map_add _
  smul_one m := map_one _
  smul_mul m := map_mul _
  one_smul b := by
    change (cyclotomicSuperspace D Sc a ha n).sgn ((0 : ZMod 2) * D.parity i) b = b
    simp
  mul_smul m l b := by
    change (cyclotomicSuperspace D Sc a ha n).sgn
      (((m.toAdd + l.toAdd : ℕ) : ZMod 2) * D.parity i) b =
      ((cyclotomicSuperspace D Sc a ha n).sgn ((m.toAdd : ZMod 2) * D.parity i))
        ((cyclotomicSuperspace D Sc a ha n).sgn ((l.toAdd : ZMod 2) * D.parity i) b)
    rw [← LinearMap.comp_apply, SVec.sgn_comp_sgn, Nat.cast_add, add_mul]

end OddMath.QuiverHecke
