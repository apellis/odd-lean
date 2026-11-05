/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerGrading
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetDot

/-!
# Right cyclotomic coefficients on the moving-strand quotients

The coefficient portion of KKO I, arXiv:1206.5933v2, Proposition 8.4.
Right multiplication descends on the existing integral balanced quotients.
The target uses the right action of the parity-shifted regular superbimodule;
its canonical insertion is right-linear without an additional sign.
Composition of right operators reverses multiplication. The dot/coefficient
relation is the supertensor relation, not square-zero for an odd variable.
The finite-colour, positive-height and polynomial-parity restrictions remain;
this does not assert the full content-corner statement of Proposition 8.4.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Right multiplication commutes with the affine action on the coefficient quotient. -/
def sourceCoefficientRight (a : I → _root_.Polynomial k) (n : ℕ)
    (c : CyclotomicAlgebra D Sc a n) :
    Module.End (Hn D Sc (n + 1)) (CyclotomicAlgebra D Sc a n) where
  toFun b := b * c
  map_add' b b' := add_mul b b' c
  map_smul' r b := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact congrArg (cyclotomicMk D Sc a n) (mul_assoc r b c)

/-- The shifted coefficient right action still commutes with its twisted left action. -/
def targetCoefficientRight (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    Module.End (Hn D Sc (n + 1)) (qCoefficient D Sc i β a ha n).toSVec where
  toFun := (qCoefficient D Sc i β a ha n).ract c
  map_add' := SVec.hom_map_add _
  map_smul' r b := congrArg (fun f => f b)
    ((qCoefficient D Sc i β a ha n).lact_ract (cyclotomicMk D Sc a n r) c)

/-- Descended coefficient multiplication on the source quotient. -/
def sourceRightCoefficient (i : I) (a : I → _root_.Polynomial k) (n : ℕ)
    (c : CyclotomicAlgebra D Sc a n) :=
  InductionAlong.Ind.map (φ := (appendAlgebra D Sc i (n + 1) :
    Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) (sourceCoefficientRight D Sc a n c)

/-- Descended shifted right action on the target quotient. -/
def targetRightCoefficient (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (c : CyclotomicAlgebra D Sc a n) :=
  InductionAlong.Ind.map (φ := (prependAlgebra D Sc i (n + 1) :
    Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) (targetCoefficientRight D Sc i β a ha n c)

@[simp] theorem targetRightCoefficient_tmul (i : I) (β : Multiset I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (c : CyclotomicAlgebra D Sc a n)
    (x : InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : (qCoefficient D Sc i β a ha n).toSVec) :
    targetRightCoefficient D Sc i β a ha n c (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul x ((qCoefficient D Sc i β a ha n).ract c b) := rfl

end OddMath.QuiverHecke
