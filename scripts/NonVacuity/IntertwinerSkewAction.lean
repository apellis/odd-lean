import OddMath.QuiverHecke.CyclotomicAction.IntertwinerSkewAction
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerSkewAction then
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke Categorification
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace IntertwinerSkewActionConsumer

def mixedDatum : OddMath.SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }

def mixedScalars : OddMath.SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

def polys (_ : Bool) : _root_.Polynomial ℚ := _root_.Polynomial.X ^ 4

private theorem polys_parity (D : OddMath.SKM.Datum Bool (Bool → ℤ)) :
    CyclotomicPolynomialParity D polys := by
  intro i m hm
  by_cases h : 4 = m
  · subst m; simp [polys]
  · simp [polys, Polynomial.coeff_X_pow, Ne.symm h] at hm

/-- Both coefficient shifts here are genuinely odd. -/
example : datum.parity true * contentSumParity datum ({false, true, false} : Multiset Bool) = 1 := by
  decide
example : mixedDatum.parity true * contentSumParity mixedDatum ({false, true} : Multiset Bool) = 1 := by
  decide

/-- Ring multiplication acts by right composition, including nonconstant products. -/
example : letI := coefficientParityAction datum scalars true polys (polys_parity datum) 2
    let f : _root_.SkewPolynomial (CyclotomicAlgebra datum scalars polys 2) :=
      _root_.SkewPolynomial.X + _root_.SkewPolynomial.C 1
    (sourceRightSkew datum scalars true polys (polys_parity datum) 2 (f * f)).unop =
      (sourceRightSkew datum scalars true polys (polys_parity datum) 2 f).unop * (sourceRightSkew datum scalars true polys (polys_parity datum) 2 f).unop := by
  exact sourceRightSkew_mul datum scalars true polys (polys_parity datum) 2 _ _

example := targetRightSkew_mul datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2

/-- Q equivariance for the square of a nonconstant skew polynomial. -/
example : letI := coefficientParityAction datum scalars true polys (polys_parity datum) 2
    let f : _root_.SkewPolynomial (CyclotomicAlgebra datum scalars polys 2) :=
      _root_.SkewPolynomial.X + _root_.SkewPolynomial.C 1
    (targetRightSkew datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 (f * f)).unop.comp
        (parityCyclotomicContentQLinear datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2) =
      (parityCyclotomicContentQLinear datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2).comp (sourceRightSkew datum scalars true polys (polys_parity datum) 2 (f * f)).unop := by
  exact rightSkew_Q datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 _

/-- Odd coefficient crossing one odd variable changes the normal-order sign. -/
example : let c := cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)
    coefficientParityHom datum scalars polys (polys_parity datum) 2 1 c = -c := by
  change (cyclotomicSuperspace datum scalars polys (polys_parity datum) 2).sgn 1 _ = _
  rw [SVec.sgn_apply_of_mem 1 (cyclotomicMk_parity datum scalars polys (polys_parity datum) 2
    (affineLastDot_parity datum scalars true 2))]
  simp [Supercategory.sign_one, datum]

example := sourceRightSkew_dotFirst datum scalars true polys (polys_parity datum) 2 1
  (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2))
example := targetRightSkew_coefficientFirst datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 2
  (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2))

/-- Ring multiplication acts by right composition, including nonconstant products. -/
example : letI := coefficientParityAction mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
    let f : _root_.SkewPolynomial (CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
      _root_.SkewPolynomial.X + _root_.SkewPolynomial.C 1
    (sourceRightSkew mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 (f * f)).unop =
      (sourceRightSkew mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 f).unop * (sourceRightSkew mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 f).unop := by
  exact sourceRightSkew_mul mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 _ _

example := targetRightSkew_mul mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1

/-- Q equivariance for the square of a nonconstant skew polynomial. -/
example : letI := coefficientParityAction mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
    let f : _root_.SkewPolynomial (CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
      _root_.SkewPolynomial.X + _root_.SkewPolynomial.C 1
    (targetRightSkew mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 (f * f)).unop.comp
        (parityCyclotomicContentQLinear mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1) =
      (parityCyclotomicContentQLinear mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1).comp (sourceRightSkew mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 (f * f)).unop := by
  exact rightSkew_Q mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 _

/-- Odd coefficient crossing one odd variable changes the normal-order sign. -/
example : let c := cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)
    coefficientParityHom mixedDatum mixedScalars polys (polys_parity mixedDatum) 1 1 c = -c := by
  change (cyclotomicSuperspace mixedDatum mixedScalars polys (polys_parity mixedDatum) 1).sgn 1 _ = _
  rw [SVec.sgn_apply_of_mem 1 (cyclotomicMk_parity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1
    (affineLastDot_parity mixedDatum mixedScalars true 1))]
  simp [Supercategory.sign_one, mixedDatum]

example := sourceRightSkew_dotFirst mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 1
  (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1))
example := targetRightSkew_coefficientFirst mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 2
  (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1))

#print axioms OddMath.QuiverHecke.sourceRightSkew
#print axioms OddMath.QuiverHecke.targetRightSkew
#print axioms OddMath.QuiverHecke.rightSkew_Q
#print axioms OddMath.QuiverHecke.sourceRightSkew_coefficientFirst
end IntertwinerSkewActionConsumer
