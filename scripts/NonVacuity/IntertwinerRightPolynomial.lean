import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightPolynomial
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightPolynomial then
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
namespace IntertwinerRightPolynomialConsumer

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

/-- Two nonconstant terms, including an even power of the odd variable. -/
example : let c := cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)
    let f := Finsupp.single 1 c + Finsupp.single 2 (1 : CyclotomicAlgebra datum scalars polys 2)
    (targetRightPolynomial datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 f).comp (parityCyclotomicContentQLinear datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2) =
      (parityCyclotomicContentQLinear datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2).comp (sourceRightPolynomial datum scalars true polys (polys_parity datum) 2 f) := by
  exact rightPolynomial_Q datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 _

example := sourceRightPolynomial_one datum scalars true polys (polys_parity datum) 2
example := targetRightPolynomial_one datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2

/-- Moving an odd coefficient past 1 odd dot(s) has the prescribed sign. -/
example : let b := cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)
    sourceRightMonomial datum scalars true polys (polys_parity datum) 2 1 1 * sourceRightMonomial datum scalars true polys (polys_parity datum) 2 2 b =
      -(sourceRightMonomial datum scalars true polys (polys_parity datum) 2 (2 + 1) (b * 1)) := by
  simpa only [show datum.parity true = 1 from rfl, mul_one,
    Supercategory.sign_one, neg_one_sq, pow_one, neg_one_smul, one_smul] using
    sourceRightMonomial_comp datum scalars true polys (polys_parity datum) 2 2 1 1 (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)) 1 (cyclotomicMk_parity datum scalars polys (polys_parity datum) 2
      (affineLastDot_parity datum scalars true 2))

/-- Moving an odd coefficient past 2 odd dot(s) has the prescribed sign. -/
example : let b := cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)
    sourceRightMonomial datum scalars true polys (polys_parity datum) 2 2 1 * sourceRightMonomial datum scalars true polys (polys_parity datum) 2 2 b =
      (sourceRightMonomial datum scalars true polys (polys_parity datum) 2 (2 + 2) (b * 1)) := by
  simpa only [show datum.parity true = 1 from rfl, mul_one,
    Supercategory.sign_one, neg_one_sq, pow_one, neg_one_smul, one_smul] using
    sourceRightMonomial_comp datum scalars true polys (polys_parity datum) 2 2 2 1 (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)) 1 (cyclotomicMk_parity datum scalars polys (polys_parity datum) 2
      (affineLastDot_parity datum scalars true 2))

/-- Moving an odd coefficient past 1 odd dot(s) has the prescribed sign. -/
example : let b := cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)
    targetRightMonomial datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 1 1 * targetRightMonomial datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 2 b =
      -(targetRightMonomial datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 (2 + 1) (b * 1)) := by
  simpa only [show datum.parity true = 1 from rfl, mul_one,
    Supercategory.sign_one, neg_one_sq, pow_one, neg_one_smul, one_smul] using
    targetRightMonomial_comp datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 2 1 1 (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)) 1 (cyclotomicMk_parity datum scalars polys (polys_parity datum) 2
      (affineLastDot_parity datum scalars true 2))

/-- Moving an odd coefficient past 2 odd dot(s) has the prescribed sign. -/
example : let b := cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)
    targetRightMonomial datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 2 1 * targetRightMonomial datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 2 b =
      (targetRightMonomial datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 (2 + 2) (b * 1)) := by
  simpa only [show datum.parity true = 1 from rfl, mul_one,
    Supercategory.sign_one, neg_one_sq, pow_one, neg_one_smul, one_smul] using
    targetRightMonomial_comp datum scalars true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 2 2 1 (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)) 1 (cyclotomicMk_parity datum scalars polys (polys_parity datum) 2
      (affineLastDot_parity datum scalars true 2))

/-- Two nonconstant terms, including an even power of the odd variable. -/
example : let c := cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)
    let f := Finsupp.single 1 c + Finsupp.single 2 (1 : CyclotomicAlgebra mixedDatum mixedScalars polys 1)
    (targetRightPolynomial mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 f).comp (parityCyclotomicContentQLinear mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1) =
      (parityCyclotomicContentQLinear mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1).comp (sourceRightPolynomial mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 f) := by
  exact rightPolynomial_Q mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 _

example := sourceRightPolynomial_one mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
example := targetRightPolynomial_one mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1

/-- Moving an odd coefficient past 1 odd dot(s) has the prescribed sign. -/
example : let b := cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)
    sourceRightMonomial mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 1 1 * sourceRightMonomial mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 2 b =
      -(sourceRightMonomial mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 (2 + 1) (b * 1)) := by
  simpa only [show mixedDatum.parity true = 1 from rfl, mul_one,
    Supercategory.sign_one, neg_one_sq, pow_one, neg_one_smul, one_smul] using
    sourceRightMonomial_comp mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 2 1 1 (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)) 1 (cyclotomicMk_parity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1
      (affineLastDot_parity mixedDatum mixedScalars true 1))

/-- Moving an odd coefficient past 2 odd dot(s) has the prescribed sign. -/
example : let b := cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)
    sourceRightMonomial mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 2 1 * sourceRightMonomial mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 2 b =
      (sourceRightMonomial mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 (2 + 2) (b * 1)) := by
  simpa only [show mixedDatum.parity true = 1 from rfl, mul_one,
    Supercategory.sign_one, neg_one_sq, pow_one, neg_one_smul, one_smul] using
    sourceRightMonomial_comp mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 2 2 1 (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)) 1 (cyclotomicMk_parity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1
      (affineLastDot_parity mixedDatum mixedScalars true 1))

/-- Moving an odd coefficient past 1 odd dot(s) has the prescribed sign. -/
example : let b := cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)
    targetRightMonomial mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 1 1 * targetRightMonomial mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 2 b =
      -(targetRightMonomial mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 (2 + 1) (b * 1)) := by
  simpa only [show mixedDatum.parity true = 1 from rfl, mul_one,
    Supercategory.sign_one, neg_one_sq, pow_one, neg_one_smul, one_smul] using
    targetRightMonomial_comp mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 2 1 1 (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)) 1 (cyclotomicMk_parity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1
      (affineLastDot_parity mixedDatum mixedScalars true 1))

/-- Moving an odd coefficient past 2 odd dot(s) has the prescribed sign. -/
example : let b := cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)
    targetRightMonomial mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 2 1 * targetRightMonomial mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 2 b =
      (targetRightMonomial mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 (2 + 2) (b * 1)) := by
  simpa only [show mixedDatum.parity true = 1 from rfl, mul_one,
    Supercategory.sign_one, neg_one_sq, pow_one, neg_one_smul, one_smul] using
    targetRightMonomial_comp mixedDatum mixedScalars true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 2 2 1 (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)) 1 (cyclotomicMk_parity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1
      (affineLastDot_parity mixedDatum mixedScalars true 1))

/-- The formal variable square is not killed, independently of whether a
particular quotient representation has a kernel. -/
example : (Finsupp.single 2 (1 : ℚ) : ℕ →₀ ℚ) ≠ 0 := by
  intro h
  have := congrArg (fun f : ℕ →₀ ℚ => f 2) h
  norm_num at this

#print axioms rightPolynomial_Q
#print axioms sourceRightMonomial_comp
#print axioms targetRightMonomial_comp
end IntertwinerRightPolynomialConsumer
