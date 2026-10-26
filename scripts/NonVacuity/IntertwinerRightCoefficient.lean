import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightCoefficient
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightCoefficient then
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
namespace IntertwinerRightCoefficientConsumer

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

/-- Quotient-level instances only; no nonvanishing or inversion is claimed. -/
example := @rightCoefficient_Q Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2
example := @sourceRightCoefficient_one Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true polys 2
example := @targetRightCoefficient_one Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2
example := @sourceRightCoefficient_mul Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true polys 2
example := @targetRightCoefficient_mul Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2
example := @sourceRightCoefficient_add Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true polys 2
example := @targetRightCoefficient_add Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2
example := @sourceRightCoefficient_parity Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true polys (polys_parity datum) 2 1
  (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2))
  (cyclotomicMk_parity datum scalars polys (polys_parity datum) 2
    (affineLastDot_parity datum scalars true 2))
example := @targetRightCoefficient_parity Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 1
  (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2))
  (cyclotomicMk_parity datum scalars polys (polys_parity datum) 2
    (affineLastDot_parity datum scalars true 2))
example := @sourceRightDot_coefficient Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true polys (polys_parity datum) 2 1
  (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2))
  (cyclotomicMk_parity datum scalars polys (polys_parity datum) 2
    (affineLastDot_parity datum scalars true 2))
example := @targetRightDot_coefficient Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2 1
  (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2))
  (cyclotomicMk_parity datum scalars polys (polys_parity datum) 2
    (affineLastDot_parity datum scalars true 2))

/-- A concrete odd last dot supplies the homogeneous cyclotomic coefficient. -/
example : let c := cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)
    (sourceRightDotLinear datum scalars true polys (polys_parity datum) 2).comp
        (sourceRightCoefficientLinear datum scalars true polys (polys_parity datum) 2 c) =
      -(sourceRightCoefficientLinear datum scalars true polys (polys_parity datum) 2 c).comp
        (sourceRightDotLinear datum scalars true polys (polys_parity datum) 2) := by
  simpa only [show datum.parity true = 1 from rfl, mul_one,
    Supercategory.sign_one, neg_one_smul] using sourceRightDot_coefficient datum scalars true polys (polys_parity datum) 2 1
    (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2))
    (cyclotomicMk_parity datum scalars polys (polys_parity datum) 2
      (affineLastDot_parity datum scalars true 2))
example := @rightCoefficient_Q Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1
example := @sourceRightCoefficient_one Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true polys 1
example := @targetRightCoefficient_one Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1
example := @sourceRightCoefficient_mul Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true polys 1
example := @targetRightCoefficient_mul Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1
example := @sourceRightCoefficient_add Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true polys 1
example := @targetRightCoefficient_add Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1
example := @sourceRightCoefficient_parity Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true polys (polys_parity mixedDatum) 1 1
  (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1))
  (cyclotomicMk_parity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1
    (affineLastDot_parity mixedDatum mixedScalars true 1))
example := @targetRightCoefficient_parity Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 1
  (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1))
  (cyclotomicMk_parity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1
    (affineLastDot_parity mixedDatum mixedScalars true 1))
example := @sourceRightDot_coefficient Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true polys (polys_parity mixedDatum) 1 1
  (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1))
  (cyclotomicMk_parity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1
    (affineLastDot_parity mixedDatum mixedScalars true 1))
example := @targetRightDot_coefficient Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1 1
  (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1))
  (cyclotomicMk_parity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1
    (affineLastDot_parity mixedDatum mixedScalars true 1))

/-- A concrete odd last dot supplies the homogeneous cyclotomic coefficient. -/
example : let c := cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)
    (sourceRightDotLinear mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1).comp
        (sourceRightCoefficientLinear mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 c) =
      -(sourceRightCoefficientLinear mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 c).comp
        (sourceRightDotLinear mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1) := by
  simpa only [show mixedDatum.parity true = 1 from rfl, mul_one,
    Supercategory.sign_one, neg_one_smul] using sourceRightDot_coefficient mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 1
    (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1))
    (cyclotomicMk_parity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1
      (affineLastDot_parity mixedDatum mixedScalars true 1))

#print axioms rightCoefficient_Q
#print axioms sourceRightDot_coefficient
#print axioms targetRightDot_coefficient
end IntertwinerRightCoefficientConsumer
