import OddMath.QuiverHecke.CyclotomicAction.IntertwinerDotGrading
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerDotGrading then
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
namespace IntertwinerDotGradingConsumer

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

/-- Typed consumers on the existing quotients; these do not prove nonvanishing or inversion. -/
example := @sourceRightDot_parity Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true polys (polys_parity datum) 2
example := @targetRightDot_parity Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2
example := @rightDot_Q_square Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2
example := @rightDot_Q_gradedSquare Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true ({false, true, false} : Multiset Bool) polys (polys_parity datum) 2
example := @sourceRightDot_parity Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true polys (polys_parity mixedDatum) 1
example := @targetRightDot_parity Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1
example := @rightDot_Q_square Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1
example := @rightDot_Q_gradedSquare Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1

#print axioms sourceRightDot_parity
#print axioms targetRightDot_parity
#print axioms rightDot_Q_gradedSquare
end IntertwinerDotGradingConsumer
