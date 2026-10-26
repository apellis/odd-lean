import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if #[`OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightDot,
        `OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetDot].contains
        env.header.moduleNames[i]! then
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
namespace IntertwinerRightDotConsumer

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

/-- These are nonzero-shift contents for Q, not even-only tests. -/
example : datum.parity true * contentSumParity datum ({false, true, false} : Multiset Bool) = 1 := by decide
example : mixedDatum.parity true * contentSumParity mixedDatum ({false, true} : Multiset Bool) = 1 := by decide

example (b : CyclotomicAlgebra datum scalars polys 2) :=
  sourceRightDot_tmul datum scalars true polys (polys_parity datum) 2
    (InductionAlong.unitGen (appendAlgebra datum scalars true 3 :
      Hn datum scalars 3 →ₙ+* Hn datum scalars 4)) b

example (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  sourceRightDot_tmul mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
    (InductionAlong.unitGen (appendAlgebra mixedDatum mixedScalars true 2 :
      Hn mixedDatum mixedScalars 2 →ₙ+* Hn mixedDatum mixedScalars 3)) b

example (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1)
    (hb : b ∈ cyclotomicParity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1 1) :
    rightDotCoefficient mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 b = -b := by
  simpa [mixedDatum] using rightDotCoefficient_of_mem mixedDatum mixedScalars true polys
    (polys_parity mixedDatum) 1 1 b hb

/-- All-odd content of height three retains the nonzero coefficient shift. -/
example :
    (targetRightDot datum scalars true {false, true, false} polys (polys_parity datum) 2).comp
        (parityCyclotomicContentQ datum scalars true {false, true, false} polys (polys_parity datum) 2) =
      (parityCyclotomicContentQ datum scalars true {false, true, false} polys (polys_parity datum) 2).comp
        (sourceRightDot datum scalars true polys (polys_parity datum) 2) :=
  targetRightDot_Q datum scalars true {false, true, false} polys (polys_parity datum) 2

/-- Mixed content on the same balanced quotient, with odd moving colour. -/
example :
    (targetRightDot mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1).comp
        (parityCyclotomicContentQ mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1) =
      (parityCyclotomicContentQ mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1).comp
        (sourceRightDot mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1) :=
  targetRightDot_Q mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1

example (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1) :
    (qCoefficient mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1).toSVec.sgn 1
        (qCoefficientInsert mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1 b) =
      -(qCoefficientInsert mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1
        (rightDotCoefficient mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 b)) := by
  simpa [mixedDatum, contentSumParity] using targetDotCoefficient_insert mixedDatum mixedScalars
    true {false, true} polys (polys_parity mixedDatum) 1 b

example (b : CyclotomicAlgebra datum scalars polys 2) :=
  LinearMap.congr_fun
    (targetRightDot_Q datum scalars true {false, true, false} polys (polys_parity datum) 2)
    (InductionAlong.Ind.tmul
      (InductionAlong.unitGen (appendAlgebra datum scalars true 3 :
        Hn datum scalars 3 →ₙ+* Hn datum scalars 4)) b)

example (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  LinearMap.congr_fun
    (targetRightDot_Q mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1)
    (InductionAlong.Ind.tmul
      (InductionAlong.unitGen (appendAlgebra mixedDatum mixedScalars true 2 :
        Hn mixedDatum mixedScalars 2 →ₙ+* Hn mixedDatum mixedScalars 3)) b)

end IntertwinerRightDotConsumer
