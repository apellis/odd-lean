import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContentDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerContentDot then
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
open scoped TensorProduct BigOperators
namespace IntertwinerContentDotConsumer

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


example (z : contentSourceTensor datum scalars true {false, true} polys 1) :=
  contentTensorShiftedQ_rightDot datum scalars true {false, true} polys (polys_parity datum) 1 z

example (x : InductionAlong.Corner (qPrependAlgebra datum scalars true {false, true} 1))
    (b : CyclotomicAlgebra datum scalars polys 1) :=
  contentTargetRightDot_insert datum scalars true {false, true} polys (polys_parity datum) 1 x b

example (x : InductionAlong.Corner (qPrependAlgebra datum scalars true {false, true} 1)) :
    (contentTargetDotCorner datum scalars true {false, true} 1 x).1 =
      x.1 * affineFirstDot datum scalars true (1 + 1) := rfl

example (z : contentSourceTensor datum scalars true {false, true, false} polys 2) :=
  contentTensorShiftedQ_rightDot datum scalars true {false, true, false} polys (polys_parity datum) 2 z

example (x : InductionAlong.Corner (qPrependAlgebra datum scalars true {false, true, false} 2))
    (b : CyclotomicAlgebra datum scalars polys 2) :=
  contentTargetRightDot_insert datum scalars true {false, true, false} polys (polys_parity datum) 2 x b

example (x : InductionAlong.Corner (qPrependAlgebra datum scalars true {false, true, false} 2)) :
    (contentTargetDotCorner datum scalars true {false, true, false} 2 x).1 =
      x.1 * affineFirstDot datum scalars true (2 + 1) := rfl

example (z : contentSourceTensor mixedDatum mixedScalars true {false, true} polys 1) :=
  contentTensorShiftedQ_rightDot mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1 z

example (x : InductionAlong.Corner (qPrependAlgebra mixedDatum mixedScalars true {false, true} 1))
    (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  contentTargetRightDot_insert mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1 x b

example (x : InductionAlong.Corner (qPrependAlgebra mixedDatum mixedScalars true {false, true} 1)) :
    (contentTargetDotCorner mixedDatum mixedScalars true {false, true} 1 x).1 =
      x.1 * affineFirstDot mixedDatum mixedScalars true (1 + 1) := rfl

example (z : contentSourceTensor mixedDatum mixedScalars true {true, true} polys 1) :=
  contentTensorShiftedQ_rightDot mixedDatum mixedScalars true {true, true} polys (polys_parity mixedDatum) 1 z

example (x : InductionAlong.Corner (qPrependAlgebra mixedDatum mixedScalars true {true, true} 1))
    (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  contentTargetRightDot_insert mixedDatum mixedScalars true {true, true} polys (polys_parity mixedDatum) 1 x b

example (x : InductionAlong.Corner (qPrependAlgebra mixedDatum mixedScalars true {true, true} 1)) :
    (contentTargetDotCorner mixedDatum mixedScalars true {true, true} 1 x).1 =
      x.1 * affineFirstDot mixedDatum mixedScalars true (1 + 1) := rfl

example : Supercategory.sign ℚ (datum.parity true * contentSumParity datum {false, true}) = 1 := by
  norm_num [contentSumParity, mixedDatum, datum, Supercategory.sign, OddMath.SKM.zsign]

example : Supercategory.sign ℚ (datum.parity true * contentSumParity datum {false, true, false}) = -1 := by
  norm_num [contentSumParity, mixedDatum, datum, Supercategory.sign, OddMath.SKM.zsign]

example : Supercategory.sign ℚ (mixedDatum.parity true * contentSumParity mixedDatum {false, true}) = -1 := by
  norm_num [contentSumParity, mixedDatum, datum, Supercategory.sign, OddMath.SKM.zsign]

example : Supercategory.sign ℚ (mixedDatum.parity true * contentSumParity mixedDatum {true, true}) = 1 := by
  norm_num [contentSumParity, mixedDatum, datum, Supercategory.sign, OddMath.SKM.zsign]

end IntertwinerContentDotConsumer
