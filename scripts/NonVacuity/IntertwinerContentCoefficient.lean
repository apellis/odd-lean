import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContentCoefficient
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerContentCoefficient then
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
namespace IntertwinerContentCoefficientConsumer

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

example (c : CyclotomicAlgebra mixedDatum mixedScalars polys 1)
    (z : contentSourceTensor mixedDatum mixedScalars true {false, true} polys 1) :=
  contentTensorShiftedQ_rightCoefficient mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1 c z

example (c : CyclotomicAlgebra mixedDatum mixedScalars polys 1)
    (x : InductionAlong.Corner (qPrependAlgebra mixedDatum mixedScalars true {false, true} 1))
    (b : qContentCoefficient mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1) :=
  contentTargetRightCoefficient_tmul mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1 c x b

example (c : CyclotomicAlgebra mixedDatum mixedScalars polys 1)
    (x : InductionAlong.Corner (ContentTensor.append
      (appendAlgebra mixedDatum mixedScalars true 2 : Hn mixedDatum mixedScalars 2 →ₙ+* Hn mixedDatum mixedScalars 3)
      (contentIdempotent mixedDatum mixedScalars 2 {false, true}) (contentIdempotent_sq mixedDatum mixedScalars 2 {false, true})))
    (b : ContentTensor.Coefficient (cyclotomicMk mixedDatum mixedScalars polys 1).toRingHom
      (contentIdempotent mixedDatum mixedScalars 2 {false, true}) (contentIdempotent_sq mixedDatum mixedScalars 2 {false, true})) :=
  contentSourceRightCoefficient_tmul mixedDatum mixedScalars true {false, true} polys 1 c x b

example (c : CyclotomicAlgebra datum scalars polys 2)
    (z : contentSourceTensor datum scalars true {false, true, false} polys 2) :=
  contentTensorShiftedQ_rightCoefficient datum scalars true {false, true, false} polys (polys_parity datum) 2 c z

example (c : CyclotomicAlgebra datum scalars polys 2)
    (x : InductionAlong.Corner (qPrependAlgebra datum scalars true {false, true, false} 2))
    (b : qContentCoefficient datum scalars true {false, true, false} polys (polys_parity datum) 2) :=
  contentTargetRightCoefficient_tmul datum scalars true {false, true, false} polys (polys_parity datum) 2 c x b

example (c : CyclotomicAlgebra datum scalars polys 2)
    (x : InductionAlong.Corner (ContentTensor.append
      (appendAlgebra datum scalars true 3 : Hn datum scalars 3 →ₙ+* Hn datum scalars 4)
      (contentIdempotent datum scalars 3 {false, true, false}) (contentIdempotent_sq datum scalars 3 {false, true, false})))
    (b : ContentTensor.Coefficient (cyclotomicMk datum scalars polys 2).toRingHom
      (contentIdempotent datum scalars 3 {false, true, false}) (contentIdempotent_sq datum scalars 3 {false, true, false})) :=
  contentSourceRightCoefficient_tmul datum scalars true {false, true, false} polys 2 c x b

end IntertwinerContentCoefficientConsumer
