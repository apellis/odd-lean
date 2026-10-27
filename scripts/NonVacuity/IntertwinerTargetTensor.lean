import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetTensor
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetTensor then
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
namespace IntertwinerTargetTensorConsumer

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

example (z : contentTargetTensor mixedDatum mixedScalars true {false, true} polys
    (polys_parity mixedDatum) 1) :=
  contentTargetBackward_forward mixedDatum mixedScalars true {false, true} polys
    (polys_parity mixedDatum) 1 z

example (z : qTargetContent datum scalars true {false, true, false} polys
    (polys_parity datum) 2) :
    contentTargetEquiv datum scalars true {false, true, false} polys (polys_parity datum) 2
      ((contentTargetEquiv datum scalars true {false, true, false} polys
        (polys_parity datum) 2).symm z) = z :=
  (contentTargetEquiv datum scalars true {false, true, false} polys
    (polys_parity datum) 2).apply_symm_apply z

example (x : InductionAlong.Corner (appendAlgebra mixedDatum mixedScalars true 2 :
    Hn mixedDatum mixedScalars 2 →ₙ+* Hn mixedDatum mixedScalars 3))
    (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  contentTensorShiftedQ_representative mixedDatum mixedScalars true {false, true} polys
    (polys_parity mixedDatum) 1 x b

example (x : InductionAlong.Corner (prependAlgebra datum scalars true 3 :
    Hn datum scalars 3 →ₙ+* Hn datum scalars 4))
    (b : CyclotomicAlgebra datum scalars polys 2) :=
  contentTargetEquiv_cut_tmul datum scalars true {false, true, false} polys
    (polys_parity datum) 2 x b

example (x : InductionAlong.Corner (prependAlgebra mixedDatum mixedScalars false 2 :
    Hn mixedDatum mixedScalars 2 →ₙ+* Hn mixedDatum mixedScalars 3))
    (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  contentTargetEquiv_cut_tmul mixedDatum mixedScalars false {false, false} polys
    (polys_parity mixedDatum) 1 x b

#print axioms contentTargetEquiv
#print axioms contentTargetBackward_forward
#print axioms contentTargetForward_backward
#print axioms contentTensorShiftedQ_representative
end IntertwinerTargetTensorConsumer
