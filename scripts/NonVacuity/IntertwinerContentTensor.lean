import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContentTensor
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerContentTensor then
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
namespace IntertwinerContentTensorConsumer

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

example (z : contentSourceTensor datum scalars true {false, true, false} polys 2) :=
  contentSourceBackward_forward datum scalars true {false, true, false} polys 2 z

example (z : qSourceContent mixedDatum mixedScalars true {false, true} polys 1) :
    contentSourceEquiv mixedDatum mixedScalars true {false, true} polys 1
      ((contentSourceEquiv mixedDatum mixedScalars true {false, true} polys 1).symm z) = z :=
  (contentSourceEquiv mixedDatum mixedScalars true {false, true} polys 1).apply_symm_apply z

example (x : InductionAlong.Corner (appendAlgebra mixedDatum mixedScalars true 2 :
    Hn mixedDatum mixedScalars 2 →ₙ+* Hn mixedDatum mixedScalars 3))
    (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  contentTensorQ_representative mixedDatum mixedScalars true {false, true} polys 1
    (polys_parity mixedDatum) x b

example (x : InductionAlong.Corner (appendAlgebra datum scalars true 3 :
    Hn datum scalars 3 →ₙ+* Hn datum scalars 4))
    (b : CyclotomicAlgebra datum scalars polys 2) :=
  contentTensorQ_representative datum scalars true {false, true, false} polys 2
    (polys_parity datum) x b

example (x : InductionAlong.Corner (appendAlgebra mixedDatum mixedScalars false 2 :
    Hn mixedDatum mixedScalars 2 →ₙ+* Hn mixedDatum mixedScalars 3))
    (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  contentSourceEquiv_representative mixedDatum mixedScalars false {false, false} polys 1 x b

#print axioms contentSourceEquiv
#print axioms contentSourceBackward_forward
#print axioms contentSourceForward_backward
#print axioms contentSourceCorner_support
#print axioms contentTensorQ_representative
end IntertwinerContentTensorConsumer
