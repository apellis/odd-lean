import OddMath.QuiverHecke.CyclotomicAction.IntertwinerSupertensorScalars
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerSupertensorScalars then
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
open scoped TensorProduct
namespace IntertwinerSupertensorScalarsConsumer

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

/-- These content choices retain nonzero coefficient parity shifts. -/
example : datum.parity true * contentSumParity datum ({false, true, false} : Multiset Bool) = 1 := by decide
example : mixedDatum.parity true * contentSumParity mixedDatum ({false, true} : Multiset Bool) = 1 := by decide

example (r : ℚ) (f : Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra datum scalars polys 2) :=
  sourceRightSupertensor_smul datum scalars true polys (polys_parity datum) 2 r f

example (r : ℚ) (f : Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra datum scalars polys 2) :=
  targetRightSupertensor_smul datum scalars true polys (polys_parity datum) 2 ({false, true, false} : Multiset Bool) r f

example (r : ℚ) (f : Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra datum scalars polys 2) :=
  rightSupertensor_scalarQ datum scalars true polys (polys_parity datum) 2 ({false, true, false} : Multiset Bool) r f

example (r : ℚ) (f : Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  sourceRightSupertensor_smul mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 r f

example (r : ℚ) (f : Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  targetRightSupertensor_smul mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 ({false, true} : Multiset Bool) r f

example (r : ℚ) (f : Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  rightSupertensor_scalarQ mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 ({false, true} : Multiset Bool) r f

end IntertwinerSupertensorScalarsConsumer
