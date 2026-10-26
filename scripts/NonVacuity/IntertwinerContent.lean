import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContent
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerContent then
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
namespace IntertwinerContentConsumer

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

example : datum.parity true * contentSumParity datum ({false, true, false} : Multiset Bool) = 1 := by decide
example : mixedDatum.parity true * contentSumParity mixedDatum ({false, true} : Multiset Bool) = 1 := by decide

example (x : InductionAlong.Corner (appendAlgebra datum scalars true 3 :
    Hn datum scalars 3 →ₙ+* Hn datum scalars 4))
    (b : CyclotomicAlgebra datum scalars polys 2) :=
  contentCornerQ_tmul datum scalars true {false, true, false} polys (polys_parity datum) 2 x b

example (x : InductionAlong.Corner (prependAlgebra mixedDatum mixedScalars true 2 :
    Hn mixedDatum mixedScalars 2 →ₙ+* Hn mixedDatum mixedScalars 3))
    (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  targetContentRightDot_tmul mixedDatum mixedScalars true {false, true} polys
    (polys_parity mixedDatum) 1 x b

example (c : CyclotomicAlgebra datum scalars polys 2)
    (z : qSourceContent datum scalars true {false, true, false} polys 2) :=
  contentCornerQ_rightCoefficient datum scalars true {false, true, false} polys
    (polys_parity datum) 2 c z

example (z : qSourceContent mixedDatum mixedScalars true {false, true} polys 1) :=
  contentCornerQ_rightDot mixedDatum mixedScalars true {false, true} polys
    (polys_parity mixedDatum) 1 z

example (r : Hn mixedDatum mixedScalars 3)
    (z : qSourceContent mixedDatum mixedScalars true {false, true} polys 1) :=
  contentCornerQ_left mixedDatum mixedScalars true {false, true} polys
    (polys_parity mixedDatum) 1 r z

/-- The cut representatives determine maps on the whole fixed-content source. -/
example (f g : qSourceContent mixedDatum mixedScalars true {false, true} polys 1 →ₗ[
      Hn mixedDatum mixedScalars 3] qTargetContent mixedDatum mixedScalars true
        {false, true} polys (polys_parity mixedDatum) 1)
    (h : ∀ x b, f (sourceContentTensor mixedDatum mixedScalars true {false, true} polys 1 x b) =
      g (sourceContentTensor mixedDatum mixedScalars true {false, true} polys 1 x b)) : f = g := by
  apply LinearMap.ext
  intro z
  induction z using sourceContent_induction with
  | hzero => exact (map_zero f).trans (map_zero g).symm
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | htmul x b => exact h x b

#print axioms contentCornerQ
#print axioms contentCornerQ_tmul
#print axioms sourceContent_induction
#print axioms targetContent_induction
#print axioms contentCornerQ_rightCoefficient
#print axioms contentCornerQ_rightDot
#print axioms targetContentRightDot_tmul
end IntertwinerContentConsumer
