import OddMath.QuiverHecke.CyclotomicAction.IntertwinerGrading
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerGrading then
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
namespace IntertwinerGradingConsumer

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


example (p : ZMod 2) (b : CyclotomicAlgebra datum scalars polys 2)
    (hb : b ∈ cyclotomicParity datum scalars polys (polys_parity datum) 2 p) :=
  qSourceSpace_tmul_mem datum scalars true polys (polys_parity datum) 2
    (x := InductionAlong.unitGen (appendAlgebra datum scalars true 3 :
      Hn datum scalars 3 →ₙ+* Hn datum scalars 4))
    (appendAlgebra_parity datum scalars true 3 (SetLike.one_mem_graded _)) hb

example (p : ZMod 2) (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1)
    (hb : b ∈ cyclotomicParity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1 p) :=
  qSourceSpace_tmul_mem mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
    (x := InductionAlong.unitGen (appendAlgebra mixedDatum mixedScalars true 2 :
      Hn mixedDatum mixedScalars 2 →ₙ+* Hn mixedDatum mixedScalars 3))
    (appendAlgebra_parity mixedDatum mixedScalars true 2 (SetLike.one_mem_graded _)) hb

example (p : ZMod 2) (b : CyclotomicAlgebra datum scalars polys 2)
    (hb : b ∈ cyclotomicParity datum scalars polys (polys_parity datum) 2 p) :=
  qTargetSpace_tmul_mem datum scalars true ({false, true, false} : Multiset Bool)
    polys (polys_parity datum) 2
    (x := InductionAlong.unitGen (prependAlgebra datum scalars true 3 :
      Hn datum scalars 3 →ₙ+* Hn datum scalars 4))
    (prependAlgebra_parity datum scalars true 3 (SetLike.one_mem_graded _))
    (qCoefficientInsert_mem datum scalars true ({false, true, false} : Multiset Bool)
      polys (polys_parity datum) 2 p b hb)

example (p : ZMod 2) (b : CyclotomicAlgebra mixedDatum mixedScalars polys 1)
    (hb : b ∈ cyclotomicParity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1 p) :=
  qTargetSpace_tmul_mem mixedDatum mixedScalars true ({false, true} : Multiset Bool)
    polys (polys_parity mixedDatum) 1
    (x := InductionAlong.unitGen (prependAlgebra mixedDatum mixedScalars true 2 :
      Hn mixedDatum mixedScalars 2 →ₙ+* Hn mixedDatum mixedScalars 3))
    (prependAlgebra_parity mixedDatum mixedScalars true 2 (SetLike.one_mem_graded _))
    (qCoefficientInsert_mem mixedDatum mixedScalars true ({false, true} : Multiset Bool)
      polys (polys_parity mixedDatum) 1 p b hb)

/-- Specialize both actual action-degree theorems. Avoid unfolding the enormous
concrete quotient carrier again while elaborating an explicit `hz` binder. -/
example := @qSourceSpace_smul_mem Bool ℚ (Bool → ℤ) inferInstance datum inferInstance
  scalars inferInstance true polys (polys_parity datum) 2
example := @qTargetSpace_smul_mem Bool ℚ (Bool → ℤ) inferInstance mixedDatum inferInstance
  mixedScalars inferInstance true ({false, true} : Multiset Bool) polys (polys_parity mixedDatum) 1

end IntertwinerGradingConsumer
