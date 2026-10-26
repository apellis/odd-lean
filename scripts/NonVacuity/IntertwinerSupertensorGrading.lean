import OddMath.QuiverHecke.CyclotomicAction.IntertwinerSupertensorGrading
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerSupertensorGrading then
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
namespace IntertwinerSupertensorGradingConsumer

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

example (c : CyclotomicAlgebra datum scalars polys 2)
    (hc : c ∈ cyclotomicParity datum scalars polys (polys_parity datum) 2 0) :
    SVec.ofHom (sourceRightSupertensor datum scalars true polys (polys_parity datum) 2
      ((Polynomial.X ^ 3) ⊗ₜ[ℚ] c)).unop ∈
      SVec.parityHom (qSourceSpace datum scalars true polys (polys_parity datum) 2)
        (qSourceSpace datum scalars true polys (polys_parity datum) 2) 1 := by
  rw [← (show (3 : ZMod 2) * datum.parity true + 0 = 1 by decide)]
  exact sourceRightSupertensor_parity datum scalars true polys (polys_parity datum) 2
    (3 * datum.parity true + 0) _
    (polynomialSupertensor_tmul_mem datum scalars true polys (polys_parity datum) 2 3 0 c hc)

example (c : CyclotomicAlgebra mixedDatum mixedScalars polys 1)
    (hc : c ∈ cyclotomicParity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1 1) :
    SVec.ofHom (targetRightSupertensor mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
      ({false, true} : Multiset Bool) ((Polynomial.X ^ 3) ⊗ₜ[ℚ] c)).unop ∈
      SVec.parityHom (qTargetSpace mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1)
        (qTargetSpace mixedDatum mixedScalars true {false, true} polys (polys_parity mixedDatum) 1) 0 := by
  rw [← (show (3 : ZMod 2) * mixedDatum.parity true + 1 = 0 by decide)]
  exact targetRightSupertensor_parity mixedDatum mixedScalars true polys
    (polys_parity mixedDatum) 1 {false, true} (3 * mixedDatum.parity true + 1) _
    (polynomialSupertensor_tmul_mem mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 3 1 c hc)

/-- Arbitrary finite homogeneous tensors, with a nonzero target shift, in both degrees. -/
example (d : ZMod 2) (s : Finset ℕ) (r : ℕ → ℚ)
    (f : ℕ → Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra datum scalars polys 2)
    (hf : ∀ j ∈ s, f j ∈ polynomialSupertensorPart datum scalars true polys (polys_parity datum) 2 d) :=
  rightSupertensor_Q_gradedSquare datum scalars true polys (polys_parity datum) 2
    {false, true, false} d (∑ j ∈ s, r j • f j)
    ((polynomialSupertensorPart datum scalars true polys (polys_parity datum) 2 d).sum_mem
      (fun j hj => (polynomialSupertensorPart datum scalars true polys (polys_parity datum) 2 d).smul_mem (r j) (hf j hj)))

example (d : ZMod 2) (s : Finset ℕ) (r : ℕ → ℚ)
    (f : ℕ → Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra mixedDatum mixedScalars polys 1)
    (hf : ∀ j ∈ s, f j ∈ polynomialSupertensorPart mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 d) :=
  rightSupertensor_Q_gradedSquare mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
    {false, true} d (∑ j ∈ s, r j • f j)
    ((polynomialSupertensorPart mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 d).sum_mem
      (fun j hj => (polynomialSupertensorPart mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 d).smul_mem (r j) (hf j hj)))

#print axioms rightSupertensor_Q_gradedSquare
end IntertwinerSupertensorGradingConsumer
