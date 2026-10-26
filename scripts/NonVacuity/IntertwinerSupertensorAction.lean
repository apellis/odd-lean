import OddMath.QuiverHecke.CyclotomicAction.IntertwinerSupertensorAction
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerSupertensorAction then
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
namespace IntertwinerSupertensorActionConsumer

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


example := polynomialTensorSkewEquiv_tmul datum scalars true polys (polys_parity datum) 2 2 (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2))
example := polynomialTensorSkewEquiv_symm_monomial datum scalars true polys (polys_parity datum) 2 1 (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2))
example := polynomialSupertensor_one datum scalars true polys (polys_parity datum) 2
example := sourceRightSupertensor_tmul datum scalars true polys (polys_parity datum) 2 1 (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2))
example := targetRightSupertensor_tmul datum scalars true polys (polys_parity datum) 2 ({false, true, false} : Multiset Bool) 2 (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2))
example (f : Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra datum scalars polys 2) :=
  rightSupertensor_Q datum scalars true polys (polys_parity datum) 2 ({false, true, false} : Multiset Bool) f

/-- The odd crossing sign is negative at exponent one and positive at exponent two. -/
example : letI : Mul (Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra datum scalars polys 2) :=
    (polynomialSupertensorRing datum scalars true polys (polys_parity datum) 2).toMul
    let b := cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)
    (((Polynomial.X : Polynomial ℚ) ^ 1) ⊗ₜ[ℚ] b) *
        (((Polynomial.X : Polynomial ℚ) ^ 1) ⊗ₜ[ℚ] (1 : CyclotomicAlgebra datum scalars polys 2)) =
      (-1 : ℚ) • (((Polynomial.X : Polynomial ℚ) ^ (1 + 1)) ⊗ₜ[ℚ] b) := by
  simpa [Supercategory.sign_one, Supercategory.sign_zero, show (2 : ZMod 2) = 0 by decide, datum] using
    polynomialSupertensor_mul_tmul datum scalars true polys (polys_parity datum) 2 1 1 1 (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)) 1 (cyclotomicMk_parity datum scalars polys (polys_parity datum) 2 (affineLastDot_parity datum scalars true 2))

/-- The odd crossing sign is negative at exponent one and positive at exponent two. -/
example : letI : Mul (Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra datum scalars polys 2) :=
    (polynomialSupertensorRing datum scalars true polys (polys_parity datum) 2).toMul
    let b := cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)
    (((Polynomial.X : Polynomial ℚ) ^ 1) ⊗ₜ[ℚ] b) *
        (((Polynomial.X : Polynomial ℚ) ^ 2) ⊗ₜ[ℚ] (1 : CyclotomicAlgebra datum scalars polys 2)) =
      (((Polynomial.X : Polynomial ℚ) ^ (1 + 2)) ⊗ₜ[ℚ] b) := by
  simpa [Supercategory.sign_one, Supercategory.sign_zero, show (2 : ZMod 2) = 0 by decide, datum] using
    polynomialSupertensor_mul_tmul datum scalars true polys (polys_parity datum) 2 1 2 1 (cyclotomicMk datum scalars polys 2 (affineLastDot datum scalars true 2)) 1 (cyclotomicMk_parity datum scalars polys (polys_parity datum) 2 (affineLastDot_parity datum scalars true 2))

example := polynomialTensorSkewEquiv_tmul mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 2 (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1))
example := polynomialTensorSkewEquiv_symm_monomial mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 1 (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1))
example := polynomialSupertensor_one mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
example := sourceRightSupertensor_tmul mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 1 (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1))
example := targetRightSupertensor_tmul mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 ({false, true} : Multiset Bool) 2 (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1))
example (f : Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
  rightSupertensor_Q mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 ({false, true} : Multiset Bool) f

/-- The odd crossing sign is negative at exponent one and positive at exponent two. -/
example : letI : Mul (Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
    (polynomialSupertensorRing mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1).toMul
    let b := cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)
    (((Polynomial.X : Polynomial ℚ) ^ 1) ⊗ₜ[ℚ] b) *
        (((Polynomial.X : Polynomial ℚ) ^ 1) ⊗ₜ[ℚ] (1 : CyclotomicAlgebra mixedDatum mixedScalars polys 1)) =
      (-1 : ℚ) • (((Polynomial.X : Polynomial ℚ) ^ (1 + 1)) ⊗ₜ[ℚ] b) := by
  simpa [Supercategory.sign_one, Supercategory.sign_zero, show (2 : ZMod 2) = 0 by decide, mixedDatum] using
    polynomialSupertensor_mul_tmul mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 1 1 1 (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)) 1 (cyclotomicMk_parity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1 (affineLastDot_parity mixedDatum mixedScalars true 1))

/-- The odd crossing sign is negative at exponent one and positive at exponent two. -/
example : letI : Mul (Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
    (polynomialSupertensorRing mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1).toMul
    let b := cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)
    (((Polynomial.X : Polynomial ℚ) ^ 1) ⊗ₜ[ℚ] b) *
        (((Polynomial.X : Polynomial ℚ) ^ 2) ⊗ₜ[ℚ] (1 : CyclotomicAlgebra mixedDatum mixedScalars polys 1)) =
      (((Polynomial.X : Polynomial ℚ) ^ (1 + 2)) ⊗ₜ[ℚ] b) := by
  simpa [Supercategory.sign_one, Supercategory.sign_zero, show (2 : ZMod 2) = 0 by decide, mixedDatum] using
    polynomialSupertensor_mul_tmul mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 1 2 1 (cyclotomicMk mixedDatum mixedScalars polys 1 (affineLastDot mixedDatum mixedScalars true 1)) 1 (cyclotomicMk_parity mixedDatum mixedScalars polys (polys_parity mixedDatum) 1 (affineLastDot_parity mixedDatum mixedScalars true 1))

end IntertwinerSupertensorActionConsumer
