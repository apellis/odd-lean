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
namespace IntertwinerSupertensorScalarConsumer

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
example := polynomialSupertensorSkewAlgEquiv datum scalars true polys (polys_parity datum) 2
example := qCoefficientScalarTower datum scalars true polys (polys_parity datum) 2 ({false, true, false} : Multiset Bool)
example (r : ℚ) (f : Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra datum scalars polys 2) :
    (polynomialSupertensorAlgebra datum scalars true polys (polys_parity datum) 2).smul r f = r • f := rfl
example (r : ℚ) :
    letI := coefficientParityAction datum scalars true polys (polys_parity datum) 2
    letI := coefficientParityScalarComm datum scalars true polys (polys_parity datum) 2
    letI : Semiring (Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra datum scalars polys 2) :=
      (polynomialSupertensorRing datum scalars true polys (polys_parity datum) 2).toSemiring
    letI := polynomialSupertensorAlgebra datum scalars true polys (polys_parity datum) 2
    polynomialSupertensorSkewAlgEquiv datum scalars true polys (polys_parity datum) 2
        (algebraMap ℚ (Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra datum scalars polys 2) r) =
      algebraMap ℚ (_root_.SkewPolynomial (CyclotomicAlgebra datum scalars polys 2)) r := by
  let := coefficientParityAction datum scalars true polys (polys_parity datum) 2
  let := coefficientParityScalarComm datum scalars true polys (polys_parity datum) 2
  let : Semiring (Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra datum scalars polys 2) :=
    (polynomialSupertensorRing datum scalars true polys (polys_parity datum) 2).toSemiring
  let := polynomialSupertensorAlgebra datum scalars true polys (polys_parity datum) 2
  exact (polynomialSupertensorSkewAlgEquiv datum scalars true polys (polys_parity datum) 2).commutes r

example : mixedDatum.parity true * contentSumParity mixedDatum ({false, true} : Multiset Bool) = 1 := by decide
example := polynomialSupertensorSkewAlgEquiv mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
example := qCoefficientScalarTower mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1 ({false, true} : Multiset Bool)
example (r : ℚ) (f : Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra mixedDatum mixedScalars polys 1) :
    (polynomialSupertensorAlgebra mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1).smul r f = r • f := rfl
example (r : ℚ) :
    letI := coefficientParityAction mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
    letI := coefficientParityScalarComm mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
    letI : Semiring (Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
      (polynomialSupertensorRing mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1).toSemiring
    letI := polynomialSupertensorAlgebra mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
    polynomialSupertensorSkewAlgEquiv mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
        (algebraMap ℚ (Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra mixedDatum mixedScalars polys 1) r) =
      algebraMap ℚ (_root_.SkewPolynomial (CyclotomicAlgebra mixedDatum mixedScalars polys 1)) r := by
  let := coefficientParityAction mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
  let := coefficientParityScalarComm mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
  let : Semiring (Polynomial ℚ ⊗[ℚ] CyclotomicAlgebra mixedDatum mixedScalars polys 1) :=
    (polynomialSupertensorRing mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1).toSemiring
  let := polynomialSupertensorAlgebra mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1
  exact (polynomialSupertensorSkewAlgEquiv mixedDatum mixedScalars true polys (polys_parity mixedDatum) 1).commutes r

end IntertwinerSupertensorScalarConsumer
