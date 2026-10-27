import OddMath.QuiverHecke.CyclotomicAction.IntertwinerError
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerError then
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
namespace IntertwinerErrorConsumer

def powers (m : ℕ) (_ : Bool) : _root_.Polynomial ℚ := _root_.Polynomial.X ^ m

private theorem powers_parity (m : ℕ) : CyclotomicPolynomialParity datum (powers m) := by
  intro i j hj
  by_cases h : m = j
  · subst j; simp [powers]
  · simp [powers, Polynomial.coeff_X_pow, Ne.symm h] at hj

/-- All exponents, including the constant polynomial, in the prescribed shifted tensor. -/
example (m : ℕ) (r : Hn datum scalars 2)
    (b : (qCoefficient datum scalars true {true} (powers m) (powers_parity m) 0).toSVec) :
    InductionAlong.Ind.tmul
      ((r * OddMath.FiniteHomMatrix.single (⟨[true, true], rfl⟩ : Word Bool 2)
        ⟨[true, true], rfl⟩ (repeatedOddError datum scalars true (powers m))) •
        InductionAlong.unitGen (prependAlgebra datum scalars true 1 :
          Hn datum scalars 1 →ₙ+* Hn datum scalars 2)) b = 0 :=
  repeatedOddError_tmul_zero datum scalars true rfl {true} (powers m) (powers_parity m) r b

private theorem zero_parity : CyclotomicPolynomialParity datum (fun _ => 0 : Bool → _root_.Polynomial ℚ) := by
  intro i m hm
  simp at hm

example (r : Hn datum scalars 2)
    (b : (qCoefficient datum scalars true {true} (fun _ => 0) zero_parity 0).toSVec) :=
  repeatedOddError_tmul_zero datum scalars true rfl {true} (fun _ => 0) zero_parity r b

/-- The scalar polynomial need not be a monomial, and its constant term is retained. -/
def evenPolynomial (_ : Bool) : _root_.Polynomial ℚ :=
  _root_.Polynomial.X ^ 4 + _root_.Polynomial.X ^ 2 + _root_.Polynomial.C 3

private theorem evenPolynomial_parity : CyclotomicPolynomialParity datum evenPolynomial := by
  intro i m hm
  have hd : (evenPolynomial i).natDegree = 4 := by
    norm_num [evenPolynomial, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  rw [hd]
  change m • (1 : ZMod 2) = (4 : ℕ) • (1 : ZMod 2)
  by_cases h4 : m = 4
  · subst m; rfl
  by_cases h2 : m = 2
  · subst m; decide
  by_cases h0 : m = 0
  · subst m; decide
  simp [evenPolynomial, Polynomial.coeff_X_pow, Polynomial.coeff_C, h4, h2, h0] at hm

example (r : Hn datum scalars 2)
    (b : CyclotomicAlgebra datum scalars evenPolynomial 0) :=
  repeatedOddError_tmul_zero datum scalars true rfl {true} evenPolynomial evenPolynomial_parity r
    (qCoefficientInsert datum scalars true {true} evenPolynomial evenPolynomial_parity 0 b)

#print axioms OddMath.OddNilHecke.Intertwiner.error_pow
#print axioms OddMath.OddNilHecke.Intertwiner.error_polynomial
#print axioms OddMath.QuiverHecke.repeatedOddError_factor
#print axioms OddMath.QuiverHecke.repeatedOddError_tmul_zero
end IntertwinerErrorConsumer
