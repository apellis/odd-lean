import OddMath.QuiverHecke.CyclotomicAction.ELVEvenRowDivision
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace EvenRowDivisionConsumer
open CyclotomicAction.AsymmetricParameters
private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }

private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num


abbrev Coeff := Old mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false]
abbrev High := evenBoundaryRowHigh mixedDatum mixedScalars (fun _ => 4) false [false, true] [true, false]
abbrev Window := evenBoundaryRowWindow mixedDatum mixedScalars (fun _ => 4) false [false, true] [true, false]

def division : (High × Window) ≃ₗ[ℚ] (ℕ →₀ Coeff) :=
  evenBoundaryRowDivisionEquiv mixedDatum mixedScalars (fun _ => 4) 1 false rfl
    [false, true] [true, false]

example (f : ℕ →₀ Coeff) : division (division.symm f) = f := division.apply_symm_apply f
example (x : High × Window) : division.symm (division x) = x := division.symm_apply_apply x
example (x : High × Window) : division x =
    offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 4) 1 false
      [false, true] [true, false] x.1 + x.2 := rfl

example (f : ℕ →₀ Coeff) :
    offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 4) 1 false
        [false, true] [true, false] f = 0 ↔
      ∀ d ∈ f.support, d + endpointQPDegree mixedDatum (fun _ => 4) false [false, true] <
        outputSDegree mixedDatum false [false, true] :=
  offDiagonalPolynomialBoundary_even_eq_zero_iff mixedDatum mixedScalars (fun _ => 4)
    1 false rfl [false, true] [true, false] f

example : Function.Injective
    (offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 4) 1 false [] []) :=
  offDiagonalPolynomialBoundary_even_injective mixedDatum mixedScalars (fun _ => 4)
    1 false rfl [] [] (by norm_num [endpointQPDegree, outputSDegree])

example : Function.Surjective
    (offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 1) 1 false
      [false, false] [false, false]) :=
  offDiagonalPolynomialBoundary_even_surjective mixedDatum mixedScalars (fun _ => 1)
    1 false rfl [false, false] [false, false]
      (by norm_num [endpointQPDegree, outputSDegree, appendQPDegree, mixedDatum, List.range_succ, List.getD])

end EvenRowDivisionConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.Algebra.DegreeShiftRowDivision,
      `OddMath.QuiverHecke.CyclotomicAction.ELVEvenRowDivision] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited ALL {names.size} declarations of {owner}"
