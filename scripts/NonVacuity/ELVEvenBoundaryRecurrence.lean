import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryRecurrence
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open scoped TensorProduct
namespace EvenBoundaryRecurrenceConsumer
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

example (f : ℕ →₀ Old mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false]) :
    offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] [true, false]
      (evenLongShift mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false] f) =
    evenLongShift mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false]
      (offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] [true, false] f) +
    Finsupp.single 0
      (appendC0InputDefect mixedDatum mixedScalars (fun _ => 4) false [false, true] [true, false]
        (pMap mixedDatum mixedScalars (fun _ => 4) false [false, true] [true, false, false]
          (offDiagonalLongSection mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] [true, false] f)) 0) :=
  offDiagonalPolynomialBoundary_even_shift mixedDatum mixedScalars (fun _ => 4)
    1 false rfl [false, true] [true, false] f

example (n m : ℕ) (f : ℕ →₀ Old mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false]) :
    offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] [true, false]
      ((evenLongShift mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false])^[n] f) (n + m) =
    offDiagonalPolynomialBoundary mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] [true, false] f m :=
  offDiagonalPolynomialBoundary_even_iterate_high mixedDatum mixedScalars (fun _ => 4)
    1 false rfl [false, true] [true, false] n m f
end EvenBoundaryRecurrenceConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryRecurrence
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
