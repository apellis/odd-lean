import OddMath.QuiverHecke.CyclotomicAction.ELVEvenLongCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open scoped TensorProduct
namespace EvenLongCoordinatesConsumer
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

/-- Even moving colour, reversed old words, and unrestricted full old classes. -/
example (z : Target mixedDatum mixedScalars (fun _ => 4) false
    [false, true] ([true, false] ++ [false])) :
    offDiagonalLongExtraction mixedDatum mixedScalars (fun _ => 4) 1 false
      [false, true] [true, false]
      (movingPowerTarget mixedDatum mixedScalars (fun _ => 4) false
        [false, true] ([true, false] ++ [false]) 1 (by decide) z) =
    evenLongShift mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false]
      (offDiagonalLongExtraction mixedDatum mixedScalars (fun _ => 4) 1 false
        [false, true] [true, false] z) :=
  offDiagonalLongExtraction_evenMoving mixedDatum mixedScalars (fun _ => 4)
    1 false rfl _ _ z

example (f : ℕ →₀ Old mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false]) :
    movingPowerTarget mixedDatum mixedScalars (fun _ => 4) false
      [false, true] ([true, false] ++ [false]) 1 (by decide)
      (offDiagonalLongSection mixedDatum mixedScalars (fun _ => 4) 1 false
        [false, true] [true, false] f) =
    offDiagonalLongSection mixedDatum mixedScalars (fun _ => 4) 1 false
      [false, true] [true, false]
      (evenLongShift mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false] f) :=
  evenMoving_offDiagonalLongSection mixedDatum mixedScalars (fun _ => 4)
    1 false rfl _ _ f

/-- The odd exterior coefficient is retained although the moving colour is even. -/
private def exteriorOld : Old mixedDatum mixedScalars (fun _ => 4) [true] [true] :=
  (ideal mixedDatum mixedScalars (fun _ => 4) [true] [true]).mkQ
    (boundaryDelta mixedDatum mixedScalars (fun _ => 4) ⟨true, rfl⟩ [true])

example :
    movingPowerTarget mixedDatum mixedScalars (fun _ => 4) false [true] [true, false] 1 (by decide)
      (offDiagonalLongSection mixedDatum mixedScalars (fun _ => 4) 1 false [true] [true]
        (Finsupp.single 0 exteriorOld)) =
    offDiagonalLongSection mixedDatum mixedScalars (fun _ => 4) 1 false [true] [true]
      (Finsupp.single 1 exteriorOld) := by
  rw [evenMoving_offDiagonalLongSection mixedDatum mixedScalars (fun _ => 4) 1 false rfl,
    evenLongShift_single]
end EvenLongCoordinatesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVEvenLongCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    count := count + 1
  if count == 0 then throwError "Empty declaration inventory"
  logInfo m!"Audited {count} declarations; all axioms allowed."
