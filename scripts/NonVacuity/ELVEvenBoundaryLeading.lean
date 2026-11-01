import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryLeading
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open scoped TensorProduct
namespace EvenBoundaryLeadingConsumer
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

/-- The top coefficient is tested without supplying any boundary-leading law. -/
example :
    evenBoundaryPhi mixedDatum mixedScalars (fun _ => 4) 1 false [false, true]
      (outputSDegree mixedDatum false [false, true])
      (outputSDegree mixedDatum false [false, true] +
        endpointQPDegree mixedDatum (fun _ => 4) false [false, true] -
        outputSDegree mixedDatum false [false, true]) =
    (appendQPProductUnit mixedDatum mixedScalars false [false, true] : ℚ) •
      (ideal mixedDatum mixedScalars (fun _ => 4) [false, true] [false, true]).mkQ (𝟙 _) :=
  evenBoundaryPhi_top mixedDatum mixedScalars (fun _ => 4) 1 false rfl [false, true]
    (outputSDegree mixedDatum false [false, true]) (by omega)

example (d : ℕ) :
    evenBoundaryPhi mixedDatum mixedScalars (fun _ => 4) 1 false [false, true] d
      (d + endpointQPDegree mixedDatum (fun _ => 4) false [false, true] + 1) = 0 :=
  evenBoundaryPhi_above mixedDatum mixedScalars (fun _ => 4) 1 false rfl [false, true] d _ (by omega)

/-- The zero-corner/negative-height case is part of the same actual map. -/
example : evenBoundaryPhi mixedDatum mixedScalars (fun _ => 0) 1 false [false] 0 = 0 := by
  apply evenBoundaryPhi_eq_zero_of_negative mixedDatum mixedScalars (fun _ => 0) 1 false rfl [false] 0
  norm_num [endpointQPDegree, appendQPDegree, outputSDegree, mixedDatum, datum]
end EvenBoundaryLeadingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryLeading
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
