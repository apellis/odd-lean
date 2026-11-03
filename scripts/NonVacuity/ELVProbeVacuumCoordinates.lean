import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
namespace NonVacuity.ELVProbeVacuumCoordinates
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1

example (a : Hn D Sc 0) :
    heightZeroScalarEquiv D Sc ((heightZeroScalarEquiv D Sc).symm a) = a :=
  (heightZeroScalarEquiv D Sc).apply_symm_apply a

example : probeVacuumScalarEquiv D Sc m 1 = probeOldVacuumVector D Sc m :=
  probeVacuumScalarEquiv_one D Sc m

example : probeVacuumScalarEquiv D Sc m (3 : ℚ) ≠ 0 := by
  intro hz
  have h := (probeVacuumScalarEquiv D Sc m).injective
    (hz.trans (map_zero (probeVacuumScalarEquiv D Sc m)).symm)
  norm_num at h

example (v : (probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m)) :
    v ∈ ((probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m)).part 0 :=
  probeVacuum_even D Sc m v

example (a b : ℚ) :
    heightZeroScalarEquiv D Sc (a * b) =
      heightZeroScalarEquiv D Sc a * heightZeroScalarEquiv D Sc b :=
  map_mul (heightZeroScalarEquiv D Sc) a b

end NonVacuity.ELVProbeVacuumCoordinates

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
