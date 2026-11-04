import OddMath.QuiverHecke.CyclotomicAction.ELVProbeUpperLoopDot
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTensorVacuum
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
namespace NonVacuity.ELVProbeUpperLoopDot
private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
example (i : Bool) := oldAppendUpperLoop_dot D Sc m [] i (List.Perm.refl [i])
  (probeOldVacuumRegular D Sc m)
-- A nontrivial stored representative checks that the chart need not be
-- the reflexive single-colour append representative.
example (N : Superfunctor ℚ (OldContentCategory D Sc (probeCutoff D m) [false]) (SVec ℚ)) :=
  oldAppendUpperLoop_dot D Sc m [false] true (List.Perm.swap false true []) N
example : probeOldVacuumVector D Sc m ≠ 0 := probeOldVacuumVector_ne_zero D Sc m
end NonVacuity.ELVProbeUpperLoopDot
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeUpperLoopDot
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations"
