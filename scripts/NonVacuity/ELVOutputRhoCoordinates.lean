import OddMath.QuiverHecke.CyclotomicAction.ELVOutputRhoCoordinates
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) (m : ℕ)
    (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    outputLongCoordinate D Sc cutoff p j.1 v (1 + m)
      (boundaryRho D Sc cutoff j v (v ++ [j.1]) z) =
      oldTwist D Sc cutoff (D.parity j.1) v v (outputLongCoordinate D Sc cutoff p j.1 v m z) +
      SKM.zsign k (D.parity j.1 * wordSumParity D v) •
        ((2 * (-1 : k) ^ cutoff j.1) •
          oldPrecomp D Sc cutoff v v (twist k p (boundaryDelta D Sc cutoff j v))
            (outputLongCoordinate D Sc cutoff p j.1 v (1 + m) z)) :=
  outputLongCoordinate_boundaryRho_succ D Sc cutoff p j v m z

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVOutputOldAction,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOutputRhoCoordinates] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Missing module {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      logInfo m!"AUDIT {owner} {name}: {axioms}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory for {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."