import OddMath.QuiverHecke.CyclotomicAction.ELVOutputOldAction
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (p : ZMod 2) (i : I) (v : List I) (m : ℕ)
    (c : hom D Sc cutoff v v) (z : Target D Sc cutoff i v (v ++ [i])) :
    outputLongCoordinate D Sc cutoff p i v m (oldSourceTarget D Sc cutoff i v (v ++ [i]) c z) =
      oldPrecomp D Sc cutoff v v (Supercategory.twist k p c)
        (outputLongCoordinate D Sc cutoff p i v m z) :=
  outputLongCoordinate_oldSource D Sc cutoff p i v m c z

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVOutputOldAction] do
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