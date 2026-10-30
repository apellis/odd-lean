import OddMath.QuiverHecke.CyclotomicAction.ELVOutputOldTransport
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (i : I) (v t w : List I) (g : hom D Sc cutoff t w)
    (z : Target D Sc cutoff i v (t ++ [i]))
    (hz : z ∈ chronologicalShortSpan D Sc cutoff i v t) :
    act D Sc cutoff i (appendInsert D Sc cutoff i t w g) z ∈
      chronologicalShortSpan D Sc cutoff i v w :=
  act_appendInsert_chronologicalShortSpan D Sc cutoff i v t w g
    (Submodule.mem_map_of_mem hz)
example (p : ZMod 2) (i : I) (v : List I) (g : hom D Sc cutoff v v)
    (x y : Target D Sc cutoff i v (v ++ [i]))
    (h : outputLongExtraction D Sc cutoff p i v x = outputLongExtraction D Sc cutoff p i v y) :
    outputLongExtraction D Sc cutoff p i v
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) x) =
    outputLongExtraction D Sc cutoff p i v
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) y) :=
  outputLongExtraction_act_appendInsert_congr D Sc cutoff p i v g h

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVOutputOldTransport] do
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
