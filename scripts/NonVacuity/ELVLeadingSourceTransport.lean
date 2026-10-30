import OddMath.QuiverHecke.CyclotomicAction.ELVLeadingSourceTransport
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (i : I) (v : List I) (c : MoveChoices v) :
    projection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff (i :: v) (v ++ [i])
        (endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c) ≫
          OutputOldComposite.bareU D Sc i v) -
        ((bareUFull D Sc cutoff i v ≫
          appendInsert D Sc cutoff i v v (leadingSourceOldArrow D Sc cutoff i v c)) ≫
          appendMovingPower D Sc cutoff i v
            (sourceMovingDegree (leadingSourceDots D i 0 0 v c)))) ∈
      chronologicalShortSpan D Sc cutoff i v v :=
  leading_source_output_transport D Sc cutoff i v c

example (p : ZMod 2) (i : I) (v : List I)
    (c : MoveChoices v) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i])
          (endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c) ≫
            OutputOldComposite.bareU D Sc i v))) =
      Finsupp.single (sourceMovingDegree (leadingSourceDots D i 0 0 v c))
        ((ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c)) :=
  leading_source_output_extraction D Sc cutoff p i v c

example (i : I) (v : List I) (c : MoveChoices v) (q : ZMod 2) :
    twist k q (leadingSourceOldArrow D Sc cutoff i v c) =
      leadingSourceOldArrow D Sc cutoff i v c :=
  leadingSourceOldArrow_twist D Sc cutoff i v c q

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVLeadingSourceTransport
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
