import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryFirstOrder
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputLiftBoundary D Sc cutoff p j v (outputCoefficientRho D Sc cutoff p j v f) =
      appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
        (outputLiftBoundary D Sc cutoff p j v f) :=
  outputLiftBoundary_rho D Sc cutoff p j v f
example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    pMap D Sc cutoff j.1 v (v ++ [j.1]) z -
      outputLiftBoundary D Sc cutoff p j v (outputLongExtraction D Sc cutoff p j.1 v z) ∈
        chronologicalCrossingSpan D Sc cutoff j.1 v v :=
  pMap_sub_outputLiftBoundary_mem D Sc cutoff p j v z
example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (d : ℕ) (b : Old D Sc cutoff [] []) :
    pMap D Sc cutoff j.1 [] [j.1] (outputCorrectedLift D Sc cutoff p j [] d b) =
      appendMovingPowerTarget D Sc cutoff j.1 [] [j.1] d
        (pMap D Sc cutoff j.1 [] [j.1] (outputLongLift D Sc cutoff p j.1 [] 0 b)) :=
  pMap_outputCorrectedLift D Sc cutoff p j [] d b
open Lean in
run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryFirstOrder
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
  if count == 0 then throwError "Empty declaration inventory"
  logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
