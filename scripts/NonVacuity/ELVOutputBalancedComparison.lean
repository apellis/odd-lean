import OddMath.QuiverHecke.CyclotomicAction.ELVOutputBalancedComparison
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    outputLongExtraction D Sc cutoff p j.1 v (boundaryRho D Sc cutoff j v (v ++ [j.1]) z) =
      outputCoefficientRho D Sc cutoff p j v (outputLongExtraction D Sc cutoff p j.1 v z) :=
  outputLongExtraction_boundaryRho D Sc cutoff p j v z
example (p : ZMod 2) (i : I) (v : List I) (m : ℕ)
    (h : hom D Sc cutoff (i :: v) (v ++ [i])) (b : Old D Sc cutoff v v) :
    outputLongCoordinate D Sc cutoff p i v m
      (balancedForward D Sc cutoff p i v (v ++ [i]) (balancedTmul D Sc cutoff p i h b)) =
    oldComp D Sc cutoff v v v b
      (outputLongCoordinate D Sc cutoff p i v m (projection D Sc cutoff i v (v ++ [i]) h)) :=
  outputLongCoordinate_balanced D Sc cutoff p i v m h b

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVOutputOldAction,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOutputRhoCoordinates,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOutputBalancedComparison] do
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