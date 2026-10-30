import OddMath.QuiverHecke.CyclotomicAction.ELVOutputCompatibleLifts
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (p : ZMod 2) (i : I) (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) :
    outputLongExtraction D Sc cutoff p i v (outputLongSection D Sc cutoff p i v f) = f :=
  outputLongExtraction_section D Sc cutoff p i v f
example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    boundaryRho D Sc cutoff j v (v ++ [j.1]) (outputLongSection D Sc cutoff p j.1 v f) =
      outputLongSection D Sc cutoff p j.1 v (outputCoefficientRho D Sc cutoff p j v f) :=
  boundaryRho_outputLongSection D Sc cutoff p j v f
example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (d : ℕ)
    (b : Old D Sc cutoff [] []) :
    outputLongExtraction D Sc cutoff p j.1 [] (outputCorrectedLift D Sc cutoff p j [] d b) =
      (outputCoefficientRho D Sc cutoff p j [])^[d] (Finsupp.single 0 b) :=
  outputLongExtraction_correctedLift D Sc cutoff p j [] d b
example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (m : ℕ) (b : Old D Sc cutoff v v) :
    outputCorrectedCoordinateEquiv D Sc cutoff p j v (Finsupp.single m b) =
      outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v m b) :=
  outputCorrectedCoordinateEquiv_single D Sc cutoff p j v m b
example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    (outputCorrectedCoordinateEquiv D Sc cutoff p j v).symm
      (outputCorrectedCoordinateEquiv D Sc cutoff p j v f) = f :=
  (outputCorrectedCoordinateEquiv D Sc cutoff p j v).symm_apply_apply f
open Lean in
run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOutputCompatibleLifts
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
