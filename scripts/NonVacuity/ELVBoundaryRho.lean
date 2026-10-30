import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRho
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

-- Arbitrary mixed old word, full coefficients, all corrected iterates.
example (j : {j : I // D.parity j = 1}) (v w : List I) (d : ℕ)
    (z : Target D Sc cutoff j.1 v w) :
    pMap D Sc cutoff j.1 v w ((boundaryRho D Sc cutoff j v w)^[d] z) =
      appendMovingPowerTarget D Sc cutoff j.1 v w d (pMap D Sc cutoff j.1 v w z) :=
  pMap_boundaryRho_iterate D Sc cutoff j v w d z

example (j : {j : I // D.parity j = 1}) (v w : List I) (q : ℕ)
    (z : Target D Sc cutoff j.1 v w) :
    (boundaryRho D Sc cutoff j v w)^[2 * q] z =
      signedMovingPowerTarget D Sc cutoff j.1 v w (2 * q) z :=
  boundaryRho_iterate_even D Sc cutoff j v w q z

-- Empty old word and zero cutoffs are included, not exceptional hypotheses.
example (j : {j : I // D.parity j = 1}) (w : List I)
    (z : Target D Sc (fun _ => 0) j.1 [] w) :
    boundaryRho D Sc (fun _ => 0) j [] w (boundaryRho D Sc (fun _ => 0) j [] w z) =
      signedMovingPowerTarget D Sc (fun _ => 0) j.1 [] w 2 z :=
  boundaryRho_square D Sc (fun _ => 0) j [] w z

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRho
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
