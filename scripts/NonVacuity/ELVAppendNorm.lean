import OddMath.QuiverHecke.CyclotomicAction.ELVAppendNormRegularity
noncomputable section
open CategoryTheory OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Arbitrary words, cutoffs and full exterior coefficients. -/
example (i : I) (v w : List I) (z y : AppendTarget D Sc cutoff i v w)
    (h : qMap D Sc cutoff i v w z = qMap D Sc cutoff i v w y) : z = y :=
  qMap_injective D Sc cutoff i v w h

/-- A mixed word permits repeated even and repeated odd colours. -/
example (i j : I) (w : List I) (h : hom D Sc cutoff ([j, i, j] ++ [i]) w)
    (hh : appendProjection D Sc cutoff i [j, i, j] w
      (affineUnit D Sc cutoff _ _ (endpointNorm D Sc i [] [j, i, j]) ≫ h) = 0) :
    appendProjection D Sc cutoff i [j, i, j] w h = 0 :=
  appendProjection_endpointNorm_regular D Sc cutoff i [j, i, j] w h hh

/-- Empty old content and zero cutoff require no nonzero quotient corner. -/
example (i : I) (w : List I) :
    Function.Injective (qMap D Sc (fun _ => 0) i [] w) :=
  qMap_injective D Sc (fun _ => 0) i [] w

#print axioms appendProjection_endpointNorm_regular
#print axioms qMap_injective

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[
    `OddMath.QuiverHecke.CyclotomicAction.ELVAppendMovingSupport,
    `OddMath.QuiverHecke.CyclotomicAction.ELVAppendNormRegularity]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory: {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
