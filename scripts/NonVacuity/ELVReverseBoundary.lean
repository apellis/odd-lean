import OddMath.QuiverHecke.CyclotomicAction.ELVReverseBoundary
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    pMap D Sc cutoff i v w
      (projection D Sc cutoff i v w (move D Sc cutoff i v ≫ h)) =
    sign k ((cutoff i • D.parity i) * (D.parity i * wordSumParity D v)) •
      appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ h) :=
  pMap_move_projection D Sc cutoff i v w h

example (j : {i : I // D.parity i = 1})
    (v w : List I) (d : ℕ) (h : hom D Sc cutoff (v ++ [j.1]) w) :
    pMap D Sc cutoff j.1 v w
      ((boundaryRho D Sc cutoff j v w)^[d]
        (projection D Sc cutoff j.1 v w (move D Sc cutoff j.1 v ≫ h))) =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      appendProjection D Sc cutoff j.1 v w
        (appendMovingPower D Sc cutoff j.1 v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc j.1 v) ≫
          endpointELV D Sc cutoff j.1 v ≫ h) :=
  pMap_boundaryRho_move_iterate D Sc cutoff j v w d h

example (i : I) (hi : D.parity i = 0)
    (v w : List I) (d : ℕ) (h : hom D Sc cutoff (v ++ [i]) w) :
    pMap D Sc cutoff i v w
      ((movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]))^[d]
        (projection D Sc cutoff i v w (move D Sc cutoff i v ≫ h))) =
      appendProjection D Sc cutoff i v w
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ h) :=
  pMap_evenDot_move_iterate D Sc cutoff i hi v w d h

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[
    `OddMath.QuiverHecke.CyclotomicAction.AppendQPTransport,
    `OddMath.QuiverHecke.CyclotomicAction.ELVEndpointPolynomial,
    `OddMath.QuiverHecke.CyclotomicAction.ELVReverseBoundary]
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
