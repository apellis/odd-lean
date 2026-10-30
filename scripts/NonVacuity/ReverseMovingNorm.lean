import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerNorm
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVMovingNormRegularity

noncomputable section
namespace ReverseMovingNormConsumer
open CategoryTheory OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- A mixed word with a repeated moving colour uses the literal reverse-chain producer. -/
example (i j : I) :
    reverseMoveHom D Sc i [] [j, i, j] ≫ moveHom D Sc i [] [j, i, j] =
      endpointNorm D Sc i [] [j, i, j] :=
  reverseMoveHom_comp_moveHom_eq_endpointNorm D Sc i [] [j, i, j]

/-- Odd moving colour, even spectator: the reverse moving-dot sign is negative. -/
example (i j : I) (hi : D.parity i = 1) (hj : D.parity j = 0) :
    dotE D Sc [j, i, j, i] 3 ≫ reverseMoveHom D Sc i [] [j, i, j] =
      -(reverseMoveHom D Sc i [] [j, i, j] ≫ dotE D Sc [i, j, i, j] 0) := by
  simpa [wordSumParity, hi, hj, SKM.zsign] using
    dot_comp_reverseMoveHom D Sc i [] [j, i, j]

/-- The full coefficient quotient has no added domain or flatness hypothesis. -/
example (i j : I) (w : List I) (h : hom D Sc cutoff (i :: [j, i, j]) w)
    (hh : projection D Sc cutoff i [j, i, j] w
      (affineUnit D Sc cutoff _ _ (movingNormProduct D Sc i [j, i, j]) ≫ h) = 0) :
    projection D Sc cutoff i [j, i, j] w h = 0 :=
  projection_movingNormProduct_regular D Sc cutoff i [j, i, j] w h hh

#print axioms reverseMoveHom_comp_moveHom_eq_endpointNorm
#print axioms dot_mem_comp_reverseMoveHom
#print axioms projection_movingNormProduct_regular
end ReverseMovingNormConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[
    `OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerChain,
    `OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerNorm,
    `OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerNaturality,
    `OddMath.QuiverHecke.CyclotomicAction.ELVMovingNormRegularity]
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
