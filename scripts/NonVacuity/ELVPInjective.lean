import OddMath.QuiverHecke.CyclotomicAction.ELVPInjective

noncomputable section
namespace ELVPInjectiveConsumer
open CategoryTheory OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Equality after the prescribed W already implies equality in the old-only quotient. -/
example (i : I) (v w : List I) (h g : hom D Sc cutoff (i :: v) w)
    (he : appendProjection D Sc cutoff i v w (appendW D Sc cutoff i v ≫ h) =
      appendProjection D Sc cutoff i v w (appendW D Sc cutoff i v ≫ g)) :
    projection D Sc cutoff i v w h = projection D Sc cutoff i v w g := by
  apply pMap_injective D Sc cutoff i v w
  exact he

/-- Arbitrary quotient classes, with no nonvanishing or freeness premise. -/
example (i : I) (v w : List I) (x y : Target D Sc cutoff i v w)
    (h : pMap D Sc cutoff i v w x = pMap D Sc cutoff i v w y) : x = y :=
  pMap_injective D Sc cutoff i v w h

#print axioms signedQPMap_injective
#print axioms pMap_injective
end ELVPInjectiveConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVPInjective
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
