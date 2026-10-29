import OddMath.QuiverHecke.CyclotomicAction.ELVQPRegularity

noncomputable section
namespace ELVQPRegularityConsumer
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- All words and full-coefficient continuations, with the actual signed product. -/
theorem allWords (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫
        relation D Sc cutoff i v ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 :=
  projection_qp_relation_regular D Sc cutoff i v w h hh

/-- The prescribed crossing composite is the concrete input for P injectivity. -/
theorem crossingComposite (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (moveHom D Sc i [] v ≫ lastToFirstHom D Sc i v) ≫
        relation D Sc cutoff i v ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 :=
  projection_move_relation_regular D Sc cutoff i v w h hh

#print axioms projection_relation_regular
#print axioms projection_qp_relation_regular
#print axioms projection_move_relation_regular
end ELVQPRegularityConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVSignedMovingPower,
      `OddMath.QuiverHecke.CyclotomicAction.ELVRelationRegularity,
      `OddMath.QuiverHecke.CyclotomicAction.ELVQPRegularity] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory: {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
