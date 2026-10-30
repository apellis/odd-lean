import OddMath.QuiverHecke.CyclotomicAction.ELVQPDivisionEquiv
noncomputable section
open CategoryTheory OddMath OddMath.QuiverHecke ELVOld
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v w : List I) :
    AppendTarget D Sc cutoff i v w ≃ₗ[k]
      (AppendTarget D Sc cutoff i v w × endpointQPLow D Sc cutoff i v w) :=
  endpointQPDivisionEquiv D Sc cutoff i v w

example (i : I) (v w : List I) (g : hom D Sc cutoff (v ++ [i]) w) :
    endpointQPDivisionEquiv D Sc cutoff i v w
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ g)) =
      (appendProjection D Sc cutoff i v w g, 0) :=
  endpointQPDivisionEquiv_numerator D Sc cutoff i v w g

#print axioms endpointQPAction_low
#print axioms endpointQP_division_unique
#print axioms endpointQP_division_existsUnique
#print axioms endpointQPDivisionEquiv
#print axioms endpointQPDivisionEquiv_numerator
#print axioms endpointQP_remainder_zero_iff

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVQPDivisionEquiv] do
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
