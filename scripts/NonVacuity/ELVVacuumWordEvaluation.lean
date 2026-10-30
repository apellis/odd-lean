import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumWordEvaluation
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumWordEvaluationConsumer
open VacuumSourceComparison
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- An arbitrary vector in the actual whole extended word module, with its
existing terminal-content cast, is evaluated by the independent successive maps. -/
theorem entireWordEvaluation (ρ : List I) (i j : I) (γ : Multiset I)
    (he : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (w : ContentCategory D Sc cutoff N γ)
    (x : (VacuumRepresentable.wordModuleAt D Sc cutoff N (j :: i :: ρ) γ he).obj w) :
    (VacuumRepresentable.wordIsoAt D Sc cutoff N (j :: i :: ρ) γ he).hom.total w x =
      wordDoubleEvaluationAt D Sc cutoff N ρ i j γ he w x :=
  congrArg (fun f => f x) (wordIsoAt_doubleEvaluation D Sc cutoff N ρ i j γ he w)

end OddMath.QuiverHecke.ELVOld.VacuumWordEvaluationConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumWordEvaluation
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing production module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"

#print axioms OddMath.QuiverHecke.ELVOld.VacuumSourceComparison.wordIso_total_pair
#print axioms OddMath.QuiverHecke.ELVOld.VacuumSourceComparison.wordIsoAt_doubleEvaluation
#print axioms OddMath.QuiverHecke.ELVOld.VacuumWordEvaluationConsumer.entireWordEvaluation
