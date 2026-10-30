import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSourceWord

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open VacuumSourceComparison
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem actualWordSource_mixedCross_consumer (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (hne : i ≠ j) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff N γ)
    (x : ContentEPairSpace D Sc cutoff N β j i γ hji
      (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) w) :
    wordPairCoordinates D Sc cutoff N ρ β hρ i j γ hij w
      (contentEPairCross D Sc cutoff N β i j γ hij hji
        (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) w x) =
    contentAppendToComponent D Sc cutoff N hij hji (crossTwo D Sc i j)
      (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) ≫
        twist k (D.parity i * D.parity j)
          (wordPairCoordinates D Sc cutoff N ρ β hρ j i γ hji w x) :=
  wordPairCross_mixed D Sc cutoff N ρ β hρ i j hne γ hij hji w x

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSourceWord
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
