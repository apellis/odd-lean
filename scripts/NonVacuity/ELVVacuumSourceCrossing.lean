import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSourceCrossing

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open VacuumSourceComparison
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem pairSource_mixedCross_consumer (β : Multiset I) (i j : I) (hne : i ≠ j) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (v : ContentCategory D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ)
    (x : ContentEPairSpace D Sc cutoff N β j i γ hji (contentRepresentable D Sc cutoff N β v) w) :
    pairCoordinates D Sc cutoff N β i j γ hij v w
      (contentEPairCross D Sc cutoff N β i j γ hij hji (contentRepresentable D Sc cutoff N β v) w x) =
      contentAppendToComponent D Sc cutoff N hij hji (crossTwo D Sc i j) v ≫
        twist k (D.parity i * D.parity j) (pairCoordinates D Sc cutoff N β j i γ hji v w x) :=
  pairCross_mixed_coordinates D Sc cutoff N β i j hne γ hij hji v w x

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSourceCrossing
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
