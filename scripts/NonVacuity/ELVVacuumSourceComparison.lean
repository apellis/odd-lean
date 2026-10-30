import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSourceComparison

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open VacuumSourceComparison
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem iteratedSource_mixedCross_consumer (β : Multiset I) (i j : I) (hne : i ≠ j)
    (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I)))
    (x : ContentEPairSpace D Sc cutoff N β j i _ (content_pair_swap β i j)
      (contentRepresentable D Sc cutoff N β v) w) :
    VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [i,j] _ rfl v w
      (((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j)
        (contentRepresentable D Sc cutoff N β v)).app (D.parity i * D.parity j) w
        (contentEPairEquiv D Sc cutoff N β j i _ (content_pair_swap β i j)
          (contentRepresentable D Sc cutoff N β v) w x)) =
      contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j) (crossTwo D Sc i j) v ≫
        twist k (D.parity i * D.parity j)
          (pairCoordinates D Sc cutoff N β j i _ (content_pair_swap β i j) v w x) :=
  mixedCross_coordinates D Sc cutoff N β i j hne v w x

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSourceComparison
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
