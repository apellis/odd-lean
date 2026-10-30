import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumGeneratorCoordinates

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open VacuumGeneratorCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem mixedCross_consumer (β : Multiset I) (i j : I) (hij : i ≠ j)
    (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i, j] : Multiset I)))
    (h : (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j)).obj v ⟶ w) :
    equivTo D Sc cutoff N β [i, j] _ rfl v w
      (((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j)
        (contentRepresentable D Sc cutoff N β v)).app (D.parity i * D.parity j) w
        ((equivTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j) v w).symm h)) =
      contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
        (crossTwo D Sc i j) v ≫ twist k (D.parity i * D.parity j) h :=
  mixedCross_coordinates D Sc cutoff N β i j hij v w h

#print axioms mixedCross_coordinates

theorem equalCross_consumer (β : Multiset I) (i : I)
    (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i, i] : Multiset I)))
    (h : (contentAppendTo D Sc cutoff N β [i, i] _ (content_pair_swap β i i)).obj v ⟶ w) :
    equivTo D Sc cutoff N β [i, i] _ rfl v w
      (((contentInductionCross D Sc cutoff N β i i).app (D.parity i * D.parity i)
        (contentRepresentable D Sc cutoff N β v)).app (D.parity i * D.parity i) w
        ((equivTo D Sc cutoff N β [i, i] _ (content_pair_swap β i i) v w).symm h)) =
      -(contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i i)
        (crossTwo D Sc i i) v ≫ twist k (D.parity i * D.parity i) h) :=
  VacuumGeneratorCoordinates.equalCross_coordinates D Sc cutoff N β i v w h

#print axioms VacuumGeneratorCoordinates.equalCross_coordinates

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumGeneratorCoordinates
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
