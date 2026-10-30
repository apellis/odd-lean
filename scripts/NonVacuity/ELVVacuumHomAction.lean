import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumHomAction

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open VacuumHomAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem reservoirMixedCross_consumer (β : Multiset I) (i j : I) (hij : i ≠ j)
    (v : ContentCategory D Sc cutoff N β)
    (r : ContentCategory D Sc cutoff N (β + ([i, j] : Multiset I)))
    (t : (contentInductionTo D Sc cutoff N β [i, j] _ rfl).obj
        (contentRepresentable D Sc cutoff N β v) ⟶
      contentRepresentable D Sc cutoff N _ r) :
    pairing D Sc cutoff N
      (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j)) v r
      ((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j)
        (contentRepresentable D Sc cutoff N β v) ≫ t) =
    twist k (D.parity i * D.parity j)
      (pairing D Sc cutoff N (contentAppendTo D Sc cutoff N β [i, j] _ rfl) v r t) ≫
      contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
        (crossTwo D Sc i j) v :=
  mixedCross_postcompose D Sc cutoff N β i j hij v r t

theorem reservoirEqualCross_consumer (β : Multiset I) (i : I)
    (v : ContentCategory D Sc cutoff N β)
    (r : ContentCategory D Sc cutoff N (β + ([i, i] : Multiset I)))
    (t : (contentInductionTo D Sc cutoff N β [i, i] _ rfl).obj
        (contentRepresentable D Sc cutoff N β v) ⟶
      contentRepresentable D Sc cutoff N _ r) :
    pairing D Sc cutoff N
      (contentAppendTo D Sc cutoff N β [i, i] _ (content_pair_swap β i i)) v r
      ((contentInductionCross D Sc cutoff N β i i).app (D.parity i * D.parity i)
        (contentRepresentable D Sc cutoff N β v) ≫ t) =
    -(twist k (D.parity i * D.parity i)
      (pairing D Sc cutoff N (contentAppendTo D Sc cutoff N β [i, i] _ rfl) v r t) ≫
      contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i i)
        (crossTwo D Sc i i) v) :=
  equalCross_postcompose D Sc cutoff N β i v r t

#print axioms mixedCross_postcompose
#print axioms equalCross_postcompose

theorem reservoirWordCross_consumer (β : Multiset I) (i j : I)
    (v : ContentCategory D Sc cutoff N β) (ρ : List I)
    (hρ : VacuumRepresentable.content ρ = β + ([i, j] : Multiset I))
    (t : (contentInductionTo D Sc cutoff N β [i, j] _ rfl).obj
        (contentRepresentable D Sc cutoff N β v) ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N ρ _ hρ) :
    wordPairing D Sc cutoff N
      (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j)) v ρ hρ
      ((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j)
        (contentRepresentable D Sc cutoff N β v) ≫ t) =
    twist k (D.parity i * D.parity j)
      (wordPairing D Sc cutoff N (contentAppendTo D Sc cutoff N β [i, j] _ rfl) v ρ hρ t) ≫
      contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
        (contentCrossAffine D Sc i j) v :=
  cross_word_postcompose D Sc cutoff N β i j v ρ hρ t

#print axioms cross_word_postcompose
#print axioms cross_postcompose_of_mem

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumHomAction
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
