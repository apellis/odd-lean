import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (σ : List I) :
    VacuumRepresentable.wordModule D Sc cutoff N σ ≅
      contentRepresentable D Sc cutoff N (VacuumRepresentable.content σ)
        (VacuumRepresentable.wordObject D Sc cutoff N σ) :=
  VacuumRepresentable.wordIso D Sc cutoff N σ

example (σ : List I) :
    (VacuumRepresentable.wordObject D Sc cutoff N σ).obj.word = σ.reverse :=
  VacuumRepresentable.wordObject_word D Sc cutoff N σ

example (β : Multiset I) (v : ContentCategory D Sc cutoff N β) (i : I)
    (w : ContentCategory D Sc cutoff N (β + ([i] : List I)))
    (h : (contentAppend D Sc cutoff N β [i]).obj v ⟶ w) :
    InductionRepresentable.forward D Sc cutoff N β [i] v w
      (BalancedInduction.transformLinear
        (VacuumRepresentable.appendEnd_supernatural D Sc cutoff N β [i]
          (show dotE D Sc [i] 0 ∈ Supercategory.parity (R := k) _ _ (D.parity i) from by
            simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1))
        (contentRepresentable D Sc cutoff N β v) w
        (InductionRepresentable.backward D Sc cutoff N β [i] v w h)) =
      VacuumRepresentable.appendEndComponent D Sc cutoff N β [i] (dotE D Sc [i] 0) v ≫
        Supercategory.twist k (D.parity i) h :=
  VacuumRepresentable.dot_coordinates D Sc cutoff N β v i w h

#print axioms VacuumRepresentable.wordIso
#print axioms VacuumRepresentable.dot_coordinates
#print axioms VacuumRepresentable.equalCross_coordinates
#print axioms VacuumRepresentable.appendEnd_identity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
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
