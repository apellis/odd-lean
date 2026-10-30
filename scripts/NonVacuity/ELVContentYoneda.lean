import OddMath.QuiverHecke.CyclotomicAction.ELVContentYoneda

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (v w : ContentCategory D Sc cutoff N β)

example : (contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) ≃ₗ[k] (w ⟶ v) :=
  ContentYoneda.homEquiv D Sc cutoff N β

example (f : w ⟶ v) :
    ContentYoneda.evaluate D Sc cutoff N β (ContentYoneda.fromArrow D Sc cutoff N β f) = f :=
  ContentYoneda.evaluate_fromArrow D Sc cutoff N β f

example (t : contentRepresentable D Sc cutoff N β v ⟶ contentRepresentable D Sc cutoff N β w)
    (p : ZMod 2) :
    ContentYoneda.evaluate D Sc cutoff N β (proj k p t) =
      proj k p (ContentYoneda.evaluate D Sc cutoff N β t) :=
  ContentYoneda.evaluate_proj D Sc cutoff N β t p

#print axioms ContentYoneda.homEquiv
#print axioms ContentYoneda.composition_component

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentYoneda
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
