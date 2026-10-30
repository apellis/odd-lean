import OddMath.QuiverHecke.CyclotomicAction.ELVModuleYoneda
noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (v : ContentCategory D Sc cutoff N β)
  (M : ContentModules D Sc cutoff N β)
example : (contentRepresentable D Sc cutoff N β v ⟶ M) ≃ₗ[k] M.obj v :=
  ModuleYoneda.homEquiv D Sc cutoff N β M
example (m : M.obj v) :
    ModuleYoneda.evaluate D Sc cutoff N β M (ModuleYoneda.fromElement D Sc cutoff N β M m) = m :=
  ModuleYoneda.evaluate_fromElement D Sc cutoff N β M m
example (t : contentRepresentable D Sc cutoff N β v ⟶ M) :
    ModuleYoneda.fromElement D Sc cutoff N β M (ModuleYoneda.evaluate D Sc cutoff N β M t) = t :=
  ModuleYoneda.fromElement_evaluate D Sc cutoff N β M t
example (t : contentRepresentable D Sc cutoff N β v ⟶ M) (p : ZMod 2) :
    ModuleYoneda.evaluate D Sc cutoff N β M (proj k p t) =
      (M.obj v).proj p (ModuleYoneda.evaluate D Sc cutoff N β M t) :=
  ModuleYoneda.evaluate_proj D Sc cutoff N β M t p
example (t : contentRepresentable D Sc cutoff N β v ⟶ M) (p : ZMod 2)
    (z : ContentCategory D Sc cutoff N β) (h : v ⟶ z) :
    ModuleYoneda.componentMap D Sc cutoff N β M t p z h =
      M.map (twist k p h) (ModuleYoneda.componentMap D Sc cutoff N β M t p v (𝟙 v)) :=
  ModuleYoneda.app_formula D Sc cutoff N β M t p z h

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleYoneda
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
