import OddMath.QuiverHecke.CyclotomicAction.ELVModuleCentre
noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I)
example : Function.Surjective (contentRealize D Sc cutoff N β) :=
  ModuleCentre.contentRealize_surjective D Sc cutoff N β
example : ContentCoefficient D Sc cutoff N β ≃ₗ[k]
    (𝟙 (contentModuleTarget D Sc cutoff N β) ⟶ 𝟙 (contentModuleTarget D Sc cutoff N β)) :=
  ModuleCentre.centrePiEquiv D Sc cutoff N β
example (η : ModuleCentre.Centre D Sc cutoff N β) :
    contentRealize D Sc cutoff N β (ModuleCentre.reconstruct D Sc cutoff N β η) = η :=
  ModuleCentre.realize_reconstruct D Sc cutoff N β η
example (c : ContentCoefficient D Sc cutoff N β) :
    ModuleCentre.reconstruct D Sc cutoff N β (contentRealize D Sc cutoff N β c) = c :=
  ModuleCentre.reconstruct_realize D Sc cutoff N β c
example (η : ModuleCentre.Centre D Sc cutoff N β) (p : ZMod 2) :
    ModuleCentre.reconstruct D Sc cutoff N β (proj k p η) =
      proj k p (ModuleCentre.reconstruct D Sc cutoff N β η) :=
  ModuleCentre.reconstruct_proj D Sc cutoff N β η p
example (η : ModuleCentre.Centre D Sc cutoff N β) (p : ZMod 2)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β) (m : M.obj v) :
    (ModuleCentre.moduleMap D Sc cutoff N β η p M).app p v m =
      M.map (ModuleCentre.coefficient D Sc cutoff N β η p v) m :=
  ModuleCentre.action D Sc cutoff N β η p M v m
-- The odd/odd case explicitly uses both signs, without an invertibility-of-two hypothesis.
example (η : ModuleCentre.Centre D Sc cutoff N β)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (m : M.obj v) (hm : m ∈ (M.obj v).part 1) :
    (ModuleCentre.moduleMap D Sc cutoff N β η 1 M).app 1 v m =
      M.map (ModuleCentre.coefficient D Sc cutoff N β η 1 v) m :=
  ModuleCentre.action_of_mem D Sc cutoff N β η 1 M v hm
example (η : ModuleCentre.Centre D Sc cutoff N β) (p : ZMod 2)
    {v w : ContentCategory D Sc cutoff N β} {q : ZMod 2} (f : v ⟶ w)
    (hf : f ∈ parity (R := k) v w q) :
    f ≫ ModuleCentre.coefficient D Sc cutoff N β η p w =
      koszulSign p q • (ModuleCentre.coefficient D Sc cutoff N β η p v ≫ f) :=
  ModuleCentre.coefficient_naturality D Sc cutoff N β η p f hf

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleCentre
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
