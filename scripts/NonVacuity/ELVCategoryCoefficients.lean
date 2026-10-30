import OddMath.QuiverHecke.CyclotomicAction.ELVCategoryCoefficients
noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

example [Finite I] (T : PiSCat k) :
    SwappedAssembly.ProbeWindow.CoefficientIdeal (T ⟶ contentModuleTarget D Sc cutoff N β) :=
  contentModuleCoefficientIdeal D Sc cutoff N β sy hc T

example : (contentModuleTarget D Sc cutoff N β).carrier = ContentModules D Sc cutoff N β := rfl

example (c d : ContentCoefficient D Sc cutoff N β) :
    contentRealize D Sc cutoff N β (c ≫ d) =
      contentRealize D Sc cutoff N β c ≫ contentRealize D Sc cutoff N β d :=
  contentRealize_comp D Sc cutoff N β c d

#print axioms contentModuleCoefficientIdeal
#print axioms contentModule_coefficient_eq_zero

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVCategoryCoefficients]
  for owner in owners do
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
