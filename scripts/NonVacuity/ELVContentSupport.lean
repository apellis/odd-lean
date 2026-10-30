import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleBound
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

example [Finite I] (v w : List I) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegree D Sc cutoff sy hc N v w n = ⊥ :=
  truncatedContent_bounded D Sc cutoff sy hc N v w

example (M : ℤ) (hM : 0 ≤ M)
    (hb : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (v w : List I) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegree D Sc cutoff sy hc N v w n = ⊥ :=
  truncatedContent_bounded_of_bound D Sc cutoff sy hc N M hM hb v w

example [Finite I] (v : List I) (T : PiSCat k) :
    SwappedAssembly.ProbeWindow.CoefficientIdeal
      (T ⟶ SwappedAssembly.RegularReservoir.moduleTarget
        (truncatedEndGSuperAlg D Sc cutoff N sy hc v)) :=
  truncatedContentModuleCoefficientIdeal D Sc cutoff N sy hc v T

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVAppendSpanning,
    `OddMath.QuiverHecke.CyclotomicAction.ELVAppendDegree,
    `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSupport,
    `OddMath.QuiverHecke.CyclotomicAction.ELVContentSupport,
    `OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleBound]
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
