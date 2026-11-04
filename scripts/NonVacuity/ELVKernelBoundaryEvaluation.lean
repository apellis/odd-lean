import OddMath.QuiverHecke.CyclotomicAction.ELVKernelBoundaryEvaluation
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld CyclotomicCrossingTensor
namespace NonVacuity.KernelBoundaryEvaluation
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 8
private def pos : OldCategory D Sc cutoff := ⟨[false,true,false]⟩
private def neg (i : Bool) : OldCategory D Sc cutoff := ⟨List.replicate 6 i⟩
private theorem positive_height (i : Bool) :
    0 ≤ contentCrossingHeight D cutoff i (pos.word : Multiset Bool) := by
  cases i <;> norm_num [contentCrossingHeight, cutoff, pos, D,
    CyclotomicAction.AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem negative_height (i : Bool) :
    contentCrossingHeight D cutoff i ((neg i).word : Multiset Bool) ≤ 0 := by
  cases i <;> norm_num [contentCrossingHeight, cutoff, neg, D,
    CyclotomicAction.AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]

-- Every finite window, for both odd moving vertices and both height signs.
example (i : Bool) (j : Fin (contentUnitCount D cutoff i (pos.word : Multiset Bool))) :=
  moduleUnitMatrixIso_window_inv_tensor D Sc cutoff (oldRepresentable D Sc cutoff pos)
    i pos pos (positive_height i) j (𝟙 ((append D Sc cutoff i).obj pos)) (𝟙 pos)
example (i : Bool) (j : Fin (contentCapCount D cutoff i ((neg i).word : Multiset Bool))) :=
  moduleCapMatrixIso_window_inv_tensor D Sc cutoff (oldRepresentable D Sc cutoff (neg i))
    i (neg i) (neg i) (negative_height i) j (𝟙 (neg i)) (𝟙 (neg i))
example (i : Bool) (j : Fin (contentUnitCount D cutoff i (pos.word : Multiset Bool))) (r : ℕ) :=
  positiveKernelBoundary_evaluate D Sc cutoff (oldRepresentable D Sc cutoff pos)
    i pos pos (positive_height i) j r (𝟙 pos) (𝟙 pos)
example (i : Bool) (j : Fin (contentCapCount D cutoff i ((neg i).word : Multiset Bool))) (r : ℕ) :=
  negativeKernelBoundary_evaluate D Sc cutoff (oldRepresentable D Sc cutoff (neg i))
    i (neg i) (neg i) (negative_height i) r j (𝟙 (neg i)) (𝟙 (neg i))
end NonVacuity.KernelBoundaryEvaluation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVKernelBoundaryEvaluation
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
