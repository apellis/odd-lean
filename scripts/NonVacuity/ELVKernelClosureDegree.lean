import OddMath.QuiverHecke.CyclotomicAction.ELVKernelClosureDegree
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld CyclotomicCrossingTensor
namespace NonVacuity.KernelClosureDegree
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev sy := CyclotomicAction.AsymmetricParameters.symmetrizer
private theorem hc : Sc.Homogeneous := CyclotomicAction.AsymmetricParameters.homogeneous
private def cutoff (_ : Bool) : ℕ := 8
private def positive : OldCategory D Sc cutoff := ⟨[false,true,false]⟩
private def negative : OldCategory D Sc cutoff := ⟨[true,true,true,true,true,true]⟩
private def zeroHeight (i : Bool) : OldCategory D Sc cutoff :=
  ⟨if i then [true,true,true,true] else [false,false,false,false]⟩
private theorem positive_height (i : Bool) :
    0 ≤ contentCrossingHeight D cutoff i (positive.word : Multiset Bool) := by
  cases i <;> norm_num [contentCrossingHeight, cutoff, positive, D,
    CyclotomicAction.AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem negative_height :
    contentCrossingHeight D cutoff true (negative.word : Multiset Bool) ≤ 0 := by
  norm_num [contentCrossingHeight, cutoff, negative, D,
    CyclotomicAction.AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem zero_height (i : Bool) :
    contentCrossingHeight D cutoff i ((zeroHeight i).word : Multiset Bool) = 0 := by
  cases i <;> norm_num [contentCrossingHeight, cutoff, zeroHeight, D,
    CyclotomicAction.AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]

-- Unequal symmetrizers, all dot powers, and both nonzero-height orientations.
example (i : Bool) (r s : ℕ) :
    positiveKernelClosure D Sc cutoff i positive positive (positive_height i) r s (𝟙 positive) ∈
      oldDegree D sy Sc hc cutoff positive.word positive.word (2 * sy.d i * (r+s+1 : ℕ)) := by
  simpa only [zero_add] using positiveKernelClosure_degree D Sc cutoff sy hc i positive positive
    (positive_height i) r s ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree _)
example (r s : ℕ) :
    negativeKernelClosure D Sc cutoff true negative negative negative_height r s (𝟙 negative) ∈
      oldDegree D sy Sc hc cutoff negative.word negative.word (2 * sy.d true * (r+s+1 : ℕ)) := by
  simpa only [zero_add] using negativeKernelClosure_degree D Sc cutoff sy hc true negative negative
    negative_height r s ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree _)

-- Height zero uses either actual finite inverse with no secondary slots.
example (i : Bool) (r s : ℕ) := positiveKernelClosure_degree D Sc cutoff sy hc i
  (zeroHeight i) (zeroHeight i) (by rw [zero_height]) r s
  ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree (zeroHeight i))
example (i : Bool) (r s : ℕ) := negativeKernelClosure_degree D Sc cutoff sy hc i
  (zeroHeight i) (zeroHeight i) (by rw [zero_height]) r s
  ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree (zeroHeight i))
example (i : Bool) (r s : ℕ) : 0 < 2 * sy.d i * (r+s+1 : ℕ) :=
  kernelClosureDegree_pos D sy i r s

-- Evaluation uses the actual module unit, cap and canonical principal inverse.
example (r s : ℕ) := positiveKernelClosure_evaluate D Sc cutoff
  (oldRepresentable D Sc cutoff positive) false positive positive (positive_height false)
  r s (𝟙 positive) (𝟙 positive)
example (r s : ℕ) := negativeKernelClosure_evaluate D Sc cutoff
  (oldRepresentable D Sc cutoff negative) true negative negative negative_height
  r s (𝟙 negative) (𝟙 negative)
example (i : Bool) := negativeKernelCoordinates_single_tensor D Sc cutoff
  (oldRepresentable D Sc cutoff positive) i 0 positive positive
  (𝟙 ((append D Sc cutoff i).obj positive)) (𝟙 positive)
end NonVacuity.KernelClosureDegree

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVKernelClosureDegree
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
