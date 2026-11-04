import OddMath.QuiverHecke.CyclotomicAction.ELVKernelBoundaryDegrees
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld CyclotomicCrossingTensor
namespace NonVacuity.KernelBoundaryDegrees
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev sy := CyclotomicAction.AsymmetricParameters.symmetrizer
private theorem hc : Sc.Homogeneous := CyclotomicAction.AsymmetricParameters.homogeneous
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

-- The universally quantified finite windows below are nonempty at both vertices.
example (i : Bool) : 0 < contentUnitCount D cutoff i (pos.word : Multiset Bool) := by
  cases i <;> decide
example (i : Bool) : 0 < contentCapCount D cutoff i ((neg i).word : Multiset Bool) := by
  cases i <;> decide

-- Both unequal symmetrizer values and both odd vertices, at every finite slot.
example (i : Bool) (j : Fin (contentUnitCount D cutoff i (pos.word : Multiset Bool))) :=
  positiveKernelWindowInverse_degree D Sc cutoff sy hc i pos pos (positive_height i) j
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree _)
example (i : Bool) (j : Fin (contentCapCount D cutoff i ((neg i).word : Multiset Bool))) :=
  negativeKernelWindowInverse_degree D Sc cutoff sy hc i (neg i) (neg i) (negative_height i) j
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree _)

-- The arbitrary ordinary row/column is strictly beyond the entire finite window.
example (i : Bool) (j : Fin (contentUnitCount D cutoff i (pos.word : Multiset Bool))) (s : ℕ) :=
  positiveKernelBoundary_degree D Sc cutoff sy hc i pos pos (positive_height i) j
    (contentUnitCount D cutoff i (pos.word : Multiset Bool) + s)
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree _)
example (i : Bool) (j : Fin (contentCapCount D cutoff i ((neg i).word : Multiset Bool))) (s : ℕ) :=
  negativeKernelBoundary_degree D Sc cutoff sy hc i (neg i) (neg i) (negative_height i)
    (contentCapCount D cutoff i ((neg i).word : Multiset Bool) + s) j
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree _)
example (i : Bool) (j : Fin (contentUnitCount D cutoff i (pos.word : Multiset Bool))) (s : ℕ) :
    0 < 2 * sy.d i * ((contentUnitCount D cutoff i (pos.word : Multiset Bool) + s : ℕ) - (j.val : ℤ)) :=
  kernelBoundaryDegree_pos D sy i (by omega)
example (i : Bool) (j : Fin (contentCapCount D cutoff i ((neg i).word : Multiset Bool))) (s : ℕ) :
    0 < 2 * sy.d i * ((contentCapCount D cutoff i ((neg i).word : Multiset Bool) + s : ℕ) - (j.val : ℤ)) :=
  kernelBoundaryDegree_pos D sy i (by omega)
example : D.parity true = 1 := rfl
example : D.parity false = 1 := rfl
example : 2 * sy.d false = 4 := rfl
example : 2 * sy.d true = 2 := rfl
end NonVacuity.KernelBoundaryDegrees

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVKernelBoundaryDegrees
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
