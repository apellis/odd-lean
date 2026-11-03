import OddMath.QuiverHecke.CyclotomicAction.ELVKernelEntryDegrees
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor IndResKernel
namespace KernelEntryDegreesConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev sy := CyclotomicAction.AsymmetricParameters.symmetrizer
private theorem homogeneous : Sc.Homogeneous := CyclotomicAction.AsymmetricParameters.homogeneous
private def cutoff (_ : Bool) : ℕ := 8
local instance : GradedSupercategory ℚ (OldCategory D Sc cutoff) :=
  oldCategoryGradedSupercategory D Sc cutoff sy homogeneous
private abbrev J (i : Bool) := append D Sc cutoff i
local instance (i : Bool) : IsGradedSuperfunctor ℚ (J i) :=
  (oldAppendGraded D Sc cutoff sy homogeneous i).isGraded
private def mixed : OldCategory D Sc cutoff := ⟨[false,true,false]⟩
private abbrev up (i : Bool) := (J i).obj mixed
private def vector (i : Bool) : Component (k := ℚ) (J i) (up i) (up i) :=
  componentTensor (k := ℚ) (J i) (up i) (up i) mixed (𝟙 (up i)) (𝟙 (up i))
private theorem vector_degree (i : Bool) :
    vector i ∈ representedKernelDegree D Sc cutoff sy homogeneous i (up i) (up i) 0 := by
  have h := componentTensor_mem_integerDegree (k := ℚ) (J i) (up i) (up i) mixed
    (𝟙 (up i)) (𝟙 (up i)) (id_mem_degree (up i)) (id_mem_degree (up i))
  dsimp only [vector, representedKernelDegree, oldCategoryGradedSupercategory] at h ⊢
  simpa only [zero_add] using h

example (i : Bool) := actualMateKernelComponent_degree D Sc cutoff sy homogeneous i (up i) (up i)
  (vector_degree i)
example (i : Bool) := actualDotKernelComponent_degree D Sc cutoff sy homogeneous i (up i) (up i)
  (vector_degree i)
example (i : Bool) (m : ℕ) := actualDotKernelComponent_power_degree D Sc cutoff sy homogeneous i (up i) (up i)
  m (vector_degree i)
example (i : Bool) := actualCounitKernelComponent_degree D Sc cutoff sy homogeneous i (up i) (up i)
  (vector_degree i)
example (i : Bool) (m : ℕ) := actualCapKernelComponent_degree D Sc cutoff sy homogeneous i (up i) (up i)
  m (vector_degree i)
example (i : Bool) (m : ℕ) := actualUnitKernelComponent_degree D Sc cutoff sy homogeneous i (up i) (up i)
  m (id_mem_degree (up i))

/-- The zero-power cap really composes the two native identities. -/
example (i : Bool) : actualCounitKernelComponent D Sc cutoff i (up i) (up i) (vector i) = 𝟙 (up i) := by
  rw [vector, componentTensor, actualCounitKernelComponent_tensor, Category.id_comp]
example : -2 * sy.d false = -4 := rfl
example : -2 * sy.d true = -2 := rfl
example : 2 * sy.d false = 4 := rfl
example : 2 * sy.d true = 2 := rfl
end KernelEntryDegreesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVKernelEntryDegrees
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
