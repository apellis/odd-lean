import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernelInteger
import OddMath.QuiverHecke.CyclotomicAction.ELVOldGeneratorDegrees
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor IndResKernel
namespace IndResKernelIntegerConsumer
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
example (i : Bool) := integerDegree_internal (k := ℚ) (J i) (up i) (up i)
example (i : Bool) := iSup_integerDegree_eq_top (k := ℚ) (J i) (up i) (up i)
example (i : Bool) (n : ℤ) := integerProjection_tensor (k := ℚ) (J i) (up i) (up i) n mixed
  (𝟙 (up i)) (𝟙 (up i)) (id_mem_degree (up i)) (id_mem_degree (up i))
example (i : Bool) : componentTensor (k := ℚ) (J i) (up i) (up i) mixed
    (oldAppendDotComponent D Sc cutoff i mixed) (𝟙 (up i)) ∈
    integerDegree (k := ℚ) (J i) (up i) (up i) (2 * sy.d i + 0) :=
  componentTensor_mem_integerDegree (J i) (up i) (up i) mixed _ _
    (oldAppendDotComponent_degree D Sc cutoff sy homogeneous i mixed) (id_mem_degree (up i))
example (i : Bool) (n : ℤ) := integerProjection_tensor (k := ℚ) (J i) (up i) (up i) n mixed
  (oldAppendDotComponent D Sc cutoff i mixed) (𝟙 (up i))
  (oldAppendDotComponent_degree D Sc cutoff sy homogeneous i mixed) (id_mem_degree (up i))
example (i : Bool) (n : ℤ) (x : Component (k := ℚ) (J i) (up i) (up i)) :=
  integerProjection_mem (k := ℚ) (J i) (up i) (up i) n x
example (i : Bool) (n : ℤ) (x : Component (k := ℚ) (J i) (up i) (up i)) :=
  mem_integerDegree_iff_projection (k := ℚ) (J i) (up i) (up i) n x
end IndResKernelIntegerConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernelInteger
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
