import OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensorCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicAction.AsymmetricParameters
open CyclotomicCrossingTensor.TensorMatrixCoordinates
namespace KernelTensorCoordinatesConsumer
private def cutoff (_ : Bool) : ℕ := 2
private abbrev C := OldCategory datum scalars cutoff
private def M : Superfunctor ℚ C (SVec ℚ) :=
  oldRepresentable datum scalars cutoff ⟨[false, true]⟩

example (v t : C) (b : v ⟶ t) (m : M.obj v) :
    identityKernelCoordinates datum scalars cutoff M t
      (BalancedKernelTensor.tensor (BalancedKernelTensor.inductionKernel (k := ℚ)
        (𝟭 C) t) M.toFunctor v b m) = M.map b m :=
  identityKernelCoordinates_tensor datum scalars cutoff M v t b m

/-- The empty finite window still retains the canonically shifted mate slot. -/
example (i : Bool) (t : C) :
    Function.Bijective (positiveKernelCoordinates datum scalars cutoff M i 0 t) :=
  (positiveKernelCoordinates datum scalars cutoff M i 0 t).bijective

/-- The two-slot window includes distinct ordinary dot parity shifts. -/
example (i : Bool) (t : C) :
    Function.Bijective (negativeKernelCoordinates datum scalars cutoff M i 2 t) :=
  (negativeKernelCoordinates datum scalars cutoff M i 2 t).bijective

example (i : Bool) (t : C)
    (z : BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel
        (CyclotomicCrossingTensor.positiveKernelFamily datum scalars cutoff i 2 t)) M.toFunctor) :
    positiveKernelCoordinates datum scalars cutoff M i 2 t z (some ⟨1, by decide⟩) =
      positiveSlotCoordinates datum scalars cutoff M i 2 t (some ⟨1, by decide⟩)
        (BalancedKernelTensor.map M.toFunctor
          (BalancedKernelTensor.piProjection
            (CyclotomicCrossingTensor.positiveKernelFamily datum scalars cutoff i 2 t)
              (some ⟨1, by decide⟩)) z) :=
  positiveKernelCoordinates_apply datum scalars cutoff M i 2 t z (some ⟨1, by decide⟩)

end KernelTensorCoordinatesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensorCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
