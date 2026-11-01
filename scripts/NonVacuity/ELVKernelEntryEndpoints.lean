import OddMath.QuiverHecke.CyclotomicAction.ELVKernelEntryEndpoints
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicAction.AsymmetricParameters ELVOld.CyclotomicCrossingTensor
namespace KernelEntryEndpointsConsumer
private def cutoff (_ : Bool) : ℕ := 2
private abbrev C := OldCategory datum scalars cutoff
private def M : Superfunctor ℚ C (SVec ℚ) :=
  oldRepresentable datum scalars cutoff ⟨[false, true]⟩

example (i : Bool) (v t : C) (m : M.obj v)
    (z : IndResKernel.Component (k := ℚ) (append datum scalars cutoff i) v t) :
    kernelMateEvaluationEndpoint datum scalars cutoff i M v t m z =
      moduleMateEvaluationEndpoint datum scalars cutoff i M v t m z :=
  LinearMap.congr_fun (mateEvaluationEndpoints_eq datum scalars cutoff i M v t m) z

example (i : Bool) (v t : C) (m : M.obj v)
    (z : IndResKernel.Component (k := ℚ) (append datum scalars cutoff i) v t) :
    moduleMateEvaluationEndpoint datum scalars cutoff i M v t m z =
      moduleMateLinear datum scalars cutoff i M t
        (moduleSourceEvaluation datum scalars cutoff i M v t m z) :=
  moduleMateEvaluationEndpoint_apply datum scalars cutoff i M v t m z

example (i : Bool) (t : C) (z : mateSourceSpace datum scalars cutoff i M t) :
    moduleMateLinear datum scalars cutoff i M t z =
      (matrixMateComponent datum scalars cutoff i M).total t z :=
  moduleMateLinear_apply datum scalars cutoff i M t z

end KernelEntryEndpointsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVKernelEntryEndpoints
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
