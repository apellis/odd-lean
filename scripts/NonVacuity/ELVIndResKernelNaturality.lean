import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernelNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory Opposite StringDiagrams OddMath OddMath.QuiverHecke ELVOld
open CyclotomicAction.AsymmetricParameters
namespace IndResNaturalityConsumer
private def cutoff (_ : Bool) : ℕ := 2
private abbrev C := OldCategory datum scalars cutoff
private abbrev J : C ⥤ C := 𝟭 C
private def M : C ⥤ SVec ℚ :=
  oldRepresentableFunctor datum scalars cutoff ⟨[false, true]⟩
private instance : M.Additive := by unfold M; infer_instance
private instance : M.Linear ℚ := by unfold M; infer_instance

example (v s t t' : C) (g : s ⟶ t) (b : v ⟶ s) (a : t ⟶ t') :
    (IndResKernel.targetMap (k := ℚ) J a).app (op v)
      (BalancedInduction.tensor J (J ⋙ IndResKernel.homModule (k := ℚ) v) s g b) =
      BalancedInduction.tensor J (J ⋙ IndResKernel.homModule (k := ℚ) v) s (g ≫ a) b :=
  BalancedInduction.postcompose_tensor J (J ⋙ IndResKernel.homModule (k := ℚ) v)
    a s g b

example {t t' : C} (a : t ⟶ t')
    (z : BalancedKernelTensor.Obj (IndResKernel.kernel (k := ℚ) J t) M) :
    IndResKernel.forward J M t'
        (BalancedKernelTensor.map M (IndResKernel.targetMap (k := ℚ) J a) z) =
      BalancedInduction.postcompose J (J ⋙ M) a (IndResKernel.forward J M t z) :=
  congrArg (fun f => f z) (IndResKernel.forward_targetMap J M a)

example {t t' : C} (a : t ⟶ t') (z : BalancedInduction.Obj J (J ⋙ M) t) :
    IndResKernel.backward J M t' (BalancedInduction.postcompose J (J ⋙ M) a z) =
      BalancedKernelTensor.map M (IndResKernel.targetMap (k := ℚ) J a)
        (IndResKernel.backward J M t z) :=
  congrArg (fun f => f z) (IndResKernel.backward_postcompose J M a)

end IndResNaturalityConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernelNaturality
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
