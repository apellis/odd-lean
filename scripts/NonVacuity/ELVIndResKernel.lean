import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory Opposite StringDiagrams OddMath OddMath.QuiverHecke ELVOld
open CyclotomicAction.AsymmetricParameters
namespace IndResKernelConsumer
private def cutoff (_ : Bool) : ℕ := 2
private abbrev C := OldCategory datum scalars cutoff
private def M : C ⥤ SVec ℚ :=
  oldRepresentableFunctor datum scalars cutoff ⟨[false, true]⟩
private instance : M.Additive := by
  unfold M
  infer_instance
private instance : M.Linear ℚ := by
  unfold M
  infer_instance
private abbrev J : C ⥤ C := 𝟭 C

/-- Both balances are evaluated on arbitrary old quotient arrows. -/
example (v s t : C) (g : s ⟶ t) (b : v ⟶ s) (m : M.obj v) :
    IndResKernel.equiv J M t
      (BalancedKernelTensor.tensor (IndResKernel.kernel (k := ℚ) J t) M v
        (BalancedInduction.tensor J (J ⋙ IndResKernel.homModule (k := ℚ) v) s g b) m) =
      BalancedInduction.tensor J (J ⋙ M) s g (M.map b m) := by
  change IndResKernel.forward J M t _ = _
  rw [IndResKernel.forward_tensor, IndResKernel.evaluate_tensor]
  rfl

example (s t : C) (g : s ⟶ t) (m : M.obj s) :
    (IndResKernel.equiv J M t).symm (BalancedInduction.tensor J (J ⋙ M) s g m) =
      BalancedKernelTensor.tensor (IndResKernel.kernel (k := ℚ) J t) M s
        (BalancedInduction.tensor J (J ⋙ IndResKernel.homModule (k := ℚ) s) s g (𝟙 s)) m :=
  IndResKernel.backward_tensor J M t s g m

example (t : C) : Function.Bijective (IndResKernel.forward J M t) :=
  (IndResKernel.equiv J M t).bijective

end IndResKernelConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernel
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
