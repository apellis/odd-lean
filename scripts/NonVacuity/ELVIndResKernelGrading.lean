import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernelGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicAction.AsymmetricParameters
namespace IndResKernelGradingConsumer
private def cutoff (_ : Bool) : ℕ := 2
private abbrev C := OldCategory datum scalars cutoff
private abbrev J : C ⥤ C := 𝟭 C

example (v : C) : IsSuperfunctor ℚ (IndResKernel.homModule (k := ℚ) v) :=
  inferInstance

example (t : C) :
    BalancedKernelTensor.IsGradedKernel (IndResKernel.kernel (k := ℚ) J t)
      (IndResKernel.coefficientGrading (k := ℚ) J t) :=
  IndResKernel.isGradedKernel J t

/-- Odd source components retain degree one in the actual old quotient kernel. -/
example (v w t : C) (a : v ⟶ w) :
    (IndResKernel.precompose (k := ℚ) J (proj ℚ 1 a) t :
      BalancedInduction.superspace J (J ⋙ IndResKernel.homModule (k := ℚ) w) t ⟶
        BalancedInduction.superspace J (J ⋙ IndResKernel.homModule (k := ℚ) v) t) ∈
      parity (R := ℚ) _ _ 1 :=
  IndResKernel.precompose_mem J (proj ℚ 1 a) (proj_mem 1 a) t

example (v t : C) :
    (IndResKernel.precompose (k := ℚ) J (𝟙 v) t :
      BalancedInduction.superspace J (J ⋙ IndResKernel.homModule (k := ℚ) v) t ⟶
        BalancedInduction.superspace J (J ⋙ IndResKernel.homModule (k := ℚ) v) t) ∈
      parity (R := ℚ) _ _ 0 :=
  IndResKernel.precompose_mem J (𝟙 v) (id_mem v) t

example (t v : C) :
    BalancedKernelTensor.coefficientSpace (IndResKernel.coefficientGrading (k := ℚ) J t) v =
      BalancedInduction.superspace J (J ⋙ IndResKernel.homModule (k := ℚ) v) t :=
  IndResKernel.coefficientSpace_eq J t v

end IndResKernelGradingConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernelGrading
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
