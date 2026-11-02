import OddMath.QuiverHecke.CyclotomicAction.ELVInductionKernelGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendSuperfunctor
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke ELVOld
namespace InductionKernelGradingConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev C := OldCategory D Sc (fun _ => 4)
private abbrev J := CyclotomicCrossingTensor.append D Sc (fun _ => 4) false
private abbrev M := oldRepresentable D Sc (fun _ => 4) (⟨[true,false]⟩ : C)
private abbrev w : C := ⟨[false,true,false]⟩
private abbrev K := BalancedKernelTensor.inductionKernel (k := ℚ) J w
private abbrev G := BalancedKernelTensor.inductionKernelGrading (k := ℚ) J w
private abbrev hG := BalancedKernelTensor.inductionKernel_isGraded (k := ℚ) J w

private abbrev S := BalancedKernelTensor.superspace K G M.toFunctor hG
private abbrev T := BalancedInduction.superspace J M.toFunctor w

example :
    ((BalancedKernelTensor.inductionKernelEquiv J M.toFunctor w).toLinearMap : S ⟶ T) ∈
      parity (R := ℚ) S T 0 :=
  BalancedKernelTensor.inductionKernelEquiv_even J M w

example (q : ZMod 2) (v : C) (g : J.obj v ⟶ w) :
    BalancedKernelTensor.coefficientProj G v q g = proj ℚ q g :=
  LinearMap.congr_fun (BalancedKernelTensor.inductionKernel_coefficientProj (k := ℚ) J w v q) g

end InductionKernelGradingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionKernelGrading
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
