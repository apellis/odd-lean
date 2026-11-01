import OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Mathlib.LinearAlgebra.Prod
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory Opposite StringDiagrams OddMath OddMath.QuiverHecke
open CyclotomicAction.AsymmetricParameters ELVOld
namespace KernelTensorConsumer

private def cutoff (_ : Bool) : ℕ := 2
private abbrev C := OldCategory datum scalars cutoff
private def K : Cᵒᵖ ⥤ ModuleCat ℚ :=
  (Functor.const Cᵒᵖ).obj (ModuleCat.of ℚ (ℚ × ℚ))
private def swapKernel : K ≅ K :=
  (Functor.const Cᵒᵖ).mapIso (LinearEquiv.prodComm ℚ ℚ ℚ).toModuleIso
private def M : C ⥤ SVec ℚ :=
  oldRepresentableFunctor datum scalars cutoff ⟨[false, true]⟩

/-- A nontrivial coefficient isomorphism acts on a literal quotient tensor. -/
example (v : C) (m : M.obj v) :
    BalancedKernelTensor.equiv M swapKernel
      (BalancedKernelTensor.tensor K M v (1, 2) m) =
      BalancedKernelTensor.tensor K M v (2, 1) m :=
  BalancedKernelTensor.equiv_tensor M swapKernel v (1, 2) m

example : Function.Bijective (BalancedKernelTensor.map M swapKernel.hom) :=
  (BalancedKernelTensor.equiv M swapKernel).bijective

example : BalancedKernelTensor.Obj K M ≃ₗ[ℚ] BalancedKernelTensor.Obj K M :=
  BalancedKernelTensor.equivOfBijective M swapKernel.hom
    (fun _ => (LinearEquiv.prodComm ℚ ℚ ℚ).bijective)

/-- The quotient balance uses an arbitrary old quotient arrow. -/
example {v w : C} (a : v ⟶ w) (x : K.obj (op w)) (m : M.obj v) :
    BalancedKernelTensor.tensor K M v (K.map a.op x) m =
      BalancedKernelTensor.tensor K M w x (M.map a m) :=
  BalancedKernelTensor.balance K M a x m

end KernelTensorConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensor
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
