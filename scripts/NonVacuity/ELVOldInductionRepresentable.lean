import OddMath.QuiverHecke.CyclotomicAction.ELVOldInductionRepresentable
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
namespace OldInductionRepresentableConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev cutoff : Bool → ℕ := fun _ => 12
private abbrev v : OldCategory D Sc cutoff := ⟨[false, true]⟩
example : (OldInductionRepresentable.iso D Sc cutoff false v).hom ≫
    (OldInductionRepresentable.iso D Sc cutoff false v).inv = 𝟙 _ :=
  (OldInductionRepresentable.iso D Sc cutoff false v).hom_inv_id
example : (OldInductionRepresentable.iso D Sc cutoff false v).hom ∈ parity (R := ℚ) _ _ 0 :=
  OldInductionRepresentable.iso_hom_mem D Sc cutoff false v
example (t : OldCategory D Sc cutoff)
    (h : (CyclotomicCrossingTensor.append D Sc cutoff false).obj v ⟶
      (CyclotomicCrossingTensor.append D Sc cutoff false).obj t) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff false v t
      ((OldInductionRepresentable.upperHomEquiv D Sc cutoff false v t).symm h) = h :=
  (OldInductionRepresentable.upperHomEquiv D Sc cutoff false v t).apply_symm_apply h
example (t z : OldCategory D Sc cutoff)
    (h : (CyclotomicCrossingTensor.append D Sc cutoff false).obj z ⟶
      (CyclotomicCrossingTensor.append D Sc cutoff false).obj t) (g : v ⟶ z) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff false v t
      (BalancedInduction.tensor (CyclotomicCrossingTensor.append D Sc cutoff false)
        (oldRepresentableFunctor D Sc cutoff v) z h g) =
      (CyclotomicCrossingTensor.append D Sc cutoff false).map g ≫ h :=
  OldInductionRepresentable.upperHomEquiv_tensor D Sc cutoff false v t z h g
end OldInductionRepresentableConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldInductionRepresentable
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
