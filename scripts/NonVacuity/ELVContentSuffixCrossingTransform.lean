import OddMath.QuiverHecke.CyclotomicAction.ELVContentSuffixCrossingTransform
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.SuffixCrossingTransformConsumer
open CyclotomicAction.AsymmetricParameters

example := contentSuffixCrossMorphism_source datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false true (0 + ([true,false,true] : Multiset Bool))
  rfl (by decide) (vacuumModule datum scalars (fun _ => 12) 12)

example := contentSuffixCrossMorphism_supernatural datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false true (0 + ([true,false,true] : Multiset Bool))
  rfl (by decide)

example := contentSuffixCrossTransform_total datum (parameterTwist datum scalars)
  (fun _ => 12) 12 (0 : Multiset Bool) false true true
  (0 + ([false,true,true] : Multiset Bool)) rfl rfl
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)

example := contentSuffixCrossTransform_evaluation datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false true (0 + ([true,false,true] : Multiset Bool))
  rfl (by decide) (vacuumModule datum scalars (fun _ => 12) 12)
  (⟨⟨[true,false,true]⟩, by simp⟩ : ContentCategory datum scalars (fun _ => 12) 12
    (0 + ([true,false,true] : Multiset Bool)))

example := contentSuffixCrossTransform_evaluation datum (parameterTwist datum scalars)
  (fun _ => 12) 12 (0 : Multiset Bool) false true true
  (0 + ([false,true,true] : Multiset Bool)) rfl rfl
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
  (⟨⟨[false,true,true]⟩, by simp⟩ :
    ContentCategory datum (parameterTwist datum scalars) (fun _ => 12) 12
      (0 + ([false,true,true] : Multiset Bool)))
end OddMath.QuiverHecke.ELVOld.SuffixCrossingTransformConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentSuffixCrossingTransform
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
