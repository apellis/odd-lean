import OddMath.QuiverHecke.CyclotomicAction.ELVContentBraidTransforms
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BraidTransformsConsumer
open CyclotomicAction.AsymmetricParameters

/-- The full natural-family relation with all three colours odd and equal. -/
example := contentBraidTransform_braid datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true true true (by simp) (0 + ([true,true,true] : Multiset Bool))
  rfl rfl rfl rfl rfl rfl
  ((0 + ([true] : Multiset Bool)) + ([true] : Multiset Bool)) rfl rfl (by decide)
  ((0 + ([true] : Multiset Bool)) + ([true] : Multiset Bool)) rfl rfl (by decide)
  ((0 + ([true] : Multiset Bool)) + ([true] : Multiset Bool)) rfl rfl (by decide)

/-- Adjacent equality on the coefficient parameters used by the action. -/
example := contentBraidTransform_braid datum (parameterTwist datum scalars) (fun _ => 12) 12
  (0 : Multiset Bool) true true false (by decide) (0 + ([true,true,false] : Multiset Bool))
  rfl rfl (by decide) (by decide) (by decide) (by decide)
  ((0 + ([true] : Multiset Bool)) + ([true] : Multiset Bool)) rfl rfl (by decide)
  ((0 + ([true] : Multiset Bool)) + ([false] : Multiset Bool)) rfl (by decide) (by decide)
  ((0 + ([true] : Multiset Bool)) + ([false] : Multiset Bool)) rfl (by decide) (by decide)

/-- Evaluation recovers the actual independently induced components on the vacuum. -/
example := contentBraidLeftTransform_evaluation datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true true true (0 + ([true,true,true] : Multiset Bool))
  rfl rfl rfl rfl
  ((0 + ([true] : Multiset Bool)) + ([true] : Multiset Bool)) rfl rfl (by decide)
  ((0 + ([true] : Multiset Bool)) + ([true] : Multiset Bool)) rfl rfl (by decide)
  (vacuumModule datum scalars (fun _ => 12) 12)
  (⟨⟨[true,true,true]⟩, by simp⟩ : ContentCategory datum scalars (fun _ => 12) 12
    (0 + ([true,true,true] : Multiset Bool)))

example := contentBraidRightTransform_evaluation datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true true false (0 + ([true,true,false] : Multiset Bool))
  rfl (by decide) (by decide) (by decide)
  ((0 + ([true] : Multiset Bool)) + ([false] : Multiset Bool)) rfl (by decide) (by decide)
  (vacuumModule datum scalars (fun _ => 12) 12)
  (⟨⟨[true,true,false]⟩, by simp⟩ : ContentCategory datum scalars (fun _ => 12) 12
    (0 + ([true,true,false] : Multiset Bool)))
end OddMath.QuiverHecke.ELVOld.BraidTransformsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentBraidTransforms
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
