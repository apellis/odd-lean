import OddMath.QuiverHecke.CyclotomicAction.ELVContentMixedBraidTransforms
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.MixedBraidTransformsConsumer
open CyclotomicAction.AsymmetricParameters

example := contentMixedBraidTransform datum scalars (fun _ => 12) 12 (0 : Multiset Bool)
  (i := true) (j := false) (by decide)
  ((0 + ([true] : Multiset Bool)) + ([true] : Multiset Bool)) rfl (by decide)
  ((0 + ([true] : Multiset Bool)) + ([false] : Multiset Bool)) rfl (by decide) (by decide)

example := contentTriplePolynomialTransform_evaluation datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
  (⟨⟨[true,false,true]⟩, by simp⟩ :
    ContentCategory datum (parameterTwist datum scalars) (fun _ => 12) 12
      (0 + ([true,false,true] : Multiset Bool)))

example := contentMixedBraidTransform datum scalars (fun _ => 12) 12 (0 : Multiset Bool)
  (i := false) (j := true) (by decide)
  ((0 + ([false] : Multiset Bool)) + ([false] : Multiset Bool)) rfl (by decide)
  ((0 + ([false] : Multiset Bool)) + ([true] : Multiset Bool)) rfl (by decide) (by decide)

example := contentTriplePolynomialTransform_evaluation datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) false true
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
  (⟨⟨[false,true,false]⟩, by simp⟩ :
    ContentCategory datum (parameterTwist datum scalars) (fun _ => 12) 12
      (0 + ([false,true,false] : Multiset Bool)))

end OddMath.QuiverHecke.ELVOld.MixedBraidTransformsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentMixedBraidTransforms
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
