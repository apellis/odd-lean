import OddMath.QuiverHecke.CyclotomicAction.ELVContentCorrectionCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ContentCorrectionCoordinatesExamples
open CyclotomicAction.AsymmetricParameters

/-- Both repeated outer colours on the regular coefficient vacuum. The
common output is specified independently of the intermediate words. -/
example := contentMixedBraid_at_polynomial datum scalars (fun _ => 12) 12
  0 false true (by decide) ([false,true,false] : Multiset Bool)
  (by simp) (by decide) (by decide)
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
  (⟨⟨[false,true,false]⟩, rfl⟩ : ContentCategory datum (parameterTwist datum scalars)
    (fun _ => 12) 12 ([false,true,false] : Multiset Bool))
example := contentMixedBraid_at_polynomial datum scalars (fun _ => 12) 12
  0 true false (by decide) ([true,false,true] : Multiset Bool)
  (by simp) (by decide) (by decide)
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
  (⟨⟨[true,false,true]⟩, rfl⟩ : ContentCategory datum (parameterTwist datum scalars)
    (fun _ => 12) 12 ([true,false,true] : Multiset Bool))
end OddMath.QuiverHecke.ELVOld.ContentCorrectionCoordinatesExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentCorrectionCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
