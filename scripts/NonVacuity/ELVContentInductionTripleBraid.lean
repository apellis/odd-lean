import OddMath.QuiverHecke.CyclotomicAction.ELVContentInductionTripleBraid
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ContentInductionTripleBraidExamples
open CyclotomicAction.AsymmetricParameters

/-- All three odd colours equal on the full-coefficient regular vacuum. -/
example := contentInduction_uncorrected_braid datum (parameterTwist datum scalars) (fun _ => 12) 12
  0 true true true (by decide) (0 + ([true,true,true] : Multiset Bool))
  rfl rfl rfl rfl rfl rfl
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)

/-- Equal adjacent colours with distinct odd outer colours. Every source
word equality is proved, rather than passed as a consumer premise. -/
example := contentInduction_uncorrected_braid datum (parameterTwist datum scalars) (fun _ => 12) 12
  0 true true false (by decide) (0 + ([true,true,false] : Multiset Bool))
  rfl rfl (by decide) (by decide) (by decide) (by decide)
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
example := contentInduction_uncorrected_braid datum (parameterTwist datum scalars) (fun _ => 12) 12
  0 true false false (by decide) (0 + ([true,false,false] : Multiset Bool))
  rfl (by decide) (by decide) (by decide) rfl (by decide)
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
end OddMath.QuiverHecke.ELVOld.ContentInductionTripleBraidExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentInductionTripleBraid
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
