import OddMath.QuiverHecke.CyclotomicAction.ELVTripleDotAffineContexts
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.TripleDotAffineExamples
open CyclotomicAction.AsymmetricParameters

/-- Every literal context, including distinct odd colours and equal positions. -/
example (l j i : Bool) := tripleFirstDot_affineContexts datum (parameterTwist datum scalars) l j i
example (l j i : Bool) := tripleMiddleDot_affineContexts datum (parameterTwist datum scalars) l j i
example (l j i : Bool) := tripleLastDot_affineContexts datum (parameterTwist datum scalars) l j i
/-- The indexed middle and last polynomial generators are retained exactly. -/
example (l j i : Bool) := tripleMiddleDot_affineIndex datum (parameterTwist datum scalars) l j i
example (l j i : Bool) := tripleLastDot_affineIndex datum (parameterTwist datum scalars) l j i
end OddMath.QuiverHecke.ELVOld.TripleDotAffineExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVTripleDotAffineContexts
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
