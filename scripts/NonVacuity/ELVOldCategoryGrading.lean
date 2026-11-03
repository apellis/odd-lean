import OddMath.QuiverHecke.CyclotomicAction.ELVOldCategoryGrading
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
namespace OldCategoryGradingConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev sy := CyclotomicAction.AsymmetricParameters.symmetrizer
private theorem homogeneous : Sc.Homogeneous := CyclotomicAction.AsymmetricParameters.homogeneous
private def cutoff (_ : Bool) : ℕ := 8
local instance : GradedSupercategory ℚ (OldCategory D Sc cutoff) :=
  oldCategoryGradedSupercategory D Sc cutoff sy homogeneous
example (i : Bool) := oldAppendGraded D Sc cutoff sy homogeneous i
example (i : Bool) (n : ℤ) (v w : OldCategory D Sc cutoff) (f : v ⟶ w)
    (hf : f ∈ oldDegree D sy Sc homogeneous cutoff v.word w.word n) :=
  oldAppend_mem_degree D Sc cutoff sy homogeneous i hf
private def mixed : OldCategory D Sc cutoff := ⟨[false,true,false]⟩
example : (𝟙 mixed) ∈ degree (R := ℚ) mixed mixed 0 := id_mem_degree mixed
example (i : Bool) :
    (CyclotomicCrossingTensor.append D Sc cutoff i).map (𝟙 mixed) ∈
      oldDegree D sy Sc homogeneous cutoff (mixed.word ++ [i]) (mixed.word ++ [i]) 0 :=
  oldAppend_mem_degree D Sc cutoff sy homogeneous i (id_mem_degree mixed)
example (p : ZMod 2) (n : ℤ) (f : mixed ⟶ mixed)
    (hf : f ∈ degree (R := ℚ) mixed mixed n) :
    proj ℚ p f ∈ degree (R := ℚ) mixed mixed n := proj_mem_degree p hf
end OldCategoryGradingConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldCategoryGrading
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
