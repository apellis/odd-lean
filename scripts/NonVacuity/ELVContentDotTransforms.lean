import OddMath.QuiverHecke.CyclotomicAction.ELVContentDotTransforms
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.DotTransformsConsumer
open CyclotomicAction.AsymmetricParameters

example := contentTripleFirstDotMorphism_supernatural datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false true (0 + ([true,false,true] : Multiset Bool)) rfl

example := contentTripleFirstDotTransform_total datum (parameterTwist datum scalars)
  (fun _ => 12) 12 (0 : Multiset Bool) false true false
  (0 + ([false,true,false] : Multiset Bool)) rfl
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)

example := contentTripleMiddleDotMorphism_supernatural datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false true (0 + ([true,false,true] : Multiset Bool)) rfl

example := contentTripleMiddleDotTransform_total datum (parameterTwist datum scalars)
  (fun _ => 12) 12 (0 : Multiset Bool) false true false
  (0 + ([false,true,false] : Multiset Bool)) rfl
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)

example := contentTripleLastDotMorphism_supernatural datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false true (0 + ([true,false,true] : Multiset Bool)) rfl

example := contentTripleLastDotTransform_total datum (parameterTwist datum scalars)
  (fun _ => 12) 12 (0 : Multiset Bool) false true false
  (0 + ([false,true,false] : Multiset Bool)) rfl
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)

example := supernaturalTotalEndAlgHom
  (contentETripleSuperfunctor datum (parameterTwist datum scalars) (fun _ => 12) 12
    (0 : Multiset Bool) true false true (0 + ([true,false,true] : Multiset Bool)) rfl)
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)

end OddMath.QuiverHecke.ELVOld.DotTransformsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentDotTransforms
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
