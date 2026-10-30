import OddMath.QuiverHecke.CyclotomicAction.ELVModuleRestriction
import NonVacuity.ELVTruncatedAppend
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace ELVModuleRestrictionConsumer
open ELVCoefficientCategoryConsumer

abbrev Modules := TruncatedModules datum scalars (fun _ => 2) 3

/-- Arbitrary modules and arbitrary odd module maps, not a finite set of tests. -/
theorem dot_oddModuleMap (M L : Modules) (f : M ⟶ L)
    (hf : f ∈ parity (R := ℚ) M L 1) :
    (moduleRestriction datum scalars (fun _ => 2) 3 [()]).map f ≫
        (moduleRestrictionDot datum scalars (fun _ => 2) 3 ()).app 1 L =
      -((moduleRestrictionDot datum scalars (fun _ => 2) 3 ()).app 1 M ≫
        (moduleRestriction datum scalars (fun _ => 2) 3 [()]).map f) := by
  have he := (moduleRestrictionDot datum scalars (fun _ => 2) 3 ()).naturality 1 f hf
  simpa only [koszulSign_one_one, neg_one_smul] using he

example (M : Modules) (v : TruncatedCategory datum scalars (fun _ => 2) 3) :
    ((moduleRestrictionDot datum scalars (fun _ => 2) 3 ()).app 1 M).app 1 v =
      M.map (truncatedAppendComponent datum scalars (fun _ => 2) 3
        (dotE datum scalars [()] 0) v) :=
  moduleRestrictionTransform_app datum scalars (fun _ => 2) 3 _ M v

end ELVModuleRestrictionConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVModuleRestriction]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if owners.contains modules[idx.toNat]! then
        for ax in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations audited"
  logInfo m!"Audited all {count} module-restriction declarations."
#print axioms ELVModuleRestrictionConsumer.dot_oddModuleMap
