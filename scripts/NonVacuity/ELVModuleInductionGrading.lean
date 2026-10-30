import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionGrading
import Lean.Util.CollectAxioms

open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke.ELVOld

noncomputable section
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (σ : List I) (M : TruncatedModules D Sc cutoff N)

example (w : TruncatedCategory D Sc cutoff N) : SVec k :=
  BalancedInduction.superspace (truncatedAppend D Sc cutoff N σ) M.toFunctor w

example : Supercategory.IsSuperfunctor k
    (BalancedInduction.moduleFunctor (truncatedAppend D Sc cutoff N σ) M.toFunctor) :=
  inferInstance

example (w : TruncatedCategory D Sc cutoff N) :
    (BalancedInduction.superspace (truncatedAppend D Sc cutoff N σ) M.toFunctor w).carrier =
      moduleInductionTensor D Sc cutoff N σ M w := rfl

example {w z : TruncatedCategory D Sc cutoff N} {p : ZMod 2} (a : w ⟶ z)
    (ha : a ∈ Supercategory.parity (R := k) w z p) :
    (BalancedInduction.moduleFunctor (truncatedAppend D Sc cutoff N σ) M.toFunctor).map a ∈
      Supercategory.parity (R := k) _ _ p :=
  Supercategory.map_mem _ ha

#print axioms BalancedInduction.oddSummand_balance
#print axioms BalancedInduction.odd_comp_odd
#print axioms BalancedInduction.superspace
#print axioms BalancedInduction.proj_tensor
#print axioms BalancedInduction.postcompose_mem
#print axioms BalancedInduction.moduleFunctor_super

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionGrading
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Induction grading module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty induction grading inventory"
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited all {names.size} declarations owned by {owner}; all transitive axioms allowed."
