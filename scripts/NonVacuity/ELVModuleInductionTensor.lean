import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTensor
import Lean.Util.CollectAxioms

open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke.ELVOld

noncomputable section
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (σ : List I) (M : TruncatedModules D Sc cutoff N)

example (w : TruncatedCategory D Sc cutoff N) :
    moduleInductionTensor D Sc cutoff N σ
      ((moduleRestriction D Sc cutoff N σ).obj M) w →ₗ[k] M.obj w :=
  BalancedInduction.counit (truncatedAppend D Sc cutoff N σ) M.toFunctor w

example (v : TruncatedCategory D Sc cutoff N) :
    BalancedInduction.counit (truncatedAppend D Sc cutoff N σ) M.toFunctor
        ((truncatedAppend D Sc cutoff N σ).obj v) ∘ₗ
      BalancedInduction.unit (truncatedAppend D Sc cutoff N σ)
        ((moduleRestriction D Sc cutoff N σ).obj M).toFunctor v = LinearMap.id :=
  BalancedInduction.counit_unit (truncatedAppend D Sc cutoff N σ) M.toFunctor v

example {v v' w : TruncatedCategory D Sc cutoff N} (f : v ⟶ v')
    (h : (truncatedAppend D Sc cutoff N σ).obj v' ⟶ w) (m : M.obj v) :
    BalancedInduction.tensor (truncatedAppend D Sc cutoff N σ) M.toFunctor v
      ((truncatedAppend D Sc cutoff N σ).map f ≫ h) m =
    BalancedInduction.tensor (truncatedAppend D Sc cutoff N σ) M.toFunctor v'
      h (M.map f m) :=
  BalancedInduction.balance _ _ f h m

#print axioms BalancedInduction.lift
#print axioms BalancedInduction.lift_unique
#print axioms BalancedInduction.postcompose_comp
#print axioms BalancedInduction.unit_naturality
#print axioms BalancedInduction.counit_naturality
#print axioms BalancedInduction.counit_unit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTensor
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Induction tensor module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty induction tensor inventory"
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited all {names.size} declarations owned by {owner}; all transitive axioms allowed."
