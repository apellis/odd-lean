import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionRelations
import NonVacuity.ELVModuleInductionTransform
import NonVacuity.ELVContentModuleAction
import NonVacuity.ELVModuleAdjunction

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.QuiverHecke.ELVOld
universe u
namespace ELVModuleInductionRelationsConsumer
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
variable {J K L : C ⥤ D}
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [L.Additive] [L.Linear k] [IsSuperfunctor k L]
variable {α : ∀ v, J.obj v ⟶ K.obj v} {β : ∀ v, K.obj v ⟶ L.obj v}

example (hα : IsSupernatural k 1 α) (hβ : IsSupernatural k 1 β)
    (M : Superfunctor k C (SVec k)) :
    BalancedInduction.transformComponent hβ M ≫ BalancedInduction.transformComponent hα M =
      -(BalancedInduction.transformComponent (hα.comp hβ) M) := by
  simpa only [mul_one, Supercategory.sign_one, neg_one_smul] using
    BalancedInduction.transformComponent_comp hα hβ M
end ELVModuleInductionRelationsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionRelations
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules[idx.toNat]! == owner then
        for ax in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty owned audit"
  logInfo m!"Audited all {count} declarations in {owner}."
