import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import OddMath.QuiverHecke.CyclotomicAction.ELVParameterUntwist
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (β : Multiset I) (i : I) (M : ContentModules D Sc cutoff N β) :
    (contentInductionCross D Sc cutoff N β i i).app (D.parity i * D.parity i) M ≫
      (contentInductionCross D Sc cutoff N β i i).app (D.parity i * D.parity i) M = 0 :=
  contentInductionCross_square D Sc cutoff N β i M

example (β : Multiset I) (i : I) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I))) :
    (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w).comp
        (contentInductionEndLinear D Sc cutoff N (pairDot_one_parity D Sc i) M w) -
      sign k (D.parity i * D.parity i) •
        ((contentInductionEndLinear D Sc cutoff N (pairDot_zero_parity D Sc i) M w).comp
          (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w)) =
      LinearMap.id :=
  contentInduction_normalized_slide_linear D Sc cutoff N β i M w

example (β : Multiset I) (i : I) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I))) :
    (contentInductionEndLinear D Sc cutoff N (pairDot_one_parity D Sc i) M w).comp
        (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w) -
      sign k (D.parity i * D.parity i) •
        ((contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w).comp
          (contentInductionEndLinear D Sc cutoff N (pairDot_zero_parity D Sc i) M w)) =
      LinearMap.id :=
  contentInduction_normalized_slide_right_linear D Sc cutoff N β i M w

-- Every owned module is audited from its serialized declaration inventory,
-- not an environment scan which can omit generated or private declarations.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVModuleRestriction,
    `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTensor,
    `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionGrading,
    `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionMap,
    `OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction,
    `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform,
    `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionRelations,
    `OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleAction,
    `OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleTransform,
    `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp,
    `OddMath.QuiverHecke.CyclotomicAction.ELVParameterUntwist,
    `OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleRelations]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited {names.size} declarations in {owner}."
