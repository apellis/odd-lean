import OddMath.QuiverHecke.CyclotomicAction.ELVPrependCrossTail
import NonVacuity.ELVPrependOldExtraction
import Lean.Util.CollectAxioms

noncomputable section
namespace ELVPrependCrossTailConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open ELVOld ELVPrependConsumer ELVPrependOldExtractionConsumer
open scoped TensorProduct

/-- A different moving exponent, with the same old strand and shuffle. -/
def otherIndex : PrependIdx () [()] [(), ()] :=
  ⟨(2, movingIndex.val.2), movingIndex.property⟩

theorem tails_differ : movingIndex.tailKey ≠ otherIndex.tailKey := by
  intro h
  have hn := congrArg Prod.fst h
  norm_num [PrependIdx.tailKey, movingIndex, otherIndex] at hn

/-- Inhomogeneous exterior coefficients do not leak into another moving exponent. -/
example := prependExtractOld_insert_off_tail datum scalars (fun _ => 3)
  1 movingIndex otherIndex tails_differ oldCoefficient

example := prependExtractOldQuotient_insert_off_tail datum scalars (fun _ => 3)
  1 movingIndex otherIndex tails_differ oldCoefficient

example : PrependIdx.regroupEquiv.symm (PrependIdx.regroupEquiv movingIndex) = movingIndex :=
  PrependIdx.regroupEquiv.symm_apply_apply movingIndex

example (q : Σ t : PrependIdx.Tail () [()] [(), ()], NFIdx [()] t.representative.oldTarget) :
    PrependIdx.regroupEquiv (PrependIdx.regroupEquiv.symm q) = q :=
  PrependIdx.regroupEquiv.apply_symm_apply q

#print axioms PrependIdx.regroupEquiv
#print axioms prependExtractOld_insert_off_tail
#print axioms prependExtractOldQuotient_insert_off_tail
end ELVPrependCrossTailConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVPrependCrossTail
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Cross-tail module was not imported"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    count := count + 1
  if count == 0 then throwError "Empty cross-tail declaration inventory"
  logInfo m!"Audited {count} owned cross-tail declarations; all axioms allowed."
