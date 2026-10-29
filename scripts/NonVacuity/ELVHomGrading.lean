import OddMath.QuiverHecke.CyclotomicAction.ELVHomGrading
import NonVacuity.ELVCoefficientGrading
import Lean.Util.CollectAxioms

noncomputable section
namespace ELVHomGradingConsumer
open OddMath OddMath.QuiverHecke ELVCoefficientCategoryConsumer ELVCoefficientGradingConsumer

theorem homogeneous : scalars.Homogeneous := by
  intro i j p q _ _ _ _ h
  exact False.elim (h rfl)

example : StringDiagrams.GradedSupercategory ℚ
    (ELVCoefficientCategory datum scalars (fun _ => 2)) :=
  elvHomGrading datum sy scalars homogeneous (fun _ => 2)

example : ELVOld.relation datum scalars (fun _ => 2) () [] ∈
    elvHomDegree datum sy scalars homogeneous (fun _ => 2) [()] [()] 4 :=
  ELVOld.relation_mem_degree datum sy scalars homogeneous (fun _ => 2) () []

example : ELVOld.relation datum scalars (fun _ => 3) () [] ∈
    elvHomDegree datum sy scalars homogeneous (fun _ => 3) [()] [()] 6 :=
  ELVOld.relation_mem_degree datum sy scalars homogeneous (fun _ => 3) () []

example (v w : List Unit) :
    DirectSum.IsInternal (elvHomDegree datum sy scalars homogeneous (fun _ => 2) v w) :=
  elvHomDegree_internal datum sy scalars homogeneous (fun _ => 2) v w

example : SKM.SYM.elvCoefficientQuotient datum (fun _ => 2) delta ≠ 0 :=
  quotient_delta_ne_zero 2 (by decide)

end ELVHomGradingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners := #[`OddMath.SKM.BubbleELVPolynomialGrading,
    `OddMath.QuiverHecke.CyclotomicAction.ELVHomGrading]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if owners.contains moduleNames[idx.toNat]! then
        for ax in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations audited"
  logInfo m!"Audited {count} declarations in the two ELV grading modules."
