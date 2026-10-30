import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import NonVacuity.ELVHomGrading
import Lean.Util.CollectAxioms

noncomputable section
namespace ELVTruncatedDetectionConsumer
open OddMath OddMath.QuiverHecke ELVOld
open ELVCoefficientCategoryConsumer ELVCoefficientGradingConsumer ELVHomGradingConsumer

/-- The odd coefficient survives in positive content, not just in the coefficient ring. -/
theorem delta_survives :
    truncatedSingle datum scalars (fun _ => 2) 3 () delta 0 ≠ 0 :=
  truncatedSingle_delta_ne_zero datum scalars rfl

example : truncatedSingleEval datum scalars rfl
    (truncatedSingle datum scalars (fun _ => 2) 3 () delta 0) =
      ExteriorAlgebra.ι ℚ (Finsupp.single oddColour 1) :=
  truncatedSingleEval_delta datum scalars rfl

example {f : hom datum scalars (fun _ => 2) [()] [()]}
    (hf : f ∈ ideal datum scalars (fun _ => 2) [()] [()]) :
    singleEval datum scalars f = 0 := singleEval_ideal datum scalars rfl hf

example {f : hom datum scalars (fun _ => 2) [()] [()]}
    (hf : f ∈ coefficientHomIdeal datum scalars (fun _ => 2) 3 [()] [()]) :
    singleEval datum scalars f = 0 := singleEval_coefficientIdeal datum scalars hf

/-- The previously proved support bound applies to this nonzero quotient. -/
example : truncatedDegree datum scalars (fun _ => 2) sy homogeneous 3 [()] [()] 9 = ⊥ := by
  apply truncatedSingle_degree_eq_bot datum scalars (fun _ => 2) sy homogeneous 3 () 2
  · norm_num
  · exact SKM.SYM.coefficientDegree_le_weight_mul datum sy 2 (by intro i; norm_num [sy])
  · norm_num [sy]

end ELVTruncatedDetectionConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if owners.contains moduleNames[idx.toNat]! then
        for ax in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations audited"
  for ax in ← Lean.collectAxioms `ELVTruncatedDetectionConsumer.delta_survives do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Disallowed axiom {ax} in the nonzero witness"
  logInfo m!"Audited {count} declarations owned by ELVTruncatedDetection and the nonzero witness; all transitive axioms allowed."
