import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTruncation
import NonVacuity.ELVHomGrading
import Lean.Util.CollectAxioms

noncomputable section
namespace ELVCoefficientTruncationConsumer
open OddMath OddMath.QuiverHecke ELVOld
open ELVCoefficientCategoryConsumer ELVCoefficientGradingConsumer ELVHomGradingConsumer

/-- A rational odd one-strand corner with cutoff two and coefficient cutoff three. -/
example : truncatedDegree datum scalars (fun _ => 2) sy homogeneous 3 [()] [()] 9 = ⊥ := by
  apply truncatedSingle_degree_eq_bot datum scalars (fun _ => 2) sy homogeneous 3 () 2
  · norm_num
  · exact SKM.SYM.coefficientDegree_le_weight_mul datum sy 2 (by intro i; norm_num [sy])
  · norm_num [sy]

example : DirectSum.IsInternal
    (truncatedDegree datum scalars (fun _ => 2) sy homogeneous 3 [()] [()]) :=
  truncatedDegree_internal datum scalars (fun _ => 2) sy homogeneous 3 [()] [()]

example : DirectSum.IsInternal (truncatedParity datum scalars (fun _ => 2) 3 [()] [()]) :=
  truncatedParity_internal datum scalars (fun _ => 2) 3 [()] [()]

example : Function.Surjective (truncateOld datum scalars (fun _ => 2) 3 [()] [()]) :=
  truncateOld_surjective datum scalars (fun _ => 2) 3 [()] [()]

example (z : TruncatedOld datum scalars (fun _ => 0) 3 [()] [()]) : z = 0 :=
  truncatedSingle_eq_zero_of_cutoff_zero datum scalars (fun _ => 0) 3 () rfl z

example (a b : SKM.SYM datum ℚ)
    (h : SKM.SYM.truncatedELVCoefficientQuotient datum (fun _ => 2) 3 a =
      SKM.SYM.truncatedELVCoefficientQuotient datum (fun _ => 2) 3 b) :
    truncatedSingle datum scalars (fun _ => 2) 3 () a 1 =
      truncatedSingle datum scalars (fun _ => 2) 3 () b 1 :=
  truncatedSingle_eq_of_coefficient_eq datum scalars (fun _ => 2) 3 () 1 a b h

example (z : TruncatedOld datum scalars (fun _ => 2) 3 [()] [()]) :
    truncatedProj datum scalars (fun _ => 2) 3 [()] [()] 1
      (truncatedDproj datum scalars (fun _ => 2) sy homogeneous 3 [()] [()] 2 z) =
    truncatedDproj datum scalars (fun _ => 2) sy homogeneous 3 [()] [()] 2
      (truncatedProj datum scalars (fun _ => 2) 3 [()] [()] 1 z) :=
  truncatedProj_truncatedDproj datum scalars (fun _ => 2) sy homogeneous 3 1 2 [()] [()] z

/-- This control is only in the coefficient ring; it does not assert survival in `TruncatedOld`. -/
example : SKM.SYM.truncatedELVCoefficientQuotient datum (fun _ => 2) 3 delta ≠ 0 :=
  truncated_delta_ne_zero

end ELVCoefficientTruncationConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTruncation]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if owners.contains moduleNames[idx.toNat]! then
        for ax in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations audited"
  logInfo m!"Audited {count} declarations owned by ELVCoefficientTruncation; all transitive axioms allowed."
