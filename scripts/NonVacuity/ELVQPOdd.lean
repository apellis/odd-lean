import OddMath.QuiverHecke.CyclotomicAction.ELVQPOdd
import NonVacuity.ELVPrefixKilling

noncomputable section
namespace ELVQPOddConsumer
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld
open ELVPrefixKillingConsumer
open scoped TensorProduct

/-- Odd prefix parity and nonempty spectators, at every cutoff. -/
example (N : ℕ) := qp_repeated_odd (datum 1) (scalars 1) (fun _ => N) () rfl
  [()] [()] [(), (), (), ()] (𝟙 _)

/-- Empty prefix is a two-strand cancellation, not cancellation on the empty old word. -/
example := qp_repeated_odd (datum 1) (scalars 1) (fun _ => 0) () rfl
  [] [] [(), ()] (𝟙 _)

/-- Even prefix parity and positive even cutoff retain the top coefficient relation. -/
example := qp_repeated_odd (datum 1) (scalars 1) (fun _ => 2) () rfl
  [(), ()] [] [(), (), (), ()] (𝟙 _)

/-- Arbitrary full-coefficient continuation, without a homogeneity assumption. -/
example (N : ℕ)
    (h : hom (datum 1) (scalars 1) (fun _ => N) [(), (), ()] [(), (), ()]) :=
  qp_repeated_odd (datum 1) (scalars 1) (fun _ => N) () rfl [()] [] [(), (), ()] h

/-- Mixed exterior-plus-scalar continuation. -/
example := qp_repeated_odd (datum 1) (scalars 1) (fun _ => 3) () rfl [] [] [(), ()]
  (((1 : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) (datum 1) (fun _ => 3)) +
      SKM.SYM.elvCoefficientQuotient (datum 1) (fun _ => 3)
        (SKM.SYM.delta (datum 1) ℚ ⟨(), rfl⟩)) ⊗ₜ[ℚ]
    (𝟙 ((pres (datum 1) (scalars 1)).obj (ob (datum 1) [(), ()]))))

#print axioms qp_repeated_odd
#print axioms movingDot_insert
#print axioms qpEval_source_difference_zero
end ELVQPOddConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVQPOdd
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    count := count + 1
  if count == 0 then throwError "Empty declaration inventory: {owner}"
  logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
