import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockMatrixCharts
import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace ContentBlockMatrixChartsConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut (n : ℕ) : Bool → ℕ := fun _ => n
private abbrev Q (n : ℕ) := oldTruncateFunctor D Sc (cut n) n
private def M (n : ℕ) (j : Bool) := supermoduleParityObj
  ((BalancedInduction.restriction (contentInclusion D Sc (cut n) n (0 + ([j] : Multiset Bool)))).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc (cut n) n ((Q n).obj ⟨[j]⟩)))
private def empty (n : ℕ) : ContentCategory D Sc (cut n) n 0 := ⟨(Q n).obj ⟨[]⟩, by rfl⟩
private def letter (n : ℕ) (i : Bool) : ContentCategory D Sc (cut n) n (0 + ([i] : Multiset Bool)) :=
  ⟨(Q n).obj ⟨[i]⟩, by rfl⟩

example (n : ℕ) (i : Bool) := contentBlockMatrixSourceIso_hom_mem D Sc (cut n) n i 0 (M n i)
example (n : ℕ) (i : Bool) := contentBlockMatrixSourceIso_inv_mem D Sc (cut n) n i 0 (M n i)
example (n : ℕ) (i : Bool) := contentBlockMatrixTargetIso_hom_mem D Sc (cut n) n i 0 (M n i)
example (n : ℕ) (i : Bool) := contentBlockMatrixTargetIso_inv_mem D Sc (cut n) n i 0 (M n i)
example (n : ℕ) (i : Bool) := contentBlockMatrixValueIso_hom_mem D Sc (cut n) n i 0 (M n i)
example (n : ℕ) (i : Bool) := contentBlockMatrixValueIso_inv_mem D Sc (cut n) n i 0 (M n i)
example (i : Bool) := contentBlockMatrixSourceIso_hom_mem D Sc (cut 0) 0 i 0 (M 0 i)
example (i : Bool) := contentBlockMatrixTargetIso_inv_mem D Sc (cut 0) 0 i 0 (M 0 i)
example (n : ℕ) (i : Bool) := contentBlockMatrixSourceIso_total D Sc (cut n) n i 0 (M n i) (letter n i)
example (n : ℕ) (i : Bool) := contentBlockMatrixTargetIso_total D Sc (cut n) n i 0 (M n i) (letter n i)
example (n : ℕ) (i : Bool) := contentBlockMatrixValueIso_total D Sc (cut n) n i 0 (M n i) (letter n i)
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ContentBlockMatrixChartsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareParity,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockMatrixCharts] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
