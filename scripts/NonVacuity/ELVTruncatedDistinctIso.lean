import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDistinctIso
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace TruncatedDistinctIsoConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut (n : ℕ) : Bool → ℕ := fun _ => n
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide
private def M (n : ℕ) := supermoduleParityObj
  (WeightedAppendFixture.truncatedRepresentable D Sc (cut n) n
    ((oldTruncateFunctor D Sc (cut n) n).obj ⟨[true]⟩))

/-- Both mixed colour orders preserve the prescribed native mate. -/
example (n : ℕ) (i : Bool) := truncatedDistinctModuleIso D Sc (cut n) n i (!i) (distinct i) (M n)
example (n : ℕ) (i : Bool) := truncatedDistinctModuleIso_hom D Sc (cut n) n i (!i) (distinct i) (M n)
example (n : ℕ) (i : Bool) := truncatedDistinctModuleIso_inv_mem D Sc (cut n) n i (!i) (distinct i) (M n)
example (n : ℕ) (i : Bool) := truncatedDistinctFunctorIso D Sc (cut n) n i (!i) (distinct i)
example (n : ℕ) (i : Bool) := truncatedDistinctFunctorIso_hom_total D Sc (cut n) n i (!i) (distinct i) (M n)
example (i : Bool) := truncatedDistinctModuleIso D Sc (cut 0) 0 i (!i) (distinct i) (M 0)

private def oddM (n : ℕ) := supermoduleParityObj
  (WeightedAppendFixture.truncatedRepresentable AsymmetricParameters.datum AsymmetricParameters.scalars
    (cut n) n ((oldTruncateFunctor AsymmetricParameters.datum AsymmetricParameters.scalars (cut n) n).obj ⟨[]⟩))

/-- Distinct odd colours give an odd inverse and both complete functor roundtrips. -/
example (n : ℕ) := truncatedDistinctModuleIso_inv_mem AsymmetricParameters.datum
  AsymmetricParameters.scalars (cut n) n false true (by decide) (oddM n)
example (n : ℕ) := truncatedDistinctFunctorIso_inv_mem AsymmetricParameters.datum
  AsymmetricParameters.scalars (cut n) n false true (by decide)
example (n : ℕ) := (truncatedDistinctFunctorIso AsymmetricParameters.datum
  AsymmetricParameters.scalars (cut n) n false true (by decide)).hom_inv_id
example (n : ℕ) := (truncatedDistinctFunctorIso AsymmetricParameters.datum
  AsymmetricParameters.scalars (cut n) n false true (by decide)).inv_hom_id

/-- Odd input morphisms satisfy the signed inverse naturality equation. -/
example (n : ℕ) := (truncatedDistinctFunctorIso AsymmetricParameters.datum
  AsymmetricParameters.scalars (cut n) n false true (by decide)).inv.naturality 1
    (supermoduleParityIso (oddM n)).hom (supermoduleParityIso_hom_mem (oddM n))
end TruncatedDistinctIsoConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVMixedRectangularMate,
      `OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDistinctIso] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
