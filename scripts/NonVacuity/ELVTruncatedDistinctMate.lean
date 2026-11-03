import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDistinctMate
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open CyclotomicCrossingTensor
namespace TruncatedDistinctMateConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut (n : ℕ) : Bool → ℕ := fun _ => n
private abbrev Q (n : ℕ) := oldTruncateFunctor D Sc (cut n) n
private def M (n : ℕ) : Superfunctor ℚ (TruncatedCategory D Sc (cut n) n) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc (cut n) n ((Q n).obj ⟨[true]⟩)
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide

/-- Both orders of the mixed colours use the prescribed positive crossing. -/
example (n : ℕ) (i : Bool) (w : OldCategory D Sc (cut n)) :=
  truncatedDistinctMateEquivAtOld_hom D Sc (cut n) n i (!i) (M n) (distinct i) w
example (n : ℕ) (i : Bool) (w : TruncatedCategory D Sc (cut n) n) :=
  truncatedDistinctMate_bijective D Sc (cut n) n i (!i) (M n) (distinct i) w
example (n : ℕ) (i : Bool) (w : OldCategory D Sc (cut n)) :=
  LinearEquiv.apply_symm_apply
    (truncatedDistinctMateEquivAtOld D Sc (cut n) n i (!i) (M n) (distinct i) w)
example (n : ℕ) (i : Bool) (w : OldCategory D Sc (cut n)) :=
  LinearEquiv.symm_apply_apply
    (truncatedDistinctMateEquivAtOld D Sc (cut n) n i (!i) (M n) (distinct i) w)
example (n : ℕ) (i : Bool) (w : OldCategory D Sc (cut n)) :=
  truncatedDistinctMateLinear_square D Sc (cut n) n i (!i) (M n) w

private def exterior (n : ℕ) : (⟨[true]⟩ : OldCategory D Sc (cut n)) ⟶ ⟨[true]⟩ :=
  (ideal D Sc (cut n) [true] [true]).mkQ
    (SKM.SYM.elvCoefficientQuotient D (cut n) (SKM.SYM.delta D ℚ ⟨true, rfl⟩) ⊗ₜ[ℚ]
      𝟙 ((pres D Sc).obj (ob D [true])))

/-- Odd exterior input and its inhomogeneous identity sum survive the decoder roundtrip. -/
example (n : ℕ) :=
  LinearEquiv.symm_apply_apply
    (truncatedDistinctMateEquivAtOld D Sc (cut n) n false true (M n) (by decide) ⟨[false]⟩)
    (BalancedInduction.tensor (truncatedAppend D Sc (cut n) n [false])
      ((truncatedAppend D Sc (cut n) n [true]) ⋙ (M n).toFunctor)
      ((Q n).obj ⟨[]⟩) (𝟙 ((Q n).obj ⟨[false]⟩))
      ((Q n).map (𝟙 (⟨[true]⟩ : OldCategory D Sc (cut n)) + exterior n)))

/-- The empty output and zero cutoff are retained. -/
example := truncatedDistinctMate_bijective D Sc (cut 0) 0 false true (M 0) (by decide)
  ((Q 0).obj ⟨[]⟩)

private def oddM (n : ℕ) := WeightedAppendFixture.truncatedRepresentable
  AsymmetricParameters.datum AsymmetricParameters.scalars (cut n) n
    ((oldTruncateFunctor AsymmetricParameters.datum AsymmetricParameters.scalars (cut n) n).obj ⟨[]⟩)
/-- Distinct odd colours test crossing degree one. -/
example : AsymmetricParameters.datum.parity false * AsymmetricParameters.datum.parity true = 1 := by decide
example (n : ℕ) := truncatedDistinctMateEquivAtOld_hom
  AsymmetricParameters.datum AsymmetricParameters.scalars (cut n) n false true (oddM n) (by decide) ⟨[]⟩
example (n : ℕ) := truncatedDistinctMate_bijective
  AsymmetricParameters.datum AsymmetricParameters.scalars (cut n) n false true (oddM n) (by decide)
    ((oldTruncateFunctor AsymmetricParameters.datum AsymmetricParameters.scalars (cut n) n).obj ⟨[]⟩)
end TruncatedDistinctMateConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedMixedCross,
      `OddMath.QuiverHecke.CyclotomicAction.ELVRestrictionCoendCoordinates,
      `OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDistinctMate] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
