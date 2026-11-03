import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockMatrixRows
import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace ContentBlockMatrixRowsConsumer
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

example (n : ℕ) (i : Bool) := contentBlockMatrixDot_supernatural D Sc (cut n) n (0 + ([i] : Multiset Bool)) i
example (n : ℕ) (i : Bool) (r : ℕ) (b : (M n i).obj (letter n i)) :=
  contentBlockUnitDot_square D Sc (cut n) n (0 + ([i] : Multiset Bool)) i (M n i) (letter n i) r b
example (n : ℕ) (i : Bool) (r : ℕ) (b : (M n i).obj (letter n i)) :=
  contentBlockUnitDotColumn_square D Sc (cut n) n (0 + ([i] : Multiset Bool)) i (M n i) (letter n i) r b
example (i : Bool) (b : (M 0 i).obj (letter 0 i)) :=
  contentBlockUnitDot_square D Sc (cut 0) 0 (0 + ([i] : Multiset Bool)) i (M 0 i) (letter 0 i) 0 b
private def vacuumModule (n : ℕ) := supermoduleParityObj
  ((BalancedInduction.restriction (contentInclusion D Sc (cut n) n 0)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc (cut n) n ((Q n).obj ⟨[]⟩)))
example (n : ℕ) (i : Bool) (r : ℕ) (b : (vacuumModule n).obj (empty n)) :=
  contentBlockUnitDot_square D Sc (cut n) n 0 i (vacuumModule n) (empty n) r b
example (n : ℕ) (i : Bool) (r : ℕ) (b : (vacuumModule n).obj (empty n)) :=
  contentBlockUnitDotColumn_square D Sc (cut n) n 0 i (vacuumModule n) (empty n) r b
private def exterior (n : ℕ) : (⟨[true]⟩ : OldCategory D Sc (cut n)) ⟶ ⟨[true]⟩ :=
  (ideal D Sc (cut n) [true] [true]).mkQ
    (SKM.SYM.elvCoefficientQuotient D (cut n) (SKM.SYM.delta D ℚ ⟨true, rfl⟩) ⊗ₜ[ℚ]
      𝟙 ((pres D Sc).obj (ob D [true])))
example (n : ℕ) (r : ℕ) := contentBlockUnitDot_square D Sc (cut n) n
  (0 + ([true] : Multiset Bool)) true (M n true) (letter n true) r
  ((Q n).map (𝟙 (⟨[true]⟩ : OldCategory D Sc (cut n)) + exterior n))
example (n : ℕ) (r : ℕ) := contentBlockUnitDotColumn_square D Sc (cut n) n
  (0 + ([true] : Multiset Bool)) true (M n true) (letter n true) r
  ((Q n).map (𝟙 (⟨[true]⟩ : OldCategory D Sc (cut n)) + exterior n))
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ContentBlockMatrixRowsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareRows,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockMatrixRows] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
