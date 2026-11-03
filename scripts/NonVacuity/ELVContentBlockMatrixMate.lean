import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockMatrixMate
import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace ContentBlockMatrixMateConsumer
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

private abbrev J (n : ℕ) (i : Bool) := contentAppendTo D Sc (cut n) n 0 [i]
  (0 + ([i] : Multiset Bool)) (contentBlockCanonicalSum 0 [i])
private abbrev K (n : ℕ) (i : Bool) := contentAppendTo D Sc (cut n) n (0 + ([i] : Multiset Bool)) [i]
  ((0 + ([i] : Multiset Bool)) + ([i] : Multiset Bool))
  (contentBlockCanonicalSum (0 + ([i] : Multiset Bool)) [i])
private abbrev T (n : ℕ) (i : Bool) := truncatedAppend D Sc (cut n) n [i]
example (n : ℕ) (i : Bool) := BalancedInduction.rectangularMate_negative_eq_grid (J n i) (K n i)
  (contentBlockDistinctCross_supernatural D Sc (cut n) n 0 i i) (M n i) (letter n i)
example (n : ℕ) (i : Bool) := mixedMate_negative_eq_ordered (T n i)
  (truncatedEqualCross_supernatural D Sc (cut n) n i)
  (BalancedInduction.induced (contentInclusion D Sc (cut n) n (0 + ([i] : Multiset Bool))) (M n i))
  ((Q n).obj ⟨[i]⟩)
example (n : ℕ) (i : Bool) := contentBlockMatrixCross_supernatural D Sc (cut n) n 0 i
example (n : ℕ) (i : Bool) := BalancedInduction.gridMateLinear_degree_eq (J n i) (K n i)
  (contentBlockDistinctCross_supernatural D Sc (cut n) n 0 i i)
  (SKM.zmod2_mul_self (D.parity i)) (contentBlockMatrixCross_supernatural D Sc (cut n) n 0 i)
  (M n i) (letter n i)
example (n : ℕ) (i : Bool) := contentBlockMatrixMate_square D Sc (cut n) n 0 i (M n i) (letter n i)
example (i : Bool) := contentBlockMatrixMate_square D Sc (cut 0) 0 0 i (M 0 i) (letter 0 i)
private def exterior (n : ℕ) : (⟨[true]⟩ : OldCategory D Sc (cut n)) ⟶ ⟨[true]⟩ :=
  (ideal D Sc (cut n) [true] [true]).mkQ
    (SKM.SYM.elvCoefficientQuotient D (cut n) (SKM.SYM.delta D ℚ ⟨true, rfl⟩) ⊗ₜ[ℚ]
      𝟙 ((pres D Sc).obj (ob D [true])))
example (n : ℕ) := LinearMap.congr_fun
  (contentBlockMatrixMate_square D Sc (cut n) n 0 true (M n true) (letter n true))
  (BalancedInduction.tensor (J n true) ((BalancedInduction.restriction (J n true)).obj (M n true)).toFunctor
    (empty n) (𝟙 ((Q n).obj ⟨[true]⟩))
    ((Q n).map (𝟙 (⟨[true]⟩ : OldCategory D Sc (cut n)) + exterior n)))
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ContentBlockMatrixMateConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVInductionSignedMate,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockMatrixMate] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
