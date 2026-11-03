import OddMath.QuiverHecke.CyclotomicAction.ELVContentCapRowSquare
import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace ContentCapRowSquareConsumer
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

example (n : ℕ) (i : Bool) := contentMatrixSourceIso_hom_mem D Sc (cut n) n 0 i (M n i)
example (n : ℕ) (i : Bool) := contentMatrixSourceIso_inv_mem D Sc (cut n) n 0 i (M n i)
example (n a : ℕ) (i : Bool) := contentMatrixCapDotRow_square D Sc (cut n) n 0 i (M n i) a
example (a : ℕ) (i : Bool) := contentMatrixCapDotRow_square D Sc (cut 0) 0 0 i (M 0 i) a
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ContentCapRowSquareConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentCapRowSquare
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
