import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedMate
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightMixedMateConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide
private def family (x : Bool → ℤ) (v : List Bool) : ELVWeightProduct D Sc cut 8 0 x := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v⟩)))

/-- The selected whole mate exists at four actual weight corners, for both mixed colour orders. -/
example (i : Bool) := elvWeightMixedMate_mem D Sc cut 8 i (!i) 0
  (zero_add (D.α (!i))) (rfl : D.α (!i) + D.α i = D.α (!i) + D.α i)
  (zero_add (D.α i)) (add_comm (D.α i) (D.α (!i)))
example (i : Bool) (p : ZMod 2) := elvWeightMixedMate_app D Sc cut 8 i (!i) 0
  (zero_add (D.α (!i))) (rfl : D.α (!i) + D.α i = D.α (!i) + D.α i)
  (zero_add (D.α i)) (add_comm (D.α i) (D.α (!i))) p (family (D.α (!i)) [!i])

private abbrev x₀ (i : Bool) := -D.α i
private abbrev xj (i : Bool) := -D.α i + D.α (!i)
private theorem h₁ (i : Bool) : x₀ i + D.α (!i) = xj i := rfl
private theorem h₂ (i : Bool) : xj i + D.α i = D.α (!i) := by dsimp [xj]; abel
private theorem h₃ (i : Bool) : x₀ i + D.α i = 0 := by dsimp [x₀]; abel
private theorem h₄ (i : Bool) : (0 : Bool → ℤ) + D.α (!i) = D.α (!i) := zero_add _
private def emptyBlock : WeightBlocks D 0 (0 : Bool → ℤ) := ⟨0, by simp⟩
private theorem absent (i : Bool) : ¬ ∃ β, blockSucc D 0 i (h₃ i) β = emptyBlock := by
  rw [exists_blockSucc_iff]
  simp [emptyBlock]

/-- Both genuine absent coordinates vanish and the given mate is invertible there. -/
example (i : Bool) := elvMixedPredecessor_iff D i (!i) 0 (h₂ i) (h₃ i) (h₄ i) (distinct i) emptyBlock
example (i : Bool) := elvWeightMixedSource_isZero D Sc cut 8 i (!i) 0 (h₁ i) (h₃ i)
  emptyBlock (absent i) (family (xj i) [!i])
example (i : Bool) := elvWeightMixedTarget_isZero D Sc cut 8 i (!i) 0 (h₂ i) (h₃ i) (h₄ i)
  (distinct i) emptyBlock (absent i) (family (xj i) [!i])
example (i : Bool) (p : ZMod 2) := elvWeightMixedMate_absent_isIso D Sc cut 8 i (!i) 0
  (h₁ i) (h₂ i) (h₃ i) (h₄ i) (distinct i) emptyBlock (absent i) p (family (xj i) [!i])

/-- The distinct all-odd crossing gives an odd whole mate. -/
example := elvWeightMixedMate_mem AsymmetricParameters.datum AsymmetricParameters.scalars cut 8 false true 0
  (zero_add _) (rfl : AsymmetricParameters.datum.α true + AsymmetricParameters.datum.α false = _)
  (zero_add _) (add_comm _ _)
end WeightMixedMateConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVPiSCatRectangularMate,
      `OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedMate] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
