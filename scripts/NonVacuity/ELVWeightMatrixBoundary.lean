import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMatrixBoundary
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightMatrixBoundaryConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private def Λ : Bool → ℤ := fun _ => 8
private theorem hcutoff (i : Bool) : (cut i : ℤ) = D.h i Λ := rfl
private def word (i : Bool) : TruncatedCategory D Sc cut 8 :=
  (oldTruncateFunctor D Sc cut 8).obj ⟨[!i]⟩
private def M (i : Bool) := supermoduleParityObj (WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (word i))
private theorem missing (i : Bool) : i ∉ ([!i] : Multiset Bool) := by cases i <;> simp

/-- Only the lower E/F coordinate vanishes, for both moving parities at a nonempty output. -/
example (i : Bool) := truncatedIndRes_subsingleton_of_not_mem D Sc cut 8 i (M i) (word i) (missing i)
example (i : Bool) := truncatedIndRes_restriction_isZero D Sc cut 8 i ([!i] : Multiset Bool) (missing i) (M i)
private def negativeBlock (i : Bool) : WeightBlocks D Λ (D.α (!i) - Λ) := ⟨[!i], by simp⟩
private theorem step (i : Bool) : (D.α (!i) - Λ - D.α i) + D.α i = D.α (!i) - Λ := by abel
private theorem absent (i : Bool) : ¬ ∃ β, blockSucc D Λ i (step i) β = negativeBlock i := by
  rw [exists_blockSucc_iff]
  exact missing i
example (i : Bool) := elvWeightHeight_nonpos_of_absent D cut i Λ (step i) (hcutoff i)
  (negativeBlock i) (absent i)

/-- The genuine empty output is included at positive cutoff. -/
private def emptyBlock : WeightBlocks D Λ (-Λ) := ⟨0, by simp⟩
private theorem emptyStep (i : Bool) : (-Λ - D.α i) + D.α i = -Λ := by abel
example (i : Bool) := elvWeightHeight_nonpos_of_absent D cut i Λ (emptyStep i) (hcutoff i)
  emptyBlock (by rw [exists_blockSucc_iff]; simp [emptyBlock])

/-- Positive categorical height forces the actual predecessor, independently of the truncation bound. -/
private def positiveBlock (i : Bool) : WeightBlocks D 0 (D.α i) := ⟨{i}, by simp⟩
private theorem hpos (i : Bool) : 0 < D.h i (D.α i) := by
  change 0 < D.cd.coroot i (D.cd.root i)
  rw [D.cd.coroot_root_self]
  norm_num
example (i : Bool) := elvWeightPredecessor_of_positive_height D (fun _ => 0) i 0
  (zero_add (D.α i)) (by simp) (hpos i) (positiveBlock i)
end WeightMatrixBoundaryConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightMatrixBoundary
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
