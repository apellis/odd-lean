import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairInduction
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightPairExamples
private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private abbrev X := Bool → ℤ
private def vacuumBlock : WeightBlocks D (0 : X) 0 := ⟨0, by simp⟩
private theorem firstStep : (0 : X) + D.α false = D.α false := zero_add _
private theorem secondStep : D.α false + D.α true = D.α false + D.α true := rfl

private def sourceVacuum : ELVWeightProduct D Sc (fun _ => 12) 12 (0 : X) 0 :=
  fun β => if hb : β.1 = 0 then
    (by rw [hb]; exact vacuumModule D Sc (fun _ => 12) 12)
  else elvZeroModule D Sc (fun _ => 12) 12 β.1

/-- A genuine supported coordinate of the actual product induction on the
actual vacuum family, not a replacement supported-sector model. -/
example := Functor.congr_obj
  (elvEFunctor_comp₂_blockSucc D Sc (fun _ => 12) 12 true false (0 : X)
    firstStep secondStep vacuumBlock) sourceVacuum

example := elvBlockPairComparison_mem D (parameterTwist D Sc) (fun _ => 12) 12
  true false (0 : X) firstStep secondStep vacuumBlock
  (vacuumModule D (parameterTwist D Sc) (fun _ => 12) 12)

private theorem innerMissingStep : -D.α false + D.α false = (0 : X) := neg_add_cancel _
private theorem outerPresentStep : (0 : X) + D.α true = D.α true := zero_add _
private abbrev oneBlock := blockSucc D (0 : X) true outerPresentStep vacuumBlock

private theorem innerMissing : ¬ ∃ β,
    blockSucc₂ D true false (0 : X) innerMissingStep outerPresentStep β = oneBlock := by
  intro ⟨β, hβ⟩
  have he : blockSucc D (0 : X) false innerMissingStep β = vacuumBlock :=
    blockSucc_injective D (0 : X) true outerPresentStep hβ
  have hm : false ∈ vacuumBlock.1 :=
    (exists_blockSucc_iff D (0 : X) false innerMissingStep vacuumBlock).mp ⟨β, he⟩
  simpa [vacuumBlock] using hm

/-- The outer predecessor exists, but the inner predecessor does not. -/
example := elvEFunctor_comp₂_isZero D Sc (fun _ => 12) 12 true false (0 : X)
  innerMissingStep outerPresentStep oneBlock innerMissing
  (fun β => elvZeroModule D Sc (fun _ => 12) 12 β.1)

private theorem outerMissingStep : -D.α true + D.α true = (0 : X) := neg_add_cancel _
private theorem earlierStep : -(D.α true + D.α false) + D.α false = -D.α true := by abel
private theorem outerMissing : ¬ ∃ β,
    blockSucc₂ D true false (0 : X) earlierStep outerMissingStep β = vacuumBlock := by
  intro ⟨β, hβ⟩
  have hm : true ∈ vacuumBlock.1 :=
    (exists_blockSucc_iff D (0 : X) true outerMissingStep vacuumBlock).mp
      ⟨blockSucc D (0 : X) false earlierStep β, hβ⟩
  simpa [vacuumBlock] using hm

/-- The outer predecessor itself is absent. -/
example := elvEFunctor_comp₂_isZero D Sc (fun _ => 12) 12 true false (0 : X)
  earlierStep outerMissingStep vacuumBlock outerMissing
  (fun β => elvZeroModule D Sc (fun _ => 12) 12 β.1)
end OddMath.QuiverHecke.ELVWeightPairExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairInduction
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
