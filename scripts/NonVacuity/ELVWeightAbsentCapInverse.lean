import OddMath.QuiverHecke.CyclotomicAction.ELVWeightAbsentCapInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace WeightAbsentCapInverseConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 0
private theorem lower (i : Bool) : -D.α i + D.α i = (0 : Bool → ℤ) := neg_add_cancel _
private theorem upper (i : Bool) : (0 : Bool → ℤ) + D.α i = D.α i := zero_add _
private def emptyBlock : WeightBlocks D 0 0 := ⟨0, by simp⟩
private theorem cutoff (i : Bool) : (cut i : ℤ) = D.h i 0 := (D.cd.coroot i).map_zero.symm
private theorem height (i : Bool) : 0 ≤ D.h i (0 : Bool → ℤ) := by
  simp [SKM.Datum.h]
private theorem absent (i : Bool) :
    ¬ ∃ β, blockSucc D 0 i (lower i) β = emptyBlock := by
  intro h
  have hi := (exists_blockSucc_iff D 0 i (lower i) emptyBlock).mp h
  simp [emptyBlock] at hi
private def M : ELVWeightProduct D Sc cut 8 0 0 := fun δ =>
  (BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨[]⟩))
private def shifted : ELVWeightProduct D Sc cut 8 0 0 := fun δ => supermoduleParityObj (M δ)
private def oddInput : shifted ⟶ M := fun δ => (supermoduleParityIso (M δ)).hom
private theorem oddInput_mem : oddInput ∈ parity (R := ℚ) _ _ 1 := fun δ =>
  supermoduleParityIso_hom_mem (M δ)
/-- Both moving parities retain the prescribed cap inverse at the derived zero-height boundary. -/
example (i : Bool) := (Classical.choice
  (elvWeightAbsentCapInverse_nonempty D Sc cut 8 i 0 (lower i) (upper i)
    emptyBlock (cutoff i) (absent i) (height i) shifted)).total
example (i : Bool) := (Classical.choice
  (elvWeightAbsentCapInverse_nonempty D Sc cut 8 i 0 (lower i) (upper i)
    emptyBlock (cutoff i) (absent i) (height i) shifted)).ff
example (i : Bool) (n : ℕ) := (Classical.choice
  (elvWeightAbsentCapInverse_nonempty D Sc cut 8 i 0 (lower i) (upper i)
    emptyBlock (cutoff i) (absent i) (height i) shifted)).g'_mem n
/-- Whole inverse families retain signed naturality against a concrete odd input map. -/
example (i : Bool) := (Classical.choice
  (elvWeightAbsentCapFamily_nonempty D Sc cut 8 i 0 (lower i) (upper i)
    emptyBlock (cutoff i) (absent i) (height i))).total
example (i : Bool) := (Classical.choice
  (elvWeightAbsentCapFamily_nonempty D Sc cut 8 i 0 (lower i) (upper i)
    emptyBlock (cutoff i) (absent i) (height i))).ff
example (i : Bool) := ((Classical.choice
  (elvWeightAbsentCapFamily_nonempty D Sc cut 8 i 0 (lower i) (upper i)
    emptyBlock (cutoff i) (absent i) (height i))).f').naturality (D.parity i) oddInput oddInput_mem
example (i : Bool) (n : ℕ) := ((Classical.choice
  (elvWeightAbsentCapFamily_nonempty D Sc cut 8 i 0 (lower i) (upper i)
    emptyBlock (cutoff i) (absent i) (height i))).g' n).naturality (n • D.parity i) oddInput oddInput_mem
end WeightAbsentCapInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightAbsentCapInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
