import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirAbsentClosure
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ReservoirAbsentClosure
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def cut (_ : Bool) : ℕ := 0
private def emptyBlock : WeightBlocks D 0 0 := ⟨0, by simp⟩
private theorem lower (i : Bool) : -D.α i + D.α i = (0 : Bool → ℤ) := neg_add_cancel _
private theorem upper (i : Bool) : (0 : Bool → ℤ) + D.α i = D.α i := zero_add _
private theorem cut_match (i : Bool) : (cut i : ℤ) = D.h i 0 := (D.cd.coroot i).map_zero.symm
private theorem absent (i : Bool) :
    ¬ ∃ β, blockSucc D 0 i (lower i) β = emptyBlock := by
  rw [exists_blockSucc_iff]
  simp [emptyBlock]
private theorem height (i : Bool) : D.h i (0 : Bool → ℤ) = 0 := (D.cd.coroot i).map_zero

-- Both moving parities and both chosen inverse orientations at height zero.
example (i : Bool) (r s : ℕ) (M : ELVWeightProduct D Sc cut 3 0 0) :
    (ReservoirClosures.positive D Sc cut 3 0 cut_match i (lower i) (upper i)
      (by rw [height]) r s).total M emptyBlock = 0 :=
  ReservoirClosures.positive_total_absent D Sc cut 3 0 cut_match i (lower i) (upper i)
    emptyBlock (absent i) (by rw [height]) r s M
example (i : Bool) (r s : ℕ) (M : ELVWeightProduct D Sc cut 3 0 0) :
    (ReservoirClosures.negative D Sc cut 3 0 cut_match i (lower i) (upper i)
      (by rw [height]) r s).total M emptyBlock = 0 :=
  ReservoirClosures.negative_total_absent D Sc cut 3 0 cut_match i (lower i) (upper i)
    emptyBlock (absent i) (by rw [height]) r s M

-- An occupied other-colour content at strictly negative categorical height.
private def highest (i j : Bool) : ℤ := if j = i then 0 else 1
private def cutoff (i j : Bool) : ℕ := if j = i then 0 else 1
private def middle (i : Bool) : Bool → ℤ := D.α (!i) - highest i
private theorem cutoff_match (i j : Bool) : (cutoff i j : ℤ) = D.h j (highest i) := by
  cases i <;> cases j <;> rfl
private def otherBlock (i : Bool) : WeightBlocks D (highest i) (middle i) :=
  ⟨{!i}, by simp [middle]⟩
private theorem other_lower (i : Bool) : middle i - D.α i + D.α i = middle i := sub_add_cancel _ _
private theorem other_upper (i : Bool) : middle i + D.α i = middle i + D.α i := rfl
private theorem other_absent (i : Bool) :
    ¬ ∃ β, blockSucc D (highest i) i (other_lower i) β = otherBlock i := by
  rw [exists_blockSucc_iff]
  cases i <;> simp [otherBlock]
private theorem other_height (i : Bool) : D.h i (middle i) ≤ 0 := by
  cases i <;> norm_num [SKM.Datum.h, SKM.Datum.α, middle, highest, D,
    WeightedAppendFixture.datum, CyclotomicAction.AsymmetricParameters.datum]
example : D.h false (middle false) = -2 := rfl
example : D.h true (middle true) = -4 := rfl
private def represented (i : Bool) : ELVWeightProduct D Sc (cutoff i) 3 (highest i) (middle i) :=
  fun δ => contentRepresentable D Sc (cutoff i) 3 δ.1 ⟨⟨δ.1.toList⟩, by simp⟩
example (i : Bool) (r s : ℕ) :
    (ReservoirClosures.negative D Sc (cutoff i) 3 (highest i) (cutoff_match i) i
      (other_lower i) (other_upper i) (other_height i) r s).total (represented i) (otherBlock i) = 0 :=
  ReservoirClosures.negative_total_absent D Sc (cutoff i) 3 (highest i) (cutoff_match i) i
    (other_lower i) (other_upper i) (otherBlock i) (other_absent i) (other_height i) r s (represented i)
end NonVacuity.ReservoirAbsentClosure

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVReservoirAbsentClosure
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
