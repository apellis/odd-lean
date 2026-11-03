import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMatrixHeight
import Lean.Util.CollectAxioms

noncomputable section
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ELVWeightMatrixHeight
private def collisionDatum : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else -2
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -2)
    split
    · exact ⟨1, by norm_num⟩
    · exact ⟨-1, by norm_num⟩

private abbrev D := collisionDatum
private def cutoff (_ : Bool) : ℕ := 3
private def Λ : Bool → ℤ := fun _ => 3
private def x : Bool → ℤ := -Λ
private def vacuum : WeightBlocks D Λ x := ⟨0, by simp [blockWeight, x]⟩
private def occupied : WeightBlocks D Λ x := ⟨[false, true], by
  ext b
  cases b <;> norm_num [blockWeight, collisionDatum, SKM.Datum.α, x, Λ]⟩

-- A dependent-root fibre contains contents of different cardinalities.
example : vacuum ≠ occupied := by
  intro h
  have hc := congrArg (fun β => β.1.card) h
  change (0 : ℕ) = 2 at hc
  omega

example (i : Bool) : contentCrossingHeight D cutoff i vacuum.1 =
    contentCrossingHeight D cutoff i occupied.1 :=
  contentCrossingHeight_eq_of_weightBlock D cutoff i Λ x vacuum occupied

example (i : Bool) (β : WeightBlocks D Λ x) :
    contentCrossingHeight D cutoff i β.1 = 3 := by
  have h := contentCrossingHeight_eq_neg_weight D cutoff i Λ x (by rfl) β
  simpa [SKM.Datum.h, collisionDatum, x, Λ] using h

example (i : Bool) (β : WeightBlocks D Λ x) :
    contentUnitCount D cutoff i β.1 = 3 := by
  have h := contentUnitCount_weightBlock D cutoff i Λ x (by rfl) β
  simpa [SKM.Datum.h, collisionDatum, x, Λ] using h

example (i : Bool) (β : WeightBlocks D Λ x) :
    contentCapCount D cutoff i β.1 = 0 := by
  have h := contentCapCount_weightBlock D cutoff i Λ x (by rfl) β
  simpa [SKM.Datum.h, collisionDatum, x, Λ] using h
end NonVacuity.ELVWeightMatrixHeight

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightMatrixHeight
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
