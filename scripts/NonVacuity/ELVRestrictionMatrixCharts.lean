import OddMath.QuiverHecke.CyclotomicAction.ELVRestrictionMatrixCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockMatrixMate
import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace RestrictionMatrixChartsConsumer
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

private abbrev Inc (n : ℕ) (i : Bool) := contentInclusion D Sc (cut n) n (0 + ([i] : Multiset Bool))
private abbrev P (n : ℕ) (i : Bool) := BalancedInduction.induced (Inc n i) (M n i)
private theorem value_mem (n : ℕ) (i : Bool) :
    (contentExtensionUnitIso D Sc (cut n) n (0 + ([i] : Multiset Bool)) (M n i)).hom ∈
      parity (R := ℚ) _ _ 0 := by
  rw [contentExtensionUnitIso, BalancedInduction.fullyFaithfulUnitIso_hom]
  exact BalancedInduction.adjunctionUnit_mem (Inc n i) (M n i)

example (n m : ℕ) (i : Bool) := BalancedInduction.restrictionProductIso (Inc n i)
  (fun _ : Option (Fin m) => P n i)
example (n m : ℕ) (i : Bool) := BalancedInduction.restrictionFamilyIso (Inc n i)
  (fun _ : Option (Fin m) => M n i) (fun _ => P n i)
  (fun _ => contentExtensionUnitIso D Sc (cut n) n (0 + ([i] : Multiset Bool)) (M n i))
example (n m : ℕ) (i : Bool) := BalancedInduction.restrictionFamilyIso_hom_mem (Inc n i)
  (fun _ : Option (Fin m) => M n i) (fun _ => P n i)
  (fun _ => contentExtensionUnitIso D Sc (cut n) n (0 + ([i] : Multiset Bool)) (M n i))
  (fun _ => value_mem n i)
example (n m : ℕ) (i : Bool) := BalancedInduction.restrictionFamilyIso_total_apply (Inc n i)
  (fun _ : Option (Fin m) => M n i) (fun _ => P n i)
  (fun _ => contentExtensionUnitIso D Sc (cut n) n (0 + ([i] : Multiset Bool)) (M n i)) (letter n i)
example (n : ℕ) (i : Bool) (q : ZMod 2) := BalancedInduction.shiftedRestrictionChart (Inc n i)
  (M n i) (P n i) (contentExtensionUnitIso D Sc (cut n) n (0 + ([i] : Multiset Bool)) (M n i)) q
example (n : ℕ) (i : Bool) (q : ZMod 2) := BalancedInduction.shiftedRestrictionChart_hom_mem (Inc n i)
  (M n i) (P n i) (contentExtensionUnitIso D Sc (cut n) n (0 + ([i] : Multiset Bool)) (M n i)) q (value_mem n i)
example (n : ℕ) (i : Bool) (q : ZMod 2) := BalancedInduction.shiftedRestrictionChart_source_coordinate (Inc n i)
  (M n i) (P n i) (contentExtensionUnitIso D Sc (cut n) n (0 + ([i] : Multiset Bool)) (M n i)) q (value_mem n i)
example (i : Bool) := BalancedInduction.restrictionFamilyIso_hom_mem (Inc 0 i)
  (fun _ : Option (Fin 0) => M 0 i) (fun _ => P 0 i)
  (fun _ => contentExtensionUnitIso D Sc (cut 0) 0 (0 + ([i] : Multiset Bool)) (M 0 i))
  (fun _ => value_mem 0 i)
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end RestrictionMatrixChartsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVRestrictionMatrixCharts
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
