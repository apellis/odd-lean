import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierFamily
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace ELVRouquierFamilyConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def Λ : Bool → ℤ := fun _ => 4
private theorem cutoff (i : Bool) : (cut i : ℤ) = D.h i Λ := rfl
private def T := elvRouquierFamily D Sc cut 8 Λ cutoff
private def w (v : List Bool) : Bool → ℤ := (v.map D.α).sum - Λ
private def M (v : List Bool) (i : Bool) : ELVWeightProduct D Sc cut 8 Λ (w v + D.α i) := fun δ =>
  (BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v ++ [i]⟩))
private theorem negative (i : Bool) : D.h i (w [] + D.α i) ≤ 0 := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem positive (i : Bool) : 0 ≤ D.h i (w [i,i] + D.α i) := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem middle (i : Bool) : D.h i (w [i] + D.α i) = 0 := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]

example := elvRouquierFamily_toRouquierData D Sc cut 8 Λ cutoff
example (i : Bool) := elvRouquierFamily_F D Sc cut 8 Λ cutoff i (x := w []) rfl
example (i : Bool) := elvRouquierFamily_adj D Sc cut 8 Λ cutoff i (x := w []) rfl
example (i : Bool) := T.square i (a := w []) rfl rfl
example (i : Bool) := T.braid i (a := w []) rfl rfl rfl
example (i : Bool) := (T.loc i (a := w []) rfl rfl).slide_left
example (i : Bool) := (T.loc i (a := w []) rfl rfl).slide_right
/-- Both inverse orientations at zero categorical height. -/
example (i : Bool) := ((T.loc i (a := w [i]) rfl rfl).invNeg (le_of_eq (middle i))).total
example (i : Bool) := ((T.loc i (a := w [i]) rfl rfl).invPos (le_of_eq (middle i).symm)).total
/-- The constructed inverse identities on concrete quotient-representable inputs. -/
example (i : Bool) := congrArg (fun f => f.total (M [] i))
  ((T.loc i (a := w []) rfl rfl).invNeg (negative i)).total
example (i : Bool) := congrArg (fun f => f.total (M [i,i] i))
  ((T.loc i (a := w [i,i]) rfl rfl).invPos (positive i)).total

private theorem oddCutoff (i : Bool) : (cut i : ℤ) = AsymmetricParameters.datum.h i Λ := rfl
private def allOdd := elvRouquierFamily AsymmetricParameters.datum
  AsymmetricParameters.scalars cut 8 Λ oddCutoff
example (i : Bool) := allOdd.square i (a := -Λ) rfl rfl
example (i : Bool) := allOdd.braid i (a := -Λ) rfl rfl rfl
example (i : Bool) := (allOdd.loc i (a := -Λ) rfl rfl).slide_left
example (i : Bool) := (allOdd.loc i (a := -Λ) rfl rfl).cross_mem
end ELVRouquierFamilyConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVRouquierFamily
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
