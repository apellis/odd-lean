import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixFunctor
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedMatrixFunctorConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)

example (i : Bool) (m : ℕ) (a : Option (Fin m)) :=
  weightedUnitMatrixSummandFunctor_obj D Sc cut 8 i M m a
example (i : Bool) (m : ℕ) (a : Option (Fin m)) :=
  weightedCapMatrixSummandFunctor_obj D Sc cut 8 i M m a
example (i : Bool) (m : ℕ) (a : Option (Fin m)) :=
  weightedUnitMatrixEntryNatTrans_app D Sc cut 8 i M m a
example (i : Bool) (m : ℕ) (a : Option (Fin m)) :=
  weightedCapMatrixEntryNatTrans_app D Sc cut 8 i M m a
example (i : Bool) (m : ℕ) (a : Option (Fin m)) :=
  (weightedUnitMatrixEntryNatTrans D Sc cut 8 i m a).naturality (supermoduleParityIso M).hom
example (i : Bool) (m : ℕ) (a : Option (Fin m)) :=
  (weightedCapMatrixEntryNatTrans D Sc cut 8 i m a).naturality (supermoduleParityIso M).hom
example (i : Bool) (m : ℕ) (a : Option (Fin m))
    {L P : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ)} (f : L ⟶ P) :=
  (weightedUnitMatrixEntryNatTrans D Sc cut 8 i m a).naturality f
example (i : Bool) (m : ℕ) (a : Option (Fin m))
    {L P : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ)} (f : L ⟶ P) :=
  (weightedCapMatrixEntryNatTrans D Sc cut 8 i m a).naturality f
example (i : Bool) := weightedUnitMatrixEntryNatTrans_app D Sc cut 8 i M 0 none
example (i : Bool) := weightedCapMatrixEntryNatTrans_app D Sc cut 8 i M 0 none
private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def V : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)
example (i : Bool) (m : ℕ) (a : Option (Fin m)) :=
  (weightedUnitMatrixEntryNatTrans D Sc cut 8 i m a).naturality (supermoduleParityIso V).hom
example (i : Bool) (m : ℕ) (a : Option (Fin m)) :=
  (weightedCapMatrixEntryNatTrans D Sc cut 8 i m a).naturality (supermoduleParityIso V).hom
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end WeightedMatrixFunctorConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixFunctor
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
