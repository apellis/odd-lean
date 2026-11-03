import OddMath.Algebra.FiniteSupermoduleInverseRows
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace FiniteSupermoduleInverseRowsConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev C := TruncatedCategory D Sc cut 8
private def R : Superfunctor ℚ C (SVec ℚ) := WeightedAppendFixture.truncatedRepresentable D Sc cut 8
  ((oldTruncateFunctor D Sc cut 8).obj ⟨[false]⟩)
private def V (_ : Bool) := supermoduleParityObj R
private def T (_ : Bool) := R
private def restore (a : Bool) : V a ≅ T a := supermoduleParityIso R
private theorem restore_mem (a : Bool) : (restore a).hom ∈ parity (R := ℚ) _ _ 1 :=
  supermoduleParityIso_hom_mem R
private def f (a : Bool) : T a ⟶ FiniteSupermodule.product V :=
  (restore a).inv ≫ FiniteSupermodule.inclusionHom V a
private theorem f_mem (a : Bool) : f a ∈ parity (R := ℚ) _ _ 1 := by
  simpa only [f, add_zero] using comp_mem (inv_mem (restore a) (restore_mem a))
    (FiniteSupermodule.inclusionHom_mem V a)
private def e : FiniteSupermodule.product V ≅ FiniteSupermodule.product V := Iso.refl _
private theorem he : e.hom = FiniteSupermodule.restoredColumns restore (fun _ => 1) restore_mem f f_mem := by
  rw [FiniteSupermodule.restoredColumns, FiniteSupermodule.columnsHom_eq_sum]
  simp only [FiniteSupermodule.restoredColumn, f, Iso.hom_inv_id_assoc]
  exact (FiniteSupermodule.sum_projectionHom_inclusionHom V).symm

/-- Odd parity restoration is retained by every extracted inverse row and identity. -/
example (a : Bool) := FiniteSupermodule.inverseCoordinateRow_mem restore (fun _ => 1) restore_mem f f_mem e he a
example (a : Bool) := FiniteSupermodule.forward_inverseCoordinateRow restore (fun _ => 1) restore_mem f f_mem e he a
example (a : Bool) := FiniteSupermodule.forward_inverseCoordinateRow_ne restore (fun _ => 1) restore_mem f f_mem e he
  a (!a) (by cases a <;> decide)
example := FiniteSupermodule.sum_inverseCoordinateRow_forward restore (fun _ => 1) restore_mem f f_mem e he
end FiniteSupermoduleInverseRowsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.Algebra.FiniteSupermoduleInverseRows
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
