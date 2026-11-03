import OddMath.Algebra.FiniteSupermoduleInverseColumns
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace FiniteSupermoduleInverseColumnsConsumer
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
private def f (a : Bool) : FiniteSupermodule.product V ⟶ T a :=
  FiniteSupermodule.projectionHom V a ≫ (restore a).hom
private theorem f_mem (a : Bool) : f a ∈ parity (R := ℚ) _ _ 1 := by
  simpa only [f, zero_add] using comp_mem (FiniteSupermodule.projectionHom_mem V a) (restore_mem a)
private def e : FiniteSupermodule.product V ≅ FiniteSupermodule.product V := Iso.refl _
private theorem he : e.hom = FiniteSupermodule.restoredRows restore (fun _ => 1) restore_mem f f_mem := by
  rw [FiniteSupermodule.restoredRows]
  have heq : FiniteSupermodule.restoredRow restore f = FiniteSupermodule.projectionHom V := by
    funext a
    simp only [FiniteSupermodule.restoredRow, f, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [heq]
  apply FiniteSupermodule.hom_ext_total
  intro t
  have hid : e.hom.total t = 𝟙 ((FiniteSupermodule.product V).obj t) :=
    SuperNatTrans.id_total (FiniteSupermodule.product V).toFunctor t
  rw [hid]
  apply SVec.hom_ext
  intro x
  rw [SVec.id_apply]
  funext a
  rw [FiniteSupermodule.rowsHom_total_apply, FiniteSupermodule.projectionHom_total_apply]

/-- Odd parity restoration is retained by every extracted inverse row and identity. -/
example (a : Bool) := FiniteSupermodule.inverseCoordinateColumn_mem restore (fun _ => 1) restore_mem f f_mem e he a
example (a : Bool) := FiniteSupermodule.inverseCoordinateColumn_forward restore (fun _ => 1) restore_mem f f_mem e he a
example (a : Bool) := FiniteSupermodule.inverseCoordinateColumn_forward_ne restore (fun _ => 1) restore_mem f f_mem e he
  a (!a) (by cases a <;> decide)
example := FiniteSupermodule.sum_forward_inverseCoordinateColumn restore (fun _ => 1) restore_mem f f_mem e he
end FiniteSupermoduleInverseColumnsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.Algebra.FiniteSupermoduleInverseColumns
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
