import OddMath.Algebra.FiniteSupermoduleCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace FiniteSupermoduleCoordinatesConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev C := TruncatedCategory D Sc cut 8
private def R : Superfunctor ℚ C (SVec ℚ) := WeightedAppendFixture.truncatedRepresentable D Sc cut 8
  ((oldTruncateFunctor D Sc cut 8).obj ⟨[false]⟩)
private def V : Bool → Superfunctor ℚ C (SVec ℚ)
  | false => R
  | true => supermoduleParityObj R

/-- Both coordinates retain their distinct parity presentations on all vectors. -/
example (a : Bool) := FiniteSupermodule.projectionHom_mem V a
example (a : Bool) := FiniteSupermodule.inclusionHom_mem V a
example (a : Bool) (t : C) (x : (FiniteSupermodule.product V).obj t) :=
  FiniteSupermodule.projectionHom_total_apply V a t x
example (a : Bool) (t : C) (x : (V a).obj t) :=
  FiniteSupermodule.inclusionHom_total_self V a t x
example (a : Bool) (t : C) (x : (V a).obj t) :=
  FiniteSupermodule.inclusionHom_total_ne V a (!a) (by cases a <;> decide) t x
example (a : Bool) := FiniteSupermodule.inclusionHom_projectionHom V a
example (a : Bool) := FiniteSupermodule.inclusionHom_projectionHom_ne V a (!a) (by cases a <;> decide)
example := FiniteSupermodule.sum_projectionHom_inclusionHom V

/-- The matrix fields and their recovered coordinates are the given module maps. -/
example := FiniteSupermodule.columnsHom_eq_sum V
  (fun a => FiniteSupermodule.inclusionHom V a) (fun a => FiniteSupermodule.inclusionHom_mem V a)
example (a : Bool) := FiniteSupermodule.inclusionHom_columnsHom V
  (fun b => FiniteSupermodule.inclusionHom V b) (fun b => FiniteSupermodule.inclusionHom_mem V b) a
example (a : Bool) := FiniteSupermodule.rowsHom_projectionHom V
  (fun b => FiniteSupermodule.projectionHom V b) (fun b => FiniteSupermodule.projectionHom_mem V b) a

private def emptyFamily : Fin 0 → Superfunctor ℚ C (SVec ℚ) := Fin.elim0
/-- The empty finite family retains the same whole coordinate identity. -/
example := FiniteSupermodule.sum_projectionHom_inclusionHom emptyFamily
end FiniteSupermoduleCoordinatesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.Algebra.FiniteSupermoduleCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
