import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.VacuumWindow
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory
open OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
namespace NonVacuity.VacuumWindow
private abbrev L := ModuleCat.of ℚ ℚ
private abbrev Z := ModuleCat.of ℚ (Fin 0 → ℚ)
private theorem id_zero : (𝟙 Z : Z ⟶ Z) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  funext i
  exact Fin.elim0 i
private theorem zero_isZero : Limits.IsZero Z := (Limits.IsZero.iff_id_eq_zero _).mpr id_zero
private def rows (n : ℕ) : L ⟶ L := if n = 0 then 𝟙 L else 0
private def M := negMap (0 : Z ⟶ L) (0 : Z ⟶ Z) (0 : Z ⟶ Z) (0 : Z ⟶ L)
  rows (fun _ : Fin 1 => (0 : L ⟶ Z))
private def B : tObj L Z L Empty ⟶ tObj Z Z L (Fin 1) :=
  tMap 0 0 (fun _ => 𝟙 L) 0 0 (fun _ => 0)
    (fun e : Empty => e.elim) (fun e : Empty => e.elim) (fun e : Empty => e.elim)
private instance : IsIso M := by
  refine ⟨B, ?_, ?_⟩
  · rw [M, B, negMap, tMap_comp, tMap_id]
    refine tMap_congr (by simp [id_zero]) (by simp) (fun _ => by simp)
      (by simp) (by simp [id_zero]) (fun _ => by simp)
      (fun _ => by simp) (fun _ => by simp) ?_
    intro n m
    fin_cases n
    fin_cases m
    simp [rows]
  · rw [M, B, negMap, tMap_comp, tMap_id]
    refine tMap_congr (by simp [rows]) (by simp) (fun e => e.elim)
      (by simp) (by simp [id_zero]) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)

example : IsCupInverse (0 : Z ⟶ L) (fun n : Fin 1 => rows n)
    (inv M none (some none)) (fun n => inv M none (some (some n))) := by
  let : IsIso (negMap (0 : Z ⟶ L) (0 : Z ⟶ Z) (0 : Z ⟶ Z) (0 : Z ⟶ L)
      rows (fun _ : Fin 1 => (0 : L ⟶ Z))) := by change IsIso M; infer_instance
  exact negMap_isCupInverse_of_zero_corners _ _ _ _ rows _ zero_isZero zero_isZero

private def V : CupInverseData (0 : Z ⟶ L) (fun n : Fin 1 => rows n) := by
  letI : IsIso (negMap (-(0 : Z ⟶ L)) (-(0 : Z ⟶ Z)) (-(0 : Z ⟶ Z))
      (-(0 : Z ⟶ L)) rows (fun _ : Fin 1 => (0 : L ⟶ Z))) := by
    have h : IsIso (negMap (0 : Z ⟶ L) (0 : Z ⟶ Z) (0 : Z ⟶ Z) (0 : Z ⟶ L)
      rows (fun _ : Fin 1 => (0 : L ⟶ Z))) := by change IsIso M; infer_instance
    simpa only [neg_zero] using h
  exact negMapCupInverseData (0 : Z ⟶ L) (0 : Z ⟶ Z) (0 : Z ⟶ Z) (0 : Z ⟶ L)
    rows (fun _ : Fin 1 => (0 : L ⟶ Z)) zero_isZero zero_isZero

-- The extracted finite cap is nonzero and satisfies the original unit test.
example : rows 0 ≫ V.window 0 = 𝟙 L := by
  simpa using V.isInverse.2.2.2.1 0 0
example : V.window 0 ≠ 0 := by
  intro hz
  have h := V.isInverse.2.2.2.1 0 0
  simp only [hz, Limits.comp_zero, ite_true] at h
  have h' := congrArg (fun f : L ⟶ L => f.hom 1) h
  norm_num at h'

example : inv M = (Iso.refl _).hom ≫ inv M ≫ (Iso.refl _).inv :=
  inverse_of_chart_square (Iso.refl _) (Iso.refl _) M M (by simp)
end NonVacuity.VacuumWindow
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.CentralInverse.VacuumWindow
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations"
