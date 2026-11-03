import OddMath.SKM.AugmentedInverseEvaluation
import OddMath.SKM.FiniteModuleLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.SKM OddMath.FiniteSupermodule
open OddMath.QuiverHecke.ELVOld
namespace AugmentedInverseEvaluationConsumer
private def R : Superfunctor ℚ (SVec ℚ) (SVec ℚ) := ⟨𝟭 _⟩
private def V (n : ℕ) (_ : Option (Fin n)) := supermoduleParityObj R
private def restore (n : ℕ) (a : Option (Fin n)) : V n a ≅ R := supermoduleParityIso R
private theorem restore_mem (n : ℕ) (a : Option (Fin n)) :
    (restore n a).hom ∈ parity (R := ℚ) _ _ 1 := supermoduleParityIso_hom_mem R
private def col (n : ℕ) (a : Option (Fin n)) : R ⟶ product (V n) :=
  (restore n a).inv ≫ inclusionHom (V n) a
private theorem col_mem (n : ℕ) (a : Option (Fin n)) : col n a ∈ parity (R := ℚ) _ _ 1 := by
  simpa only [col, add_zero] using comp_mem (inv_mem (restore n a) (restore_mem n a))
    (inclusionHom_mem (V n) a)
private def row (n : ℕ) (a : Option (Fin n)) : product (V n) ⟶ R :=
  projectionHom (V n) a ≫ (restore n a).hom
private theorem row_mem (n : ℕ) (a : Option (Fin n)) : row n a ∈ parity (R := ℚ) _ _ 1 := by
  simpa only [row, zero_add] using comp_mem (projectionHom_mem (V n) a) (restore_mem n a)
private def cols (n m : ℕ) : R ⟶ product (V n) := by
  classical
  exact if h : m < n then col n (some ⟨m, h⟩) else 0
private theorem cols_mem (n m : ℕ) : cols n m ∈ parity (R := ℚ) _ _ 1 := by
  classical
  unfold cols
  split_ifs
  · exact col_mem _ _
  · exact Submodule.zero_mem _
private def rows (n m : ℕ) : product (V n) ⟶ R := by
  classical
  exact if h : m < n then row n (some ⟨m, h⟩) else 0
private theorem rows_mem (n m : ℕ) : rows n m ∈ parity (R := ℚ) _ _ 1 := by
  classical
  unfold rows
  split_ifs
  · exact row_mem _ _
  · exact Submodule.zero_mem _
private def e (n : ℕ) : product (V n) ≅ product (V n) := Iso.refl _

private def fromColumns (n : ℕ) : SKM.SuperSumInvFrom (k := ℚ) (col n none) (cols n) 1 (fun _ => 1) n :=
  localInverseFromColumns 1 (fun _ => 1) (restore n none) (fun a => restore n (some a))
    (restore_mem n none) (fun a => restore_mem n (some a))
    (col n none) (cols n) (col_mem n none) (cols_mem n) (e n) (by
      have hc : restoredColumn (optionRestoringIso (restore n none) (fun a => restore n (some a)))
          (optionForwardColumns (col n none) (cols n)) = inclusionHom (V n) := by
        funext a
        cases a with
        | none => simp only [restoredColumn, optionRestoringIso, optionForwardColumns, col,
            Iso.hom_inv_id_assoc]
        | some a => simp only [restoredColumn, optionRestoringIso, optionForwardColumns, cols,
            a.isLt, dite_eq_left, col, Iso.hom_inv_id_assoc]
      rw [restoredColumns, columnsHom_eq_sum]
      simp only [hc]
      exact (sum_projectionHom_inclusionHom (V n)).symm)

private def toRows (n : ℕ) : SKM.SuperSumInvTo (k := ℚ) (row n none) (rows n) 1 (fun _ => 1) n :=
  localInverseToRows 1 (fun _ => 1) (restore n none) (fun a => restore n (some a))
    (restore_mem n none) (fun a => restore_mem n (some a))
    (row n none) (rows n) (row_mem n none) (rows_mem n) (e n) (by
      have hc : restoredRow (optionRestoringIso (restore n none) (fun a => restore n (some a)))
          (optionForwardRows (row n none) (rows n)) = projectionHom (V n) := by
        funext a
        cases a with
        | none => simp only [restoredRow, optionRestoringIso, optionForwardRows, row,
            Category.assoc, Iso.hom_inv_id, Category.comp_id]
        | some a => simp only [restoredRow, optionRestoringIso, optionForwardRows, rows,
            a.isLt, dite_eq_left, row, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [restoredRows]
      simp only [hc]
      apply hom_ext_total
      intro t
      have hid : (e n).hom.total t = 𝟙 ((product (V n)).obj t) :=
        SuperNatTrans.id_total (product (V n)).toFunctor t
      rw [hid]
      apply SVec.hom_ext
      intro x
      rw [SVec.id_apply]
      funext a
      rw [rowsHom_total_apply, projectionHom_total_apply])

private abbrev N := SVec.unit (k := ℚ)
private def toAt := (toRows 2).at N
private def fromAt := (fromColumns 2).at N

-- Every finite matrix identity is retained, in both orientations.
example := toAt.total
example := toAt.ff
example := toAt.fg 1 (by decide)
example := toAt.gf 0 (by decide)
example := toAt.gg 0 1 (by decide) (by decide)
example := toAt.gg 1 1 (by decide) (by decide)
example := fromAt.total
example := fromAt.ff
example := fromAt.fg 1 (by decide)
example := fromAt.gf 0 (by decide)
example := fromAt.gg 0 1 (by decide) (by decide)
example := fromAt.gg 1 1 (by decide) (by decide)
example := ((toRows 0).at N).total
example := ((fromColumns 0).at N).total

-- The inverse components remain the literal whole-map totals, beyond the window too.
example : toAt.f' = (toRows 2).f'.total N := rfl
example (m : ℕ) : toAt.g' m = ((toRows 2).g' m).total N := rfl
example : fromAt.f' = (fromColumns 2).f'.total N := rfl
example (m : ℕ) : fromAt.g' m = ((fromColumns 2).g' m).total N := rfl
example : ((toRows 0).at N).g' 7 = ((toRows 0).g' 7).total N := rfl
example : ((fromColumns 0).at N).g' 7 = ((fromColumns 0).g' 7).total N := rfl

private theorem unit_id_ne_zero : (𝟙 N : N ⟶ N) ≠ 0 := by
  intro hz
  have h := congrArg (fun f => f (1 : ℚ)) hz
  norm_num [SVec.id_apply] at h

example : toAt.f' ≠ 0 := by
  intro hz
  have h := toAt.ff
  rw [hz, Limits.zero_comp] at h
  exact unit_id_ne_zero h.symm
example (m : Fin 2) : toAt.g' m ≠ 0 := by
  intro hz
  have h := toAt.gg m m m.isLt m.isLt
  rw [hz, Limits.zero_comp, ite_eq_left rfl] at h
  exact unit_id_ne_zero h.symm
example : fromAt.f' ≠ 0 := by
  intro hz
  have h := fromAt.ff
  rw [hz, Limits.comp_zero] at h
  exact unit_id_ne_zero h.symm
example (m : Fin 2) : fromAt.g' m ≠ 0 := by
  intro hz
  have h := fromAt.gg m m m.isLt m.isLt
  rw [hz, Limits.comp_zero, ite_eq_left rfl] at h
  exact unit_id_ne_zero h.symm

end AugmentedInverseEvaluationConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.AugmentedInverseEvaluation
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
