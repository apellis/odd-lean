import OddMath.SKM.RouquierProductInverse
import OddMath.SKM.FiniteModuleLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.SKM OddMath.FiniteSupermodule
open OddMath.QuiverHecke.ELVOld
namespace RouquierProductInverseConsumer
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

private def toProduct (n : ℕ) :=
  superSumInvToProduct (C := fun _ : Bool => SVec ℚ) (fun _ : Bool => toRows n)
private def fromProduct (n : ℕ) :=
  superSumInvFromProduct (C := fun _ : Bool => SVec ℚ) (fun _ : Bool => fromColumns n)
private abbrev RR := superfunctorProduct (fun _ : Bool => R)
private def M : Bool → SVec ℚ := fun _ => SVec.unit
private def P : Bool → SVec ℚ := fun _ => SVec.piObj SVec.unit
private def oddInput : P ⟶ M := fun _ => (SVec.ζIso SVec.unit).hom
private theorem oddInput_mem : oddInput ∈ parity (R := ℚ) _ _ 1 :=
  fun _ => SVec.ζIso_hom_mem _

-- Both orientations have every matrix identity on whole endofunctors.
example := (toProduct 0).total
example := (fromProduct 0).total
example := (toProduct 2).total
example := (toProduct 2).ff
example := (toProduct 2).fg 1 (by decide)
example := (toProduct 2).gf 0 (by decide)
example := (toProduct 2).gg 0 1 (by decide) (by decide)
example := (toProduct 2).gg 1 1 (by decide) (by decide)
example := (fromProduct 2).total
example := (fromProduct 2).ff
example := (fromProduct 2).fg 1 (by decide)
example := (fromProduct 2).gf 0 (by decide)
example := (fromProduct 2).gg 0 1 (by decide) (by decide)
example := (fromProduct 2).gg 1 1 (by decide) (by decide)

-- The two extra slots and the principal slot are genuinely nonzero.
private theorem id_RR_ne_zero : (𝟙 RR : RR ⟶ RR) ≠ 0 := by
  intro hz
  have he := congrArg (fun f => (f.app 0 M false) (1 : ℚ)) hz
  change (1 : ℚ) = 0 at he
  exact one_ne_zero he
example : superNatTransProduct (fun _ : Bool => row 2 none) ≠ 0 := by
  intro hz
  have h : (toProduct 2).f' ≫ superNatTransProduct (fun _ : Bool => row 2 none) = 𝟙 RR :=
    (toProduct 2).ff
  have he := congrArg (fun f => (toProduct 2).f' ≫ f) hz
  have hzid := h.symm.trans (he.trans (Limits.comp_zero))
  exact id_RR_ne_zero hzid
example (r : Fin 2) : superNatTransProduct (fun _ : Bool => rows 2 r.val) ≠ 0 := by
  intro hz
  have h : (toProduct 2).g' r.val ≫ superNatTransProduct (fun _ : Bool => rows 2 r.val) = 𝟙 RR := by
    simpa only [ite_true] using (toProduct 2).gg r.val r.val r.isLt r.isLt
  have he := congrArg (fun f => (toProduct 2).g' r.val ≫ f) hz
  have hzid := h.symm.trans (he.trans (Limits.comp_zero))
  exact id_RR_ne_zero hzid
example : superNatTransProduct (fun _ : Bool => col 2 none) ≠ 0 := by
  intro hz
  have h : superNatTransProduct (fun _ : Bool => col 2 none) ≫ (fromProduct 2).f' = 𝟙 RR :=
    (fromProduct 2).ff
  have he := congrArg (fun f => f ≫ (fromProduct 2).f') hz
  have hzid := h.symm.trans (he.trans (Limits.zero_comp))
  exact id_RR_ne_zero hzid
example (r : Fin 2) : superNatTransProduct (fun _ : Bool => cols 2 r.val) ≠ 0 := by
  intro hz
  have h : superNatTransProduct (fun _ : Bool => cols 2 r.val) ≫ (fromProduct 2).g' r.val = 𝟙 RR := by
    simpa only [ite_true] using (fromProduct 2).gg r.val r.val r.isLt r.isLt
  have he := congrArg (fun f => f ≫ (fromProduct 2).g' r.val) hz
  have hzid := h.symm.trans (he.trans (Limits.zero_comp))
  exact id_RR_ne_zero hzid

-- Every inverse entry is exactly its coordinate product, also beyond the window.
example := superSumInvToProduct_f' (fun _ : Bool => toRows 2)
example := superSumInvToProduct_g' (fun _ : Bool => toRows 2) 7
example := superSumInvFromProduct_f' (fun _ : Bool => fromColumns 2)
example := superSumInvFromProduct_g' (fun _ : Bool => fromColumns 2) 7
example := (toProduct 2).g'_mem 7
example := (fromProduct 2).g'_mem 7

-- Both odd forward and inverse transformations retain naturality on odd input maps.
example := (superNatTransProduct (fun _ : Bool => row 2 none)).naturality 1 oddInput oddInput_mem
example := (superNatTransProduct (fun _ : Bool => col 2 none)).naturality 1 oddInput oddInput_mem
example := ((toProduct 2).g' 0).naturality 1 oddInput oddInput_mem
example := ((fromProduct 2).g' 0).naturality 1 oddInput oddInput_mem
end RouquierProductInverseConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierProductInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
