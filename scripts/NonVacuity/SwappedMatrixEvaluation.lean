import OddMath.QuiverHecke.SwappedAssembly.Supernatural.MatrixEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
namespace MatrixEvaluationConsumer
private def R : Superfunctor ℚ (SVec ℚ) (SVec ℚ) := ⟨𝟭 _⟩
private def V : Bool → Superfunctor ℚ (SVec ℚ) (SVec ℚ)
  | false => R
  | true => supermoduleParityObj R
private def a : (j : Bool) → R ≅ V j
  | false => Iso.refl R
  | true => (supermoduleParityIso R).symm
private def ρ : Bool → ZMod 2 | false => 0 | true => 1
private theorem a_mem (j : Bool) : (a j).hom ∈ parity (R := ℚ) _ _ (ρ j) := by
  cases j
  · exact id_mem R
  · exact inv_mem (supermoduleParityIso R) (supermoduleParityIso_hom_mem R)
private def F : Mat_ (Superfunctor ℚ (SVec ℚ) (SVec ℚ)) := ⟨Bool, fun _ => R⟩
private def G : Mat_ (Superfunctor ℚ (SVec ℚ) (SVec ℚ)) := ⟨Bool, V⟩
private def f : F ⟶ G := fun i j => if i = j then (a j).hom else if i = false then (a j).hom else 0
private def g : G ⟶ F := fun i j => if i = j then (a i).inv else if i = false then -(a i).inv else 0
private theorem f_mem (i j : Bool) : f i j ∈ parity (R := ℚ) _ _ (ρ j) := by
  unfold f
  split_ifs <;> first | exact a_mem j | exact Submodule.zero_mem _
private theorem g_mem (i j : Bool) : g i j ∈ parity (R := ℚ) _ _ (ρ i) := by
  unfold g
  split_ifs
  · exact inv_mem (a i) (a_mem i)
  · exact Submodule.neg_mem _ (inv_mem (a i) (a_mem i))
  · exact Submodule.zero_mem _
private theorem fg : f ≫ g = 𝟙 F := by
  apply Mat_.hom_ext
  intro i j
  cases i <;> cases j <;>
    simp [Mat_.comp_apply, f, g, F, G]
private theorem gf : g ≫ f = 𝟙 G := by
  apply Mat_.hom_ext
  intro i j
  cases i <;> cases j <;>
    simp [Mat_.comp_apply, f, g, F, G,
      Preadditive.neg_comp]
private theorem evaluated_f (M : SVec ℚ) : IsIso (MatrixEvaluation.map f M) := by
  refine ⟨MatrixEvaluation.map g M, ?_, ?_⟩
  · rw [← MatrixEvaluation.map_comp, fg, MatrixEvaluation.map_id]
  · rw [← MatrixEvaluation.map_comp, gf, MatrixEvaluation.map_id]
private theorem evaluated_g (M : SVec ℚ) : IsIso (MatrixEvaluation.map g M) := by
  refine ⟨MatrixEvaluation.map f M, ?_, ?_⟩
  · rw [← MatrixEvaluation.map_comp, gf, MatrixEvaluation.map_id]
  · rw [← MatrixEvaluation.map_comp, fg, MatrixEvaluation.map_id]
example : IsIso f := MatrixEvaluation.isIso_of_components_target f ρ f_mem evaluated_f
example : IsIso g := MatrixEvaluation.isIso_of_components_source g ρ g_mem evaluated_g
example : IsIso (𝟙 F) := MatrixEvaluation.isIso_of_components (𝟙 F)
  (by intro i j; by_cases h : i = j
      · subst j; rw [Mat_.id_apply_self]; exact id_mem _
      · rw [Mat_.id_apply_of_ne F i j h]; exact Submodule.zero_mem _)
  (by intro M; rw [MatrixEvaluation.map_id]; infer_instance)
private theorem id_R_ne_zero : (𝟙 R : R ⟶ R) ≠ 0 := by
  intro hz
  have h := congrArg (fun z : R ⟶ R => z.total (SVec.unit (k := ℚ))) hz
  have h' := congrArg (fun z => z (1 : ℚ)) h
  norm_num [SuperNatTrans.total, SVec.id_apply] at h'
example : f false true ≠ 0 := by
  intro hz
  have h : (a true).hom = 0 := by simpa [f] using hz
  have he := (a true).hom_inv_id
  rw [h, Limits.zero_comp] at he
  exact id_R_ne_zero he.symm
example : (MatrixEvaluation.map f (SVec.unit (k := ℚ))) false true ≠ 0 := by
  intro hz
  have he := congrArg (fun z : R ⟶ R => z.total (SVec.unit (k := ℚ))) (a true).hom_inv_id
  rw [Superfunctor.comp_total] at he
  have hz' : (a true).hom.total (SVec.unit (k := ℚ)) = 0 := by simpa [MatrixEvaluation.map, f] using hz
  rw [hz', Limits.zero_comp] at he
  have h' := congrArg (fun z => z (1 : ℚ)) he
  norm_num [SuperNatTrans.total, SVec.id_apply] at h'
  exact (zero_ne_one : (0 : ℚ) ≠ 1) h'
end MatrixEvaluationConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Supernatural.MatrixEvaluation
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
