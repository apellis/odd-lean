import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentCategory
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
namespace ELVOldContentCategoryConsumer
private def D : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun i j => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by
        simp [CartanDatum.cartanMatrix_apply, Ne.symm h]
      zero_comm := fun i j => by
        by_cases h : i = j
        · subst j
          simp [CartanDatum.cartanMatrix_apply]
        · simp [CartanDatum.cartanMatrix_apply, h, Ne.symm h] }
  parity := fun i => if i then 0 else 1
  even_of_odd := by
    intro i j _
    change Even (if j = i then (2 : ℤ) else 0)
    split_ifs <;> norm_num

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit


private def cut : Bool → ℕ := fun i => if i then 5 else 6
private abbrev ν : List Bool := [false,true]
private abbrev v : ELVOld.OldContentCategory D Sc cut ν :=
  ELVOld.oldContentObject D Sc cut ν ⟨[true,false], by exact (List.perm_append_comm : ([true] ++ [false]).Perm ([false] ++ [true]))⟩

example : v.obj.word.length = 2 := ELVOld.oldContentWord_length D Sc cut ν v

example : ((ELVOld.oldContentAppend D Sc cut ν false).obj v).obj.word = [true,false,false] := rfl

example : (ELVOld.oldContentInclusion D Sc cut ν).map (𝟙 v) =
    𝟙 (ELVOld.contentObject D Sc cut ν (ELVOld.oldContentWord D Sc cut ν v)) := rfl

example : IsSuperfunctor ℚ (ELVOld.oldContentAppend D Sc cut ν false) := inferInstance

example : ELVOld.oldContentAppend D Sc cut [] true ⋙ ELVOld.oldContentInclusion D Sc cut [true] =
    ELVOld.oldContentInclusion D Sc cut [] ⋙ ELVOld.CyclotomicCrossingTensor.append D Sc cut true :=
  ELVOld.oldContentAppend_inclusion D Sc cut [] true

end ELVOldContentCategoryConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldContentCategory
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."

