import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldDotUnit
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
namespace ELVProbeOldDotUnitConsumer
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


private def m : Bool → ℕ := fun i => if i then 5 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev cut := probeCutoff D m
private abbrev M (n : ℕ) :=
  SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) n)
private abbrev ν : List Bool := [false,true]
private abbrev v : ELVOld.OldContentCategory D Sc cut ν :=
  ELVOld.oldContentObject D Sc cut ν ⟨ν,List.Perm.refl ν⟩
private abbrev v0 : ELVOld.OldContentCategory D Sc cut [] :=
  ELVOld.oldContentObject D Sc cut [] ⟨[],List.Perm.refl []⟩

example : IsUnit (End.of ((probeOldModule D m Sc (false :: ν) (M 3)).map
    (show (ELVOld.oldContentAppend D Sc cut ν false).obj v ⟶
      (ELVOld.oldContentAppend D Sc cut ν false).obj v from
        ELVOld.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut false v.obj))) :=
  probeOldAppendDot_action_isUnit D m Sc false ν (M 3) v

example : IsUnit (End.of ((probeOldModule D m Sc (true :: ν) (M 3)).map
    (show (ELVOld.oldContentAppend D Sc cut ν true).obj v ⟶
      (ELVOld.oldContentAppend D Sc cut ν true).obj v from
        ELVOld.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut true v.obj))) :=
  probeOldAppendDot_action_isUnit D m Sc true ν (M 3) v

example : IsUnit (End.of ((probeOldModule D m Sc [false] (M 1)).map
    (show (ELVOld.oldContentAppend D Sc cut [] false).obj v0 ⟶
      (ELVOld.oldContentAppend D Sc cut [] false).obj v0 from
        ELVOld.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut false v0.obj))) :=
  probeOldAppendDot_action_isUnit D m Sc false [] (M 1) v0

example : IsUnit (End.of ((probeOldModule D m Sc [true] (M 1)).map
    (show (ELVOld.oldContentAppend D Sc cut [] true).obj v0 ⟶
      (ELVOld.oldContentAppend D Sc cut [] true).obj v0 from
        ELVOld.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut true v0.obj))) :=
  probeOldAppendDot_action_isUnit D m Sc true [] (M 1) v0

end ELVProbeOldDotUnitConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldDotUnit
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
