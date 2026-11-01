import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryAppendDot
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
open scoped TensorProduct
namespace ELVProbeOrdinaryAppendDotConsumer
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
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev ν : List Bool := [false,true]
private abbrev v : OrdinaryContentCategory D Sc a ν := ⟨ν,List.Perm.refl _⟩
private abbrev vac : OrdinaryContentCategory D Sc a [] := ⟨[],List.Perm.refl _⟩

example : IsSupernatural ℚ 1 (probeOrdinaryAppendDot D Sc m ν false) :=
  probeOrdinaryAppendDot_supernatural D Sc m ν false
example : IsSupernatural ℚ 0 (probeOrdinaryAppendDot D Sc m ν true) :=
  probeOrdinaryAppendDot_supernatural D Sc m ν true
example : IsUnit (End.of (probeOrdinaryAppendDot D Sc m ν false v)) :=
  probeOrdinaryAppendDot_isUnit D Sc m ν false v
example : IsUnit (End.of (probeOrdinaryAppendDot D Sc m ν true v)) :=
  probeOrdinaryAppendDot_isUnit D Sc m ν true v
example : IsUnit (End.of (probeOrdinaryAppendDot D Sc m [] false vac)) :=
  probeOrdinaryAppendDot_isUnit D Sc m [] false vac
example : IsUnit (End.of (probeOrdinaryAppendDot D Sc m [] true vac)) :=
  probeOrdinaryAppendDot_isUnit D Sc m [] true vac

end ELVProbeOrdinaryAppendDotConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryAppendDot
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."