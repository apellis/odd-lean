import OddMath.QuiverHecke.CyclotomicAction.ProbeUnitPropagation
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke
namespace ProbeFirstDotConsumer

private def D : SKM.Datum Unit ℤ where
  cd :=
    { root := fun _ => 2
      coroot := fun _ => LinearMap.id
      coroot_root_self := fun _ => rfl }
  isGCM :=
    { diag := fun _ => rfl
      offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
      zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 0
  even_of_odd := fun _ _ _ => even_two

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit

private def a : Unit → Polynomial ℚ := fun _ => Polynomial.X^2 - 1

example : IsUnit (cyclotomicBlockDot D Sc a [] [] () 1) := by
  apply cyclotomicBlock_evenDot_isUnit D Sc a [] [] () rfl
  exact quadraticProbe_firstDot_isUnit D Sc (probeBlockWord [] [] ())

end ProbeFirstDotConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ProbeUnitPropagation
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
