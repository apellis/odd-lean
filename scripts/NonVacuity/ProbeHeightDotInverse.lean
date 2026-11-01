import OddMath.QuiverHecke.CyclotomicAction.ProbeHeightDotInverse
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
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
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit


example : IsUnit (probeHeightAppendLastDot D Sc () (fun _ => 3) 0) :=
  probeHeightAppendLastDot_isUnit D Sc () (fun _ => 3) 0

example : probeHeightAppendLastDot D Sc () (fun _ => 3) 0 *
    probeHeightAppendDotInverse D Sc () (fun _ => 3) 0 = 1 :=
  probeHeightAppendLastDot_mul_inverse D Sc () (fun _ => 3) 0

example : probeHeightAppendDotInverse D Sc () (fun _ => 3) 0 *
    probeHeightAppendLastDot D Sc () (fun _ => 3) 0 = 1 :=
  probeHeightAppendLastDot_inverse_mul D Sc () (fun _ => 3) 0

example : IsUnit (probeHeightAppendLastDot D Sc () (fun _ => 3) 2) :=
  probeHeightAppendLastDot_isUnit D Sc () (fun _ => 3) 2

end ProbeFirstDotConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ProbeHeightDotInverse
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
