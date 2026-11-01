import OddMath.QuiverHecke.CyclotomicAction.ProbeFirstDot
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

private def m : Unit → ℕ := fun _ => 3
private def a : Unit → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev s := repeatedWord () 4
private abbrev C := CyclotomicWordCorner D Sc a s

example : IsUnit (cyclotomicWordEnd D Sc a s (dotE D Sc s.val 0)) :=
  probe_firstDot_isUnit D Sc m s

example : Function.Injective (fun z : C => cyclotomicRepeatedDot D Sc a 3 () 3 * z) :=
  probeRepeated_dots_injective D Sc m 3 () 3 (by omega)

example : Function.Injective
    (fun z : CyclotomicWordCorner D Sc a (probeBlockWord [] [(),()] ()) =>
      cyclotomicBlockDot D Sc a [] [(),()] () 1 * z) :=
  probe_secondDot_injective D Sc m [(),()] ()

end ProbeFirstDotConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for suffix in #["ProbeWordCorner", "ProbeFirstDot"] do
    let owner := Name.str `OddMath.QuiverHecke.CyclotomicAction suffix
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited {names.size} declarations in {owner}."
