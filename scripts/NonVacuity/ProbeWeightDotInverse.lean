import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDotInverse
import OddMath.QuiverHecke.CyclotomicAction.ProbePolynomialParity
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



private def m : Unit → ℕ := fun _ => 3
private def a : Unit → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private theorem ha : CyclotomicPolynomialParity D a := probePolynomial_parity D m

private theorem h : (6 : ℤ) + D.α () = 8 := by decide

example : globalActionDot D Sc a ha () 6 h ≫
    (probeGlobalActionDotIso D Sc m ha () 6 h).inv =
      𝟙 (globalActionE D Sc a ha () 6 h) :=
  (probeGlobalActionDotIso D Sc m ha () 6 h).hom_inv_id

example : (probeGlobalActionDotIso D Sc m ha () 6 h).inv ≫
    globalActionDot D Sc a ha () 6 h =
      𝟙 (globalActionE D Sc a ha () 6 h) :=
  (probeGlobalActionDotIso D Sc m ha () 6 h).inv_hom_id

example : (probeGlobalActionDotIso D Sc m ha () 6 h).inv ∈
    Supercategory.parity (R := ℚ) (globalActionE D Sc a ha () 6 h)
      (globalActionE D Sc a ha () 6 h) 1 :=
  probeGlobalActionDotIso_inv_mem D Sc m ha () 6 h

example : IsUnit (End.of (globalActionDot D Sc a ha () 6 h)) :=
  probeGlobalActionDot_isUnit D Sc m ha () 6 h

end ProbeFirstDotConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDotInverse
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
