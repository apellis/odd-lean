import OddMath.QuiverHecke.CyclotomicAction.ProbeGlobalDotInverse
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

private theorem h0 : ({()} : Multiset Unit) + 0 = {()} := by simp
private theorem h1 : ({()} : Multiset Unit) + {()} = {(), ()} := rfl
private abbrev F0 := globalContentInduction D Sc () a ha h0
private abbrev F1 := globalContentInduction D Sc () a ha h1

example : IsIso (C := Supercategory.Superfunctor ℚ
    (GlobalContentModules D Sc a ha 0) (GlobalContentModules D Sc a ha {()}))
    (X := F0) (Y := F0) (globalContentDot D Sc () a ha h0) := by
  change IsIso (probeGlobalContentDotIso D Sc () m ha h0).hom
  infer_instance

example : IsIso (C := Supercategory.Superfunctor ℚ
    (GlobalContentModules D Sc a ha {()}) (GlobalContentModules D Sc a ha {(), ()}))
    (X := F1) (Y := F1) (globalContentDot D Sc () a ha h1) := by
  change IsIso (probeGlobalContentDotIso D Sc () m ha h1).hom
  infer_instance

end ProbeFirstDotConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ProbeGlobalDotInverse
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
