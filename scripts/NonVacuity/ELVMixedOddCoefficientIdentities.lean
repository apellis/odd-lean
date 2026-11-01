import OddMath.QuiverHecke.CyclotomicAction.ELVMixedOddCoefficientIdentities
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDotInverse
import OddMath.QuiverHecke.CyclotomicAction.ProbePolynomialParity
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVMixedOddCoefficientIdentities

local instance homPi {A B : PiSCat.{0, 0, 1} ℚ} : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

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

example : probeDotExponent D () * m () = 6 := by decide

private theorem h : (0 : ℤ) + D.α () = 2 := by decide


private def A : PiSCat.{0, 0, 1} ℚ where
  toSCat := globalWeightSpace D Sc a ha 6 0
  pi := globalWeightSpacePi D Sc a ha 6 0
private def B : PiSCat.{0, 0, 1} ℚ where
  toSCat := globalWeightSpace D Sc a ha 6 2
  pi := globalWeightSpacePi D Sc a ha 6 2
private def E : A ⟶ B := globalActionE D Sc a ha () 6 h
private def x : End E := globalActionDot D Sc a ha () 6 h


private def sy : SKM.Symmetrizer D where
  d := fun _ => 1
  pos := fun _ => by norm_num
  symm := fun _ _ => rfl

private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ hs
  exact (hs rfl).elim

private def R : PiSCat.{0, 0, 1} ℚ :=
  elvWeightSpace D Sc (fun _ => 12) 12 (12 : ℤ) 2

example (H : B ⟶ R) :=
  elvMixedOddCoefficient_comp_square_difference D Sc (fun _ => 12) 12 (12 : ℤ) 0 () h E 1 1 H
    sy hc rfl x (globalActionDot_mem D Sc a ha () 6 h)
    (probeGlobalActionDot_isUnit D Sc m ha () 6 h)

example (H : B ⟶ R) :=
  elvMixedOddCoefficient_identities D Sc (fun _ => 12) 12 (12 : ℤ) 0 () h E 1 1 H
    sy hc rfl x (globalActionDot_mem D Sc a ha () 6 h)
    (probeGlobalActionDot_isUnit D Sc m ha () 6 h)

end NonVacuity.ELVMixedOddCoefficientIdentities

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVMixedOddCoefficientIdentities
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"

