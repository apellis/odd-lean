import OddMath.QuiverHecke.CyclotomicAction.ELVRawMixedEvenMate
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDotInverse
import OddMath.QuiverHecke.CyclotomicAction.ProbePolynomialParity
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVRawMixedEvenMate

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



private def m : Unit → ℕ := fun _ => 6
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
  elvRawMixedSource_difference_isUnit D Sc (fun _ => 12) 12 (12 : ℤ) 0 () h E 1 H sy hc rfl x
    (globalActionDot_mem D Sc a ha () 6 h) (probeGlobalActionDot_isUnit D Sc m ha () 6 h)

example (H : B ⟶ R) :=
  elvRawMixedEvenMateDot_isIso D Sc (fun _ => 12) 12 (12 : ℤ) 0 () h E 1 1 H sy hc rfl x
    (globalActionDot_mem D Sc a ha () 6 h) (probeGlobalActionDot_isUnit D Sc m ha () 6 h)

end NonVacuity.ELVRawMixedEvenMate

namespace NonVacuity.ELVRawMixedEvenMate.Occupied

local instance homPi {A B : PiSCat.{0, 0, 1} ℚ} : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private def D : SKM.Datum Bool (Bool → ℤ) :=
  { CyclotomicAction.AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ =>
      CyclotomicAction.AsymmetricParameters.datum.even_of_odd i j rfl }

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

private def sy : SKM.Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl

private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ hs
  exact (hs rfl).elim

private theorem h : (0 : Bool → ℤ) + D.α false = D.α false := zero_add _

private def R : PiSCat.{0, 0, 1} ℚ :=
  elvWeightSpace D Sc (fun _ => 12) 12 0 (D.α false)

private def E : R ⟶ R := Superfunctor.id ℚ R.carrier
private def H : R ⟶ R := Superfunctor.id ℚ R.carrier

/-- The target one-strand block has the vacuum as its actual restriction predecessor. -/
private def vacuumBlock : WeightBlocks D 0 0 := ⟨0, by simp⟩

example : (blockSucc D 0 false h vacuumBlock).1 = {false} := by
  simp [vacuumBlock]

/-- The intermediate functor is the identity on the actual reservoir category,
and the probe endomorphism is its even identity unit. Both Hom shifts remain odd. -/
example :=
  elvRawMixedEvenMateDot_isIso D Sc (fun _ => 12) 12 0 0 false h E 1 1 H sy hc rfl
    (𝟙 E) (id_mem E) isUnit_one

end NonVacuity.ELVRawMixedEvenMate.Occupied

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVRawMixedEvenMate
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
