import OddMath.QuiverHecke.CyclotomicAction.ELVInductionPairPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVOldPairPolynomial
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
open OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace NonVacuity.ELVOldPairPolynomial
private def D : SKM.Datum Bool (Bool → ℤ) :=
  { AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => AsymmetricParameters.datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun i j p q => if (p : ZMod 2) * D.parity i = 0 ∧
    (q : ZMod 2) * D.parity j = 0 then 1 else 0
  s_symm := by intro i j p q; simp only [and_comm]
  s_eq_zero := by intro i j p q h; simp [h]
  two_isUnit := by intro _; norm_num
private def m : Bool → ℕ := fun _ => 4
private abbrev cut := probeCutoff D m
private abbrev Sc' := parameterTwist D Sc
private def vacuum : OldCategory D Sc' cut := ⟨[]⟩
private def regular := oldRepresentable D Sc' cut vacuum

-- The representable input contains a nonzero literal empty identity.
private theorem vacuum_id_ne_zero : (𝟙 vacuum) ≠ 0 := by
  intro hz
  have hz' : (𝟙 (probeOldVacuumObject D Sc' m)) = 0 := hz
  have hm := congrArg (fun f =>
    (probeOldVacuumRegular D Sc' m).toFunctor.map f (probeOldVacuumVector D Sc' m)) hz'
  have hv : probeOldVacuumVector D Sc' m = 0 := by
    simpa using hm
  exact probeOldVacuumVector_ne_zero D Sc' m hv
example : (𝟙 vacuum : regular.obj vacuum) ≠ 0 := vacuum_id_ne_zero

private abbrev F (i j : Bool) := (append D Sc' cut i) ⋙ (append D Sc' cut j)
private theorem first (i j : Bool) : IsSupernatural ℚ (D.parity i) (pairFirstDot D Sc' cut i j) :=
  (oldAppendDot_supernatural D Sc' cut i).whiskerRight (append D Sc' cut j)
private theorem second (i j : Bool) : IsSupernatural ℚ (D.parity j) (pairSecondDot D Sc' cut i j) :=
  (oldAppendDot_supernatural D Sc' cut j).whiskerLeft (append D Sc' cut i)
example : Sc.s false true 1 2 ≠ 0 := by norm_num [Sc, D]; decide
example (i : Bool) := signedQuadraticComponent_pairDots D Sc cut i (!i) vacuum
example (i : Bool) := signedQuadraticComponent_pairDots D Sc cut i (!i)
  (⟨[true,false]⟩ : OldCategory D Sc' cut)
example (i : Bool) := transformLinear_pairPolynomial_tensor (F i (!i)) D Sc i (!i)
  (first i (!i)) (second i (!i)) (by cases i <;> decide)
  regular ((F i (!i)).obj vacuum) vacuum (𝟙 _) (𝟙 vacuum)

example (i : Bool) := transformLinear_pairPolynomial (F i (!i)) D Sc i (!i)
  (first i (!i)) (second i (!i)) (by cases i <;> decide)
  (pairPolynomial_supernatural D Sc cut (i := i) (j := !i) (by cases i <;> decide))
  regular ((F i (!i)).obj vacuum)

private abbrev O := AsymmetricParameters.datum
private abbrev Os := AsymmetricParameters.scalars
private abbrev Ot := parameterTwist O Os
private abbrev Oc := probeCutoff O m
private def ov : OldCategory O Ot Oc := ⟨[]⟩
private abbrev Fo := (append O Ot Oc false) ⋙ (append O Ot Oc true)
private theorem ofirst : IsSupernatural ℚ (O.parity false) (pairFirstDot O Ot Oc false true) :=
  (oldAppendDot_supernatural O Ot Oc false).whiskerRight (append O Ot Oc true)
private theorem osecond : IsSupernatural ℚ (O.parity true) (pairSecondDot O Ot Oc false true) :=
  (oldAppendDot_supernatural O Ot Oc true).whiskerLeft (append O Ot Oc false)
example := signedQuadraticComponent_pairDots O Os Oc false true ov
example := transformLinear_pairPolynomial_tensor Fo O Os false true ofirst osecond (by decide)
  (oldRepresentable O Ot Oc ov) (Fo.obj ov) ov (𝟙 _) (𝟙 ov)
example := transformLinear_pairPolynomial Fo O Os false true ofirst osecond (by decide)
  (pairPolynomial_supernatural O Os Oc (i := false) (j := true) (by decide))
  (oldRepresentable O Ot Oc ov) (Fo.obj ov)
end NonVacuity.ELVOldPairPolynomial
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVInductionPairPolynomial,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOldPairPolynomial] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
