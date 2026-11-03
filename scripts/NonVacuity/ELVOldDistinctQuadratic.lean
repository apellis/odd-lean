import OddMath.QuiverHecke.CyclotomicAction.ELVOldDistinctQuadratic
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
namespace NonVacuity.ELVOldDistinctQuadratic

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

-- A connected mixed pair, with a genuine interior coefficient retained.
example : D.dn false true = 2 ∧ D.dn true false = 4 := by decide
example : D.parity false = 0 ∧ D.parity true = 1 := by decide
example : Sc.s false true 1 2 = 1 := by norm_num [Sc, D]; decide
example : Sc.s false true 1 2 ≠ 0 := by norm_num [Sc, D]; decide
example : elvSignedPairQuadEval D Sc false true (2 : ℚ) 3 = 67 := by
  have hd : D.d false true ≠ 0 := by decide
  have h₂ : D.dn false true = 2 := rfl
  have h₄ : D.dn true false = 4 := rfl
  rw [elvSignedPairQuadEval, ite_eq_right hd, h₂, h₄]
  norm_num [show Finset.Ioo 0 2 = {1} from by decide,
    show Finset.Ioo 0 4 = {1, 2, 3} from by decide, Sc, D, SKM.zsign]
  change ((if (0 : ZMod 2) = 0 then (-18 : ℚ) else 0) +
    if (1 : ZMod 2) = 0 then -54 else 0) +
      (4 + if (0 : ZMod 2) = 1 then -81 else 81) = 67
  norm_num
example := crossComponent_quadratic D Sc cut (i := false) (j := true) (by decide)
  (⟨[true,false]⟩ : OldCategory D Sc cut)
example := crossComponent_parameterUntwist D Sc cut (i := false) (j := true) (by decide)
  (⟨[true,false]⟩ : OldCategory D Sc' cut)
example := crossComponent_parameterUntwist D Sc cut (i := true) (j := false) (by decide)
  vacuum

-- The actual balanced map is tested on the Hom representable, with literal identity tensors.
example := mixedCrossComponent_quadratic_tensor D Sc cut (i := false) (j := true)
  (by decide) regular vacuum ⟨[false]⟩ ⟨[false,true]⟩ (𝟙 _) (𝟙 _) (𝟙 vacuum)
example := mixedCrossComponent_quadratic_tensor D Sc cut (i := true) (j := false)
  (by decide) regular vacuum ⟨[true]⟩ ⟨[true,false]⟩ (𝟙 _) (𝟙 _) (𝟙 vacuum)

-- Both odd and asymmetric exponents test the negative crossing-square sign.
private abbrev O := AsymmetricParameters.datum
private abbrev Os := AsymmetricParameters.scalars
private abbrev Oc := probeCutoff O m
private abbrev Ot := parameterTwist O Os
private def ov : OldCategory O Ot Oc := ⟨[]⟩
example : elvSignedPairQuadEval O Os false true (2 : ℚ) 3 = 77 := by
  have hd : O.d false true ≠ 0 := by decide
  have h₂ : O.dn false true = 2 := rfl
  have h₄ : O.dn true false = 4 := rfl
  rw [elvSignedPairQuadEval, ite_eq_right hd, h₂, h₄]
  norm_num [show Finset.Ioo 0 2 = {1} from by decide,
    show Finset.Ioo 0 4 = {1, 2, 3} from by decide,
    AsymmetricParameters.scalars, AsymmetricParameters.datum, SKM.zsign]
  change (-4 + if (0 : ZMod 2) = 1 then (-81 : ℚ) else 81) = 77
  norm_num
example : sign ℚ (O.parity false * O.parity true) = -1 := by decide
example := crossComponent_quadratic O Os Oc (i := false) (j := true) (by decide)
  (⟨[true]⟩ : OldCategory O Os Oc)
example := crossComponent_parameterUntwist O Os Oc (i := false) (j := true) (by decide) ov
example := mixedCrossComponent_quadratic_tensor O Os Oc (i := false) (j := true)
  (by decide) (oldRepresentable O Ot Oc ov) ov ⟨[false]⟩ ⟨[false,true]⟩
  (𝟙 _) (𝟙 _) (𝟙 ov)

end NonVacuity.ELVOldDistinctQuadratic

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldDistinctQuadratic
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
