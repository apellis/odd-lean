import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvenVacuumPolynomial
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVProbeEvenVacuumPolynomial
private theorem nonzero_of_extracts {V : Type} [AddCommGroup V] [Module ℚ V]
    (f : V →ₗ[ℚ] ℚ) (v : V) (h : f v = 1) : v ≠ 0 := by
  intro hz
  have hv : f v = 0 := (congrArg f hz).trans f.map_zero
  exact zero_ne_one (hv.symm.trans h)
private def D : SKM.Datum Bool (Bool → ℤ) :=
  { CyclotomicAction.AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => CyclotomicAction.AsymmetricParameters.datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private def m : Bool → ℕ := fun _ => 2
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev R := ProbeVacuumCap.modulePiCategory D Sc m
private abbrev H : R ⟶ R := 𝟙 R
private abbrev w := probeOldVacuumObject D Sc m
private abbrev V (i : Bool) := (ProbeVacuumCap.source D Sc m i).obj w
private def topVector (i : Bool) : V i :=
  SVec.toLinearMap (ProbeVacuumCap.dot D Sc m i ^ (probeCutoff D m i - 1))
    (ProbeVacuumCap.unitVector D Sc m i (1 : ℚ))
private theorem extracts_top (i : Bool) :
    ProbeVacuumCap.groundRow D Sc m i (positive i) (topVector i) = 1 := by
  have h := ProbeVacuumCap.groundRow_dot_unit D Sc m i (positive i)
    (probeCutoff D m i - 1) (Nat.sub_lt (positive i) (by decide)) (1 : ℚ)
  rw [ite_eq_left (Nat.sub_add_cancel (positive i))] at h
  convert h using 1
  congr 1
private theorem top_ne_zero (i : Bool) : topVector i ≠ 0 :=
  nonzero_of_extracts (ProbeVacuumCap.groundRow D Sc m i (positive i))
    (topVector i) (extracts_top i)

/-- Both colours are occupied, while only the moving colour is even. -/
example : topVector false ≠ 0 ∧ topVector true ≠ 0 := ⟨top_ne_zero false, top_ne_zero true⟩
example : D.parity false = 0 ∧ D.parity true = 1 ∧ D.d false true = 2 := by decide

example : (ProbeVacuumCap.moduleDot D Sc m false - 1) ^ 2 = 0 :=
  ProbeVacuumCap.moduleDot_even_polynomial D Sc m false rfl
example : (ProbeVacuumCap.preDotEnd D Sc m R false H - 1) ^ 2 = 0 :=
  ProbeVacuumCap.preDot_even_polynomial D Sc m R false rfl H
example : (ProbeVacuumCap.coordinatePreDotPower D Sc m R false H 1 - 1) ^ 2 = 0 :=
  ProbeVacuumCap.coordinatePreDot_even_polynomial D Sc m R false rfl H
example : (ProbeVacuumCap.shiftedPreDot D Sc m R false H - 1) ^ 2 = 0 :=
  ProbeVacuumCap.shiftedPreDot_even_polynomial D Sc m R false rfl H
example : IsUnit (ProbeVacuumCap.shiftedPreDot D Sc m R false H) :=
  ProbeVacuumCap.shiftedPreDot_even_isUnit D Sc m R false rfl H

private abbrev e := ProbeVacuumCap.preSourceComponent D Sc m R false H
private def shiftedVector := (moduleIsoLinearEquiv e w).symm (topVector false)
/-- The annihilator and unit are checked on a source with a nonzero vector. -/
example : shiftedVector ≠ 0 := by
  intro hz
  have h := congrArg (moduleIsoLinearEquiv e w) hz
  rw [show moduleIsoLinearEquiv e w shiftedVector = topVector false from
    (moduleIsoLinearEquiv e w).apply_symm_apply _, map_zero] at h
  exact top_ne_zero false h

/-- The odd colour simultaneously retains its different signed polynomial. -/
example : (ProbeVacuumCap.shiftedPreDot D Sc m R true H ^ 2 + 1) ^ 2 = 0 :=
  ProbeVacuumCap.shiftedPreDot_odd_polynomial D Sc m R true rfl H
end NonVacuity.ELVProbeEvenVacuumPolynomial
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvenVacuumPolynomial
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms"
