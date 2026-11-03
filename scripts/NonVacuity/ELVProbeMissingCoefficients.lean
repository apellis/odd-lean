import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVProbeMissingCoefficients
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m (i : Bool) : ℕ := if i then 2 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (γ : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) γ.length)
private def N (γ : List Bool) : ProbeEvaluatedModules D Sc m γ :=
  ⟨probeOldModule D m Sc γ (R γ), probeOldModule_evaluatesCoefficients D m Sc γ (R γ)⟩
private def shifted (γ : List Bool) : ProbeEvaluatedModules D Sc m γ :=
  ⟨supermoduleParityObj (N γ).obj,
    probeEvaluatesCoefficients_parity D Sc m γ (N γ).obj (N γ).property⟩
private def oddInput (γ : List Bool) : shifted γ ⟶ N γ := ⟨(supermoduleParityIso (N γ).obj).hom⟩
private theorem oddInput_mem (γ : List Bool) : oddInput γ ∈ parity (R := ℚ) _ _ 1 :=
  supermoduleParityIso_hom_mem (N γ).obj
private abbrev count (γ : List Bool) (i : Bool) := contentUnitCount D cut i (γ : Multiset Bool)
private def C (γ : List Bool) (i : Bool) (hi : i ∉ γ) := probeEvaluatedMissingCoefficients D Sc m γ i hi
private def other (i : Bool) : List Bool := [!i]
private theorem absent (i : Bool) : i ∉ other i := by cases i <;> decide
private theorem positive (i : Bool) : 0 < count [] i := by
  cases i <;> decide

private theorem inverse_column_apply
    {C : Type} [Category.{0} C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    {M T : Superfunctor ℚ C (SVec ℚ)} (u : M ⟶ T) (v : T ⟶ M) (h : u ≫ v = 𝟙 M)
    (w : C) (b : M.obj w) : v.total w (u.total w b) = b := by
  have he := congrArg (fun f : M ⟶ M => f.total w b) h
  rw [Superfunctor.comp_total, SVec.comp_apply] at he
  have hi : (𝟙 M : M ⟶ M).total w = 𝟙 (M.obj w) := SuperNatTrans.id_total M.toFunctor w
  rw [hi, SVec.id_apply] at he
  exact he

-- The source is the actual regular evaluated probe with its nonzero PBW vacuum.
example : (N []).obj = probeOldVacuumRegular D Sc m := rfl
example : probeOldVacuumVector D Sc m ≠ 0 := probeOldVacuumVector_ne_zero D Sc m

example (i : Bool) := (C [] i (by simp)).total
example (i : Bool) (j l : ℕ) (hj : j < count [] i) (hl : l < count [] i) :=
  (C [] i (by simp)).entry j l hj hl
example (i : Bool) (j : ℕ) := (C [] i (by simp)).coeff_mem j
example (i : Bool) := (C (other i) i (absent i)).total
example (i : Bool) (j : ℕ) := (C (other i) i (absent i)).coeff_mem j
example (i : Bool) (j l : ℕ) (hj : j < count (other i) i) (hl : l < count (other i) i) :=
  (C (other i) i (absent i)).entry j l hj hl

-- Every actual row keeps its original native component, including odd inputs.
example (i : Bool) (n : ℕ) (q : ZMod 2) :=
  probeEvaluatedMissingCoefficients_coeff_app D Sc m (other i) i (absent i) n q (N (other i))
example (i : Bool) (n : ℕ) :=
  probeEvaluatedMissingCoefficients_coeff_total D Sc m (other i) i (absent i) n (shifted (other i))
example (i : Bool) := probeEvaluatedMissingCoefficients_cap_total D Sc m (other i) i (absent i) (N (other i))
example (i : Bool) (n : ℕ) := ((C (other i) i (absent i)).coeff n).naturality
  ((n : ZMod 2) * D.parity i) (oddInput (other i)) (oddInput_mem (other i))

-- The evaluated top cap itself extracts a nonzero ground vector from its chosen dotted unit.
example (i : Bool) :
    ((((C [] i (by simp)).cap).total (N [])).hom).total (probeOldVacuumObject D Sc m)
      ((((SKM.RouquierBoundary.cup (probeEvaluatedRightAdjunction D Sc m [] i)
        (probeEvaluatedInductionDot D Sc m [] i) (count [] i - 1)).total (N [])).hom).total
          (probeOldVacuumObject D Sc m) (probeOldVacuumVector D Sc m)) ≠ 0 := by
  have h := (C [] i (by simp)).cup_cap (positive i) (j := count [] i - 1) (Nat.sub_lt (positive i) (by decide))
  rw [ite_eq_left rfl] at h
  have hN := congrArg (fun f : (𝟙 (probeEvaluatedTarget D Sc m [])) ⟶
      (𝟙 (probeEvaluatedTarget D Sc m [])) => (f.total (N [])).hom) h
  rw [Superfunctor.comp_total] at hN
  have hid : (𝟙 (𝟙 (probeEvaluatedTarget D Sc m [])) :
      End (𝟙 (probeEvaluatedTarget D Sc m []))).total (N []) = 𝟙 (N []) :=
    SuperNatTrans.id_total (𝟭 (ProbeEvaluatedModules D Sc m [])) (N [])
  rw [hid, InducedCategory.comp_hom, InducedCategory.id_hom] at hN
  have hv := inverse_column_apply _ _ hN (probeOldVacuumObject D Sc m) (probeOldVacuumVector D Sc m)
  rw [hv]
  exact probeOldVacuumVector_ne_zero D Sc m

-- Empty finite window is retained without a positive-cutoff hypothesis.
example (i : Bool) : contentUnitCount D (probeCutoff D (fun _ : Bool => 0)) i (0 : Multiset Bool) = 0 := by
  cases i <;> decide
private def Czero (i : Bool) := probeEvaluatedMissingCoefficients D Sc (fun _ => 0) [] i (by simp)
example (i : Bool) := (Czero i).total
example (i : Bool) (j : ℕ) := (Czero i).coeff_mem j
example : probeOldVacuumVector D Sc (fun _ : Bool => 0) ≠ 0 :=
  probeOldVacuumVector_ne_zero D Sc (fun _ : Bool => 0)
end NonVacuity.ELVProbeMissingCoefficients
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingCoefficients
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
