import OddMath.QuiverHecke.CyclotomicAction.ELVProbeZeroBoundary
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVProbeZeroBoundary
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m (i : Bool) : ℕ := if i then 2 else 3
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

private theorem evaluated_id_nonzero (γ : List Bool) (M : ProbeEvaluatedModules D Sc m γ)
    (w : OldContentCategory D Sc (probeCutoff D m) γ) (b : M.obj.obj w) (hb : b ≠ 0) :
    (𝟙 M : M ⟶ M) ≠ 0 := by
  intro hz
  have hraw : (𝟙 M.obj : M.obj ⟶ M.obj) = 0 := congrArg (fun f => f.hom) hz
  have he := congrArg (fun f : M.obj ⟶ M.obj => f.total w b) hraw
  simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
    Superfunctor.zero_app, add_zero] at he
  change b = 0 at he
  exact hb he

-- The ambient evaluated category and its actual chosen E remain occupied.
example : (𝟙 (N []) : _ ⟶ _) ≠ 0 := evaluated_id_nonzero [] (N [])
  (probeOldVacuumObject D Sc m) (probeOldVacuumVector D Sc m) (probeOldVacuumVector_ne_zero D Sc m)
private def appendN (i : Bool) := (probeEvaluatedE D Sc m [] i).obj (N [])
example (i : Bool) : (𝟙 (appendN i) : _ ⟶ _) ≠ 0 :=
  evaluated_id_nonzero [i] (appendN i) (probeOldVacuumAppendTarget D Sc m i)
    (probeOldVacuumAppendVector D Sc m i)
    (probeOldVacuumAppendVector_ne_zero D Sc m i (by cases i <;> decide))

example (γ : List Bool) : (probeEvaluatedZeroModule D Sc m γ).obj =
    zeroModule (k := ℚ) (OldContentCategory D Sc (probeCutoff D m) γ) := rfl
example (γ : List Bool) := (probeEvaluatedZeroModule D Sc m γ).property
example (γ : List Bool) := probeEvaluatedZeroModule_id D Sc m γ
example (γ : List Bool) := probeEvaluatedZeroModule_isZero D Sc m γ
example := probeEvaluatedZeroCell_id D Sc m [true,false]
example (i : Bool) := probeEvaluatedZeroCell_id D Sc m [!i]
example (γ : List Bool) : (probeEvaluatedZeroFunctor D Sc m γ).map (𝟙 (N γ)) = 0 := rfl
example (γ : List Bool) : (probeEvaluatedZeroFunctor D Sc m γ).map (oddInput γ) = 0 := rfl
example (γ : List Bool) := Supercategory.map_mem (probeEvaluatedZeroFunctor D Sc m γ) (oddInput_mem γ)

-- The prescribed append and its signed dot are used unchanged after the zero source.
example (i : Bool) := probeEvaluatedZeroCell_comp_id D Sc m [!i]
  (probeEvaluatedTarget D Sc m [i,!i]) (probeEvaluatedE D Sc m [!i] i)
example (i : Bool) := probeEvaluatedZeroCell_whiskerLeft D Sc m [!i]
  (probeEvaluatedTarget D Sc m [i,!i]) (probeEvaluatedInductionDot D Sc m [!i] i)
example (i : Bool) := probeEvaluatedZeroCell_comp_id D Sc m []
  (probeEvaluatedTarget D Sc m [i]) (probeEvaluatedE D Sc m [] i)
example (γ : List Bool) := probeEvaluatedZeroCell_comp_id D Sc m γ
  (probeEvaluatedTarget D Sc m γ) (probeEvaluatedZeroCell D Sc m γ)
example (γ : List Bool) : (probeEvaluatedZeroAdjunction D Sc m γ).unit = 0 := rfl
example (γ : List Bool) : (probeEvaluatedZeroAdjunction D Sc m γ).counit = 0 := rfl
example (γ : List Bool) := (probeEvaluatedZeroAdjunction D Sc m γ).unit_mem
example (γ : List Bool) := (probeEvaluatedZeroAdjunction D Sc m γ).counit_mem
example (γ : List Bool) := (probeEvaluatedZeroAdjunction D Sc m γ).left_triangle
example (γ : List Bool) := (probeEvaluatedZeroAdjunction D Sc m γ).right_triangle

-- Zero probe level still has a nonzero ambient vacuum and the same zero cell.
example : probeOldVacuumVector D Sc (fun _ : Bool => 0) ≠ 0 :=
  probeOldVacuumVector_ne_zero D Sc (fun _ : Bool => 0)
example := probeEvaluatedZeroCell_id D Sc (fun _ : Bool => 0) []
end NonVacuity.ELVProbeZeroBoundary
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeZeroBoundary
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
