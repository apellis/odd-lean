import OddMath.QuiverHecke.CyclotomicAction.ELVModuleZeroBoundary
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ELVModuleZeroBoundary
private theorem module_id_ne_zero
    {C : Type*} [Category* C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    (M : Superfunctor ℚ C (SVec ℚ)) (w : C) (z : M.obj w) (hz : z ≠ 0) : (𝟙 M : M ⟶ M) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : M ⟶ M => f.total w z) h
  simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
    Superfunctor.zero_app, add_zero] at hh
  change z = 0 at hh
  exact hz hh
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (_ : Bool) : ℕ := 1
private abbrev cutoff := probeCutoff D m
private abbrev C := OldContentCategory D Sc cutoff []
private abbrev C₁ := OldContentCategory D Sc cutoff [false]
private abbrev J := oldContentAppend D Sc cutoff [] false
private abbrev A := inductionModulePiCategory (k := ℚ) C
private abbrev B := inductionModulePiCategory (k := ℚ) C₁
private abbrev Z : A ⟶ A := zeroModuleCell C
private abbrev E : A ⟶ B := inductionModuleCell J
private abbrev N₀ := probeOldVacuumRegular D Sc m
private theorem occupied : (probeVacuumScalarEquiv D Sc m 1) ≠ 0 := by
  intro hz
  have he := (probeVacuumScalarEquiv D Sc m).injective
    (hz.trans (map_zero _).symm)
  exact (one_ne_zero : (1 : ℚ) ≠ 0) he

/-- The ambient module category contains the original nonzero regular
probe; the lower zero cell does not replace it by an artificial category. -/
example : (𝟙 N₀ : N₀ ⟶ N₀) ≠ 0 :=
  module_id_ne_zero N₀ (probeOldVacuumObject D Sc m) _ occupied

example : (𝟙 Z : Z ⟶ Z) = 0 := zeroModuleCell_id C
example : (𝟙 (Z ≫ E) : _ ⟶ _) = 0 := zeroModuleCell_comp_id C B E

/-- Whiskering the given odd append dot after the lower zero cell gives
exactly the required zero boundary slide. -/
example : Z ◁ inductionModuleDot J (oldContentAppendDot_supernatural D Sc cutoff [] false) = 0 :=
  zeroModuleCell_whiskerLeft C B _

example : (zeroModuleCellAdjunction (k := ℚ) C).unit = 0 := rfl
example : (zeroModuleCellAdjunction (k := ℚ) C).counit = 0 := rfl
example := (zeroModuleCellAdjunction (k := ℚ) C).left_triangle
example := (zeroModuleCellAdjunction (k := ℚ) C).right_triangle
end NonVacuity.ELVModuleZeroBoundary
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleZeroBoundary
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
