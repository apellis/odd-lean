import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumLocalCap
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor ELVOld.ProbeVacuumCap
namespace NonVacuity.ELVProbeVacuumLocalCap
private theorem module_id_ne_zero
    {C : Type*} [Category* C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    (M : Superfunctor ℚ C (SVec ℚ)) (w : C) (z : M.obj w) (hz : z ≠ 0) : (𝟙 M : M ⟶ M) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : M ⟶ M => f.total w z) h
  simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
    Superfunctor.zero_app, add_zero] at hh
  change z = 0 at hh
  exact hz hh
private theorem row_ne_zero {C : Type*} [Category* C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (r : B ⟶ A) (hr : g ≫ r = 𝟙 A)
    (hid : (𝟙 A : A ⟶ A) ≠ 0) : r ≠ 0 := by
  intro h
  rw [h, Limits.comp_zero] at hr
  exact hid hr.symm
private theorem family_ne_zero_of_total
    {k A B : Type*} [CommRing k] [Category* A] [Category* B]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k A B} (f : F ⟶ G) (a : A) (hf : f.total a ≠ 0) : f ≠ 0 := by
  intro h
  apply hf
  rw [h]
  simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add]
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private abbrev cutoff := probeCutoff D m
private abbrev C := OldContentCategory D Sc cutoff []
private abbrev K (i : Bool) := oldContentAppend D Sc cutoff [] i
private abbrev N₀ := probeOldVacuumRegular D Sc m
private abbrev star := probeOldVacuumObject D Sc m
private theorem positive (i : Bool) : 0 < cutoff i := by cases i <;> decide
private theorem level_positive (i : Bool) : 0 < m i := by cases i <;> decide
private abbrev FE (i : Bool) := (restriction (K i)).obj (induced (K i) N₀)
private def feVector (i : Bool) : (FE i).obj star := probeOldVacuumAppendVector D Sc m i
private theorem feVector_ne_zero (i : Bool) : feVector i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc m i (level_positive i)
private theorem regularVector_ne_zero : probeOldVacuumVector D Sc m ≠ 0 :=
  probeOldVacuumVector_ne_zero D Sc m

/-- The local record is CONSTRUCTED on the native probe target; this
consumer has no local-record, inverse or factor-family hypothesis. -/
example (i : Bool) := probeVacuumLoc D Sc m i (positive i)

example (i : Bool) : (probeVacuumLoc D Sc m i (positive i)).capL.total N₀ = cap D Sc m i (positive i) :=
  probeVacuumLoc_cap_total D Sc m i (positive i)

/-- The closure F(E(T0)) is occupied by its literal induction-unit vector. -/
example (i : Bool) : feVector i ≠ 0 := feVector_ne_zero i

/-- The second scalar-closure cap comparison has no scalar-evaluation
premise in the consumer: the producer proves its induction/restriction closure. -/
example (i : Bool) := probeVacuumLoc_cap_FE_coefficient D Sc m i (positive i)

private theorem regular_cap_ne_zero (i : Bool) :
    (probeVacuumLoc D Sc m i (positive i)).capL.total N₀ ≠ 0 := by
  have hp : 0 < probeCutoff D m i := positive i
  have hw := probeVacuumLoc_cap_unitDotColumn D Sc m i hp N₀ (probeCutoff D m i - 1) (by omega)
  apply row_ne_zero (unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N₀ (probeCutoff D m i - 1))
  · exact hw.trans (ite_eq_left (by omega))
  · exact module_id_ne_zero N₀ star (probeOldVacuumVector D Sc m) regularVector_ne_zero

/-- The actual raw cap family is nonzero. -/
example (i : Bool) : (probeVacuumLoc D Sc m i (positive i)).capL ≠ 0 :=
  family_ne_zero_of_total _ N₀ (regular_cap_ne_zero i)

/-- The closure component itself is nonzero, on the same occupied
F(E(T0)) value that occurs in the transpose normalization. -/
example (i : Bool) : (probeVacuumLoc D Sc m i (positive i)).capL.total (FE i) ≠ 0 := by
  have hp : 0 < probeCutoff D m i := positive i
  have hw := probeVacuumLoc_cap_unitDotColumn D Sc m i hp (FE i) (probeCutoff D m i - 1) (by omega)
  apply row_ne_zero (unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) (FE i) (probeCutoff D m i - 1))
  · exact hw.trans (ite_eq_left (by omega))
  · exact module_id_ne_zero (FE i) star (feVector i) (feVector_ne_zero i)

/-- Both all-odd positive probes have an odd raw inverse cap. -/
example (i : Bool) : (probeVacuumLoc D Sc m i (positive i)).capL ∈ parity (R := ℚ) _ _ 1 := by
  cases i
  · exact (probeVacuumLoc D Sc m false (positive false)).capL_mem
  · exact (probeVacuumLoc D Sc m true (positive true)).capL_mem
end NonVacuity.ELVProbeVacuumLocalCap
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumLocalCap
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
