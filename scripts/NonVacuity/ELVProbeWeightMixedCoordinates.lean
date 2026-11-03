import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedCoordinates
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeWeightMixedCoordinatesConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private def W (x : Bool → ℤ) : ProbeOldWeightProduct D Sc m Λ x := fun β => N β.1.toList
private def w (v : List Bool) : Bool → ℤ := (v.map D.α).sum - Λ
private def base (v : List Bool) : WeightBlocks D Λ (w v) := ⟨v, rfl⟩
private theorem diff (i : Bool) : i ≠ !i := by cases i <;> decide

example (i : Bool) := probeOldBlockTarget_perm D i Λ rfl (base [])
  (blockSucc D Λ i rfl (base [])) rfl
example (i : Bool) := probeOldInductionComponent_obj_of D Sc m i Λ rfl (base [])
  (blockSucc D Λ i rfl (base [])) rfl (W (w []))
example (i j : Bool) := probeOldWeightMixedSource_obj D Sc m i j Λ
  rfl rfl (base []) (W (w [] + D.α j))
example (i j : Bool) := probeOldWeightMixedTarget_obj D Sc m i j Λ
  rfl (by abel) rfl rfl (base []) (W (w [] + D.α j))
example (i j : Bool) := probeOldBlockDistinctCross_mixed_eq D Sc m i j Λ
  rfl (by abel) rfl rfl (base [])
example (i : Bool) (p : ZMod 2) := probeOldWeightMixedCross_comparison D Sc m i (!i) Λ
  rfl (by abel) rfl rfl (base []) (diff i) p (W (w [] + D.α (!i)))
private def shifted (x : Bool → ℤ) : ProbeOldWeightProduct D Sc m Λ x := fun β =>
  ⟨supermoduleParityObj (W x β).obj,
    probeEvaluatesCoefficients_parity D Sc m β.1.toList (W x β).obj (W x β).property⟩
private def oddInput (x : Bool → ℤ) : shifted x ⟶ W x := fun β =>
  ⟨(supermoduleParityIso (W x β).obj).hom⟩
private theorem oddInput_mem (x : Bool → ℤ) : oddInput x ∈ parity (R := ℚ) _ _ 1 := by
  intro β
  exact supermoduleParityIso_hom_mem (W x β).obj
example (i : Bool) := probeOldInductionComponent_map_of D Sc m i Λ rfl (base [])
  (blockSucc D Λ i rfl (base [])) rfl (oddInput (w []))
example := oddInput_mem (w [])
end ProbeWeightMixedCoordinatesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
