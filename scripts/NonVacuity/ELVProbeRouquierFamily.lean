import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierFamily
import NonVacuity.ELVWeightedAppendFixture
import OddMath.SKM.RouquierFTriangle
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeRouquierFamilyConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := parameterTwist D WeightedAppendFixture.scalars
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

private theorem cutoff (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private abbrev T := probeOldRouquierFamily D Sc m Λ cutoff
example : SKM.RouquierFamily (k := ℚ) (B := PiSCat.{0,0,1} ℚ) D := T
example := probeOldRouquierFamily_toRouquierData D Sc m Λ cutoff
example (i : Bool) := probeOldRouquierFamily_F D Sc m Λ cutoff i (x := w []) rfl
example (i : Bool) := probeOldRouquierFamily_adj D Sc m Λ cutoff i (x := w []) rfl
example (i : Bool) := probeOldRouquierFamily_dot_isUnit D Sc m Λ cutoff i (x := w []) rfl
example (i : Bool) := probeOldWeightLoc D Sc m i Λ (x₀ := w []) rfl rfl (cutoff i)
example := T.leftAdjoints
end ProbeRouquierFamilyConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierFamily
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
