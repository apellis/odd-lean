import OddMath.QuiverHecke.CyclotomicAction.ELVProbeBlockDistinctSlides
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeBlockDistinctSlidesConsumer
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

private theorem neq (i : Bool) : i ≠ !i := by cases i <;> decide
example (i : Bool) := probeOldBlockDistinctCross_slide_inner D Sc m i (!i) Λ
  rfl rfl rfl (by abel) (neq i) (base [i,!i]) _ rfl
example (i : Bool) := probeOldBlockDistinctCross_slide_outer D Sc m i (!i) Λ
  rfl rfl rfl (by abel) (neq i) (base [i,!i]) _ rfl
example (i : Bool) := probeOldBlockPairOuterDotTo_native_total D Sc m i (!i) Λ
  rfl rfl (base [i,!i]) _ rfl (N (base [i,!i]).1.toList)
example (i : Bool) := probeOldBlockPairInnerDotTo_native_total D Sc m i (!i) Λ
  rfl rfl (base [i,!i]) _ rfl (N (base [i,!i]).1.toList)
private abbrev Do := AsymmetricParameters.datum
private abbrev So := AsymmetricParameters.scalars
private abbrev ao : Bool → Polynomial ℚ := probePolynomial (probeDotExponent Do) m
private def Ro (ν : List Bool) := SuperBimodule.regular
  (heightParity Do So ao (probePolynomial_parity Do m) ν.length)
private def No (ν : List Bool) : ProbeEvaluatedModules Do So m ν :=
  ⟨probeOldModule Do m So ν (Ro ν), probeOldModule_evaluatesCoefficients Do m So ν (Ro ν)⟩
private def Wo (x : Bool → ℤ) : ProbeOldWeightProduct Do So m Λ x := fun β => No β.1.toList
private def shifted (x : Bool → ℤ) : ProbeOldWeightProduct Do So m Λ x := fun β =>
  ⟨supermoduleParityObj (Wo x β).obj,
    probeEvaluatesCoefficients_parity Do So m β.1.toList (Wo x β).obj (Wo x β).property⟩
private def oddInput (x : Bool → ℤ) : shifted x ⟶ Wo x := fun β =>
  ⟨(supermoduleParityIso (Wo x β).obj).hom⟩
private theorem oddInput_mem (x : Bool → ℤ) : oddInput x ∈ parity (R := ℚ) _ _ 1 :=
  fun β => supermoduleParityIso_hom_mem (Wo x β).obj

private def wo (v : List Bool) : Bool → ℤ := (v.map Do.α).sum - Λ
private def bo (v : List Bool) : WeightBlocks Do Λ (wo v) := ⟨v,rfl⟩
example := probeOldBlockDistinctCross_slide_inner Do So m false true Λ
  rfl rfl rfl (by abel) (by decide) (bo [false,true]) _ rfl
example := probeOldBlockDistinctCross_slide_outer Do So m false true Λ
  rfl rfl rfl (by abel) (by decide) (bo [false,true]) _ rfl
example := probeOldBlockDistinctCross_native_total Do So m false true Λ
  rfl rfl rfl (by abel) (bo [false,true]) _ rfl (shifted (wo [false,true]) (bo [false,true]))
example : Do.parity false * Do.parity true = 1 := by decide
end ProbeBlockDistinctSlidesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeBlockDistinctSlides
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
