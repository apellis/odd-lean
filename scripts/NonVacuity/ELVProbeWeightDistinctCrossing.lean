import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDistinctCrossing
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeWeightDistinctCrossingConsumer
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

example (i : Bool) := probeOldActionDistinctCross D Sc m i (!i) Λ (x₀ := w [])
  rfl rfl rfl (by abel)
example (i : Bool) := probeOldActionDistinctCross_mem D Sc m i (!i) Λ (x₀ := w [])
  rfl rfl rfl (by abel)
example (i : Bool) := probeOldBlockDistinctCross_mem D Sc m i (!i) Λ
  rfl rfl rfl (by abel) (base [i,!i]) _ rfl
example (i : Bool) (p : ZMod 2) := probeOldBlockDistinctCross_native_app D Sc m i (!i) Λ
  rfl rfl rfl (by abel) (base [i,!i]) _ rfl p (N (base [i,!i]).1.toList)
example (i : Bool) (p : ZMod 2) := probeOldWeightDistinctCrossVia_component D Sc m i (!i) Λ
  rfl rfl rfl (by abel) (base [i,!i]) _ rfl p (W (w [i,!i]))
example (i : Bool) (p : ZMod 2) := probeOldWeightDistinctCrossComponent_of D Sc m i (!i) Λ
  rfl rfl rfl (by abel) p (W (w [])) (base []) _ rfl

private def emptyBlock : WeightBlocks D Λ (-Λ) := ⟨0, by simp⟩
private theorem absent (i j : Bool) :
    ¬ ∃ β, blockSucc₂ D i j Λ
      (show (-Λ - D.α i - D.α j) + D.α j = -Λ - D.α i by abel)
      (show (-Λ - D.α i) + D.α i = -Λ by abel) β = emptyBlock := by
  rintro ⟨β, hβ⟩
  have h := congrArg (fun γ => γ.1.card) hβ
  simp only [blockSucc₂, blockSucc_val, Multiset.card_add, Multiset.card_singleton,
    emptyBlock, Multiset.card_zero] at h
  omega
example (i : Bool) (p : ZMod 2) := probeOldWeightDistinctCrossComponent_absent D Sc m i (!i) Λ
  (x₀ := -Λ - D.α i - D.α (!i)) (xj := -Λ - D.α i)
  (xi := -Λ - D.α (!i)) (xu := -Λ)
  (by abel) (by abel) (by abel) (by abel) p (W (-Λ - D.α i - D.α (!i))) emptyBlock
    (absent i (!i))

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

/-- Distinct odd colours retain an odd crossing on all odd input maps. -/
example := probeOldActionDistinctCross_mem Do So m false true Λ (x₀ := -Λ)
  rfl rfl rfl (by abel)
example := (probeOldWeightDistinctCross Do So m false true Λ (x₀ := -Λ)
  rfl rfl rfl (by abel)).naturality 1 (oddInput (-Λ)) (oddInput_mem (-Λ))
end ProbeWeightDistinctCrossingConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDistinctCrossing
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
