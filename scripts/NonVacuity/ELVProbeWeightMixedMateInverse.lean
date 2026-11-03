import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedMateInverse
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeWeightMixedMateInverseConsumer
private abbrev D := AsymmetricParameters.datum
private abbrev Sc := parameterTwist D AsymmetricParameters.scalars
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

example (i : Bool) (p : ZMod 2) := probeOldWeightMixedMate_comparison D Sc m i (!i) Λ
  rfl (by abel) rfl rfl (base []) (diff i) p (W (w [] + D.α (!i)))
example (i : Bool) := probeOldWeightMixedMate_supported_isIso D Sc m i (!i) Λ
  rfl (by abel) rfl rfl (base []) (diff i) (W (w [] + D.α (!i)))
example (i : Bool) := probeOldWeightMixedMate_component_isIso D Sc m i (!i) Λ (x₀ := w [])
  rfl (by abel) rfl rfl (diff i) (W (w [] + D.α (!i)))
example (i : Bool) := probeOldActionCrossMate_eq D Sc m i (!i) Λ (x₀ := w [])
  rfl (by abel) rfl rfl
example (i : Bool) := probeOldRouquierData_invNe D Sc m i (!i) Λ (x₀ := w [])
  rfl (by abel) rfl rfl (diff i)
private abbrev mate (i : Bool) := probeOldWeightMixedMate D Sc m i (!i) Λ (x₀ := w [])
  rfl (by abel) rfl rfl
private instance (i : Bool) : IsIso (mate i) :=
  probeOldWeightMixedMate_isIso D Sc m i (!i) Λ (x₀ := w []) rfl (by abel) rfl rfl (diff i)
example (i : Bool) : mate i ≫ inv (mate i) = 𝟙 _ := IsIso.hom_inv_id _
example (i : Bool) : inv (mate i) ≫ mate i = 𝟙 _ := IsIso.inv_hom_id _
example (i : Bool) : inv (mate i) ∈ parity (R := ℚ) _ _ 1 := by
  have hp : D.parity i * D.parity (!i) = (1 : ZMod 2) := by cases i <;> decide
  simpa only [hp] using probeOldWeightMixedMate_inverse_mem D Sc m i (!i) Λ (x₀ := w [])
    rfl (by abel) rfl rfl (diff i)
private def shifted (x : Bool → ℤ) : ProbeOldWeightProduct D Sc m Λ x := fun β =>
  ⟨supermoduleParityObj (W x β).obj,
    probeEvaluatesCoefficients_parity D Sc m β.1.toList (W x β).obj (W x β).property⟩
private def oddInput (x : Bool → ℤ) : shifted x ⟶ W x := fun β =>
  ⟨(supermoduleParityIso (W x β).obj).hom⟩
example (i : Bool) := ((inv (mate i)).isSupernatural 1).naturality_twist
  (oddInput (w [] + D.α (!i)))

private def emptyBlock : WeightBlocks D Λ (-Λ) := ⟨0, by simp⟩
private theorem absent (i : Bool) :
    ¬ ∃ β, blockSucc D Λ i (show (-Λ - D.α i) + D.α i = -Λ by abel) β = emptyBlock := by
  rintro ⟨β, hβ⟩
  have h := congrArg (fun γ => γ.1.card) hβ
  simp only [blockSucc_val, Multiset.card_add, Multiset.card_singleton,
    emptyBlock, Multiset.card_zero] at h
  omega
example (i : Bool) (p : ZMod 2) := probeOldWeightMixedMate_absent_isIso D Sc m i (!i) Λ
  (x₀ := -Λ - D.α i) (xi := -Λ) rfl (by abel) (by abel) rfl
  (diff i) emptyBlock (absent i) p (W ((-Λ - D.α i) + D.α (!i)))
example (i : Bool) := probeOldWeightMixedMate_coordinate_isIso D Sc m i (!i) Λ
  (x₀ := -Λ - D.α i) (xi := -Λ) rfl (by abel) (by abel) rfl
  (diff i) (W ((-Λ - D.α i) + D.α (!i))) emptyBlock
end ProbeWeightMixedMateInverseConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedMateInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
