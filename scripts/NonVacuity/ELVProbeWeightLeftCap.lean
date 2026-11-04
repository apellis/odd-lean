import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightLeftCap
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTensorVacuum
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ELVProbeWeightLeftCap
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private theorem hc (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private def a (i : Bool) : Bool → ℤ := -Λ - D.α i
private def c (i : Bool) : Bool → ℤ := -Λ + D.α i
private theorem h₁ (i : Bool) : a i + D.α i = -Λ := sub_add_cancel _ _
private theorem h₂ (i : Bool) : -Λ + D.α i = c i := rfl
private abbrev δ := WeightTensorVacuum.emptyBlock D Λ
private abbrev M := WeightTensorVacuum.regularProbe D Sc m Λ
private theorem missing (i : Bool) : ¬ ∃ β, blockSucc D Λ i (h₁ i) β = δ := by
  rw [exists_blockSucc_iff]
  change i ∉ (0 : Multiset Bool)
  simp
private theorem negative (i : Bool) : D.h i (-Λ) < 0 := by
  rw [map_neg, ← hc]
  have hp : 0 < probeCutoff D m i := by cases i <;> decide
  omega

-- Both odd colours, every scalar-evaluating input at the whole weight,
-- with the missing-block condition and categorical height proved.
example (i : Bool) (V : ProbeOldWeightProduct D Sc m Λ (-Λ)) :=
  probeOldWeightLoc_cap_missing D Sc m i Λ (h₁ i) (h₂ i) δ
    (hc i) (missing i) (negative i) V
example (i : Bool) :=
  probeOldWeightLoc_cap_missing D Sc m i Λ (h₁ i) (h₂ i) δ
    (hc i) (missing i) (negative i) M

-- The selected whole-weight input contains the literal nonzero regular
-- probe, rather than a zero product used to discharge the chart square.
example : (WeightTensorVacuum.emptyProbe D Sc m Λ).obj M = probeOldVacuumRegular D Sc m :=
  WeightTensorVacuum.emptyProbe_regular D Sc m Λ
example : probeOldVacuumVector D Sc m ≠ 0 := probeOldVacuumVector_ne_zero D Sc m

end NonVacuity.ELVProbeWeightLeftCap
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightLeftCap
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations"
