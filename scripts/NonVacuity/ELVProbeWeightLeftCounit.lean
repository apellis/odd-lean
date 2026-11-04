import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightLeftCounit
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTensorVacuum
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
namespace NonVacuity.ELVProbeWeightLeftCounit
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
  change -(probeCutoff D m i : ℤ) < 0
  have hp : 0 < probeCutoff D m i := by cases i <;> decide
  omega

-- Both odd colours have the nontrivial diagonal sign.
example (i : Bool) : koszulSign (SKM.leftAdjParity D i (-Λ)) (SKM.leftAdjParity D i (-Λ)) = -1 := by
  cases i <;> decide
-- The prescribed parity factor is cancelled at the actual native family.
example (i : Bool) := probeOldLeftCounit_negative_sign D Sc m Λ hc i (h₂ i) (negative i)
example (i : Bool) (V : ProbeOldWeightProduct D Sc m Λ (-Λ)) :=
  probeOldLeftCounit_missing D Sc m Λ hc i (h₂ i) (negative i) δ (missing i) V
example (i : Bool) :=
  probeOldLeftCounit_missing D Sc m Λ hc i (h₂ i) (negative i) δ (missing i) M

-- The selected whole-weight input contains the literal nonzero regular
-- probe, rather than a zero product used to discharge the chart square.
example : (WeightTensorVacuum.emptyProbe D Sc m Λ).obj M = probeOldVacuumRegular D Sc m :=
  WeightTensorVacuum.emptyProbe_regular D Sc m Λ
example : probeOldVacuumVector D Sc m ≠ 0 := probeOldVacuumVector_ne_zero D Sc m

end NonVacuity.ELVProbeWeightLeftCounit
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightLeftCounit
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations"
