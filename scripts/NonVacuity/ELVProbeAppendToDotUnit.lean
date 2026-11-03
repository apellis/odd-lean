import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToDotUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeAppendToDotUnitConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private abbrev ν : List Bool := [false,true]
private abbrev μ (i : Bool) := ν ++ [i]
private theorem hp (i : Bool) : (i :: ν).Perm (μ i) := List.perm_append_comm (l₁ := [i]) (l₂ := ν)
example (i : Bool) := probeAppendToInductionDot_isUnit D Sc m ν i (μ i) (hp i)
example (i : Bool) := probeAppendToInductionDotIso_inv_mem D Sc m ν i (μ i) (hp i)
example (i : Bool) := probeAppendToInductionDotIso_hom D Sc m ν i (μ i) (hp i)
example (i : Bool) := probeAppendToInductionDot_total D Sc m ν i (μ i) (hp i) (N ν)
example (i : Bool) := probeAppendToDotModuleIso_hom D Sc m ν i (μ i) (hp i) (N ν)
example (i : Bool) := (probeAppendToInductionDotIso D Sc m ν i (μ i) (hp i)).hom_inv_id
example (i : Bool) := (probeAppendToInductionDotIso D Sc m ν i (μ i) (hp i)).inv_hom_id
example (i : Bool) := probeAppendToInductionDot_isUnit D Sc m [] i [i] (List.Perm.refl _)
example (i : Bool) := probeAppendToInductionDot_total D Sc m [] i [i] (List.Perm.refl _) (N [])
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ProbeAppendToDotUnitConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToDotUnit
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
