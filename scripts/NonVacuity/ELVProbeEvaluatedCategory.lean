import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedCategory
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeEvaluatedCategoryConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
example (i : Bool) := (probeEvaluatedInduction D Sc m [false,true] i).obj (N [false,true])
example (i : Bool) := (probeEvaluatedRestriction D Sc m [false,true] i).obj (N (i :: [false,true]))
example (i : Bool) := (probeEvaluatedInduction D Sc m [] i).obj (N [])
example (i : Bool) := (probeEvaluatedRestriction D Sc m [] i).obj (N [i])
example (ν : List Bool) := probeEvaluatesCoefficients_parity D Sc m ν (N ν).obj (N ν).property
example (ν : List Bool) := probeEvaluatesCoefficients_product D Sc m ν
  (fun _ : Option (Fin 2) => (N ν).obj) (fun _ => (N ν).property)
example := probeEvaluatesCoefficients_product D Sc m []
  (fun _ : Fin 0 => (N []).obj) (fun _ => (N []).property)
example (ν : List Bool) := probeEvaluatedPiSupercategory D Sc m ν
example (i : Bool) : (probeEvaluatedInduction D Sc m [] i).Additive := inferInstance
example (i : Bool) : IsSuperfunctor ℚ (probeEvaluatedRestriction D Sc m [] i) := inferInstance
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ProbeEvaluatedCategoryConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedCategory
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
