import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexRows
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeReindexRowsConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private abbrev ν : List Bool := [false,true]
private theorem h₁ (i : Bool) : (i :: ν).Perm (ν ++ [i]) :=
  (show ([i] ++ ν).Perm (ν ++ [i]) from List.perm_append_comm)
private theorem h₂ (i : Bool) : (i :: (ν ++ [i])).Perm (ν ++ [i,i]) := by
  simpa only [List.append_assoc, List.singleton_append] using
    (show ([i] ++ (ν ++ [i])).Perm ((ν ++ [i]) ++ [i]) from List.perm_append_comm)
private def shifted (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨supermoduleParityObj (N ν).obj,
    probeEvaluatesCoefficients_parity D Sc m ν (N ν).obj (N ν).property⟩
example (i : Bool) := oldAppendReindexIso_cap D Sc m ν i (h₁ i) (N (i :: ν)).obj
example (i : Bool) := oldAppendReindexIso_unit_row D Sc m ν i (h₁ i) (h₂ i) (N (i :: ν)).obj
example (i : Bool) (n : ℕ) := oldAppendReindexIso_capDotRow D Sc m ν i (h₁ i) (N (i :: ν)).obj n
example (i : Bool) (n : ℕ) := oldAppendReindexIso_unitDotColumn D Sc m ν i (h₁ i) (h₂ i)
  (N (i :: ν)).obj n
example (i : Bool) (n : ℕ) := oldAppendReindexIso_capDotRow D Sc m ν i (h₁ i)
  (shifted (i :: ν)).obj n
example (i : Bool) (n : ℕ) := oldAppendReindexIso_unitDotColumn D Sc m ν i (h₁ i) (h₂ i)
  (shifted (i :: ν)).obj n
example : D.parity false = 0 := by decide
example : D.parity true = 1 := by decide
end ProbeReindexRowsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexRows
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
