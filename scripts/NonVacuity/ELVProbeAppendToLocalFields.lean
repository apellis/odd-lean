import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToLocalFields
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeAppendToLocalFieldsConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 2 else 4
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
private def shifted : ProbeEvaluatedModules D Sc m ν :=
  ⟨supermoduleParityObj (N ν).obj,
    probeEvaluatesCoefficients_parity D Sc m ν (N ν).obj (N ν).property⟩
private def oddInput : shifted ⟶ N ν := ⟨(supermoduleParityIso (N ν).obj).hom⟩
private theorem oddInput_mem : oddInput ∈ parity (R := ℚ) _ _ 1 :=
  supermoduleParityIso_hom_mem (N ν).obj
example (i : Bool) := probeAppendToEqualCross_mem D Sc m ν i (h₁ i) (h₂ i)
example (i : Bool) (q : ZMod 2) :=
  probeAppendToEqualCross_app D Sc m ν i (h₁ i) (h₂ i) q (N ν)
example (i : Bool) := probeAppendToEqualCross_total D Sc m ν i (h₁ i) (h₂ i) (N ν)
example (i : Bool) (q : ZMod 2) := probeAppendToInductionDot_app D Sc m ν i (h₁ i) q (N ν)
example (i : Bool) (n : ℕ) (q : ZMod 2) :=
  probeAppendToDotPower_app D Sc m ν i (h₁ i) n q (N ν)
example (i : Bool) (q : ZMod 2) :=
  probeAppendToMate_app D Sc m ν i (h₁ i) (h₂ i) q (N (ν ++ [i]))
example (i : Bool) :=
  ((probeAppendToEqualCross D Sc m ν i (h₁ i) (h₂ i)).isSupernatural (D.parity i)).naturality
    oddInput_mem
end ProbeAppendToLocalFieldsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToLocalFields
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
