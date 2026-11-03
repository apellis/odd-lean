import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexMate
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeReindexMateConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 2 else 4
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) := probeOldModule D m Sc ν (R ν)
private abbrev ν : List Bool := [false,true]
private theorem h₁ (i : Bool) : (i :: ν).Perm (ν ++ [i]) :=
  (show ([i] ++ ν).Perm (ν ++ [i]) from List.perm_append_comm)
private theorem h₂ (i : Bool) : (i :: (ν ++ [i])).Perm (ν ++ [i,i]) := by
  simpa only [List.append_assoc, List.singleton_append] using
    (show ([i] ++ (ν ++ [i])).Perm ((ν ++ [i]) ++ [i]) from List.perm_append_comm)
private def t (i : Bool) : OldContentCategory D Sc cut (ν ++ [i]) :=
  ⟨⟨ν ++ [i]⟩, List.Perm.refl _⟩
example (i : Bool) := oldAppendToEqualCross_supernatural D Sc cut ν i (h₁ i) (h₂ i)
example (i : Bool) := oldReindexLoopLinear_mate D Sc cut ν i (h₁ i) (h₂ i)
  (N (i :: ν)) (t i)
example (i : Bool) := oldReindexLoopLinear_mate D Sc cut ν i (h₁ i) (h₂ i)
  (supermoduleParityObj (N (i :: ν))) (t i)
example (i : Bool) := oldReindexLowerLoopLinear D Sc cut ν i (h₁ i) (N (i :: ν)) (t i)
example (i : Bool) := oldReindexUpperLoopLinear D Sc cut ν i (h₁ i) (h₂ i)
  (N (i :: ν)) (t i)
end ProbeReindexMateConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexMate
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
