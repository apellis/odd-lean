import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToRowReindex
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeAppendToRowReindexConsumer
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
private def shifted (i : Bool) : ProbeEvaluatedModules D Sc m (ν ++ [i]) :=
  ⟨supermoduleParityObj (N (ν ++ [i])).obj,
    probeEvaluatesCoefficients_parity D Sc m (ν ++ [i]) (N (ν ++ [i])).obj
      (N (ν ++ [i])).property⟩
private def oddInput (i : Bool) : shifted i ⟶ N (ν ++ [i]) :=
  ⟨(supermoduleParityIso (N (ν ++ [i])).obj).hom⟩
private theorem oddInput_mem (i : Bool) : oddInput i ∈ parity (R := ℚ) _ _ 1 :=
  supermoduleParityIso_hom_mem (N (ν ++ [i])).obj
example (i : Bool) (n : ℕ) := probeAppendToCapRow_reindex D Sc m ν i (h₁ i) n
example (i : Bool) (n : ℕ) := probeAppendToUnitColumn_reindex D Sc m ν i (h₁ i) (h₂ i) n
example (i : Bool) (n : ℕ) := probeAppendToCapRow_standard D Sc m ν i n
example (i : Bool) (n : ℕ) := probeAppendToUnitColumn_standard D Sc m (i :: ν) i n
example (i : Bool) (n : ℕ) := probeAppendToCapRow_total_native D Sc m ν i
  (h₁ i) n (N (ν ++ [i]))
example (i : Bool) (n : ℕ) := probeAppendToCapRow_total_native D Sc m ν i
  (h₁ i) n (shifted i)
example (i : Bool) (n : ℕ) :=
  congrArg (fun f => f.total (N (ν ++ [i])))
    (probeAppendToCapRow_reindex D Sc m ν i (h₁ i) n)
example (i : Bool) (n : ℕ) :=
  congrArg (fun f => f.total (shifted i))
    (probeAppendToUnitColumn_reindex D Sc m ν i (h₁ i) (h₂ i) n)
example (i : Bool) (n : ℕ) (q : ZMod 2) :=
  ((probeAppendToCapRow D Sc m ν i (h₁ i) n).isSupernatural q).naturality (oddInput_mem i)
example (i : Bool) (n : ℕ) (q : ZMod 2) :=
  ((probeAppendToUnitColumn D Sc m (ν ++ [i]) i (h₂ i) n).isSupernatural q).naturality
    (oddInput_mem i)
end ProbeAppendToRowReindexConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToRowReindex
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
