import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendUpperLoop
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeAppendUpperLoopConsumer
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
private theorem upper (γ : List Bool) (i : Bool) : (i :: γ).Perm (γ ++ [i]) :=
  (show ([i] ++ γ).Perm (γ ++ [i]) from List.perm_append_comm)
private def γ (i : Bool) : List Bool := [!i]
example (i : Bool) : i ∉ γ i := by cases i <;> decide
example (i : Bool) := (probeAppendUpperLoopIso D Sc m (γ i) i (upper (γ i) i)).hom_inv_id
example (i : Bool) := (probeAppendUpperLoopSuperIso D Sc m (γ i) i (upper (γ i) i)).inv_hom_id
example (i : Bool) := probeAppendUpperLoopSuperIso_hom_mem D Sc m (γ i) i (upper (γ i) i)
example (i : Bool) := probeAppendUpperLoopSuperIso_hom_total D Sc m (γ i) i (upper (γ i) i) (N (γ i))
example (i : Bool) := probeAppendUpperLoopSuperIso_hom_total D Sc m ν i (upper ν i) (shifted ν)
example (i : Bool) (n : ℕ) := probeAppendUpperLoop_unitColumn D Sc m (γ i) i (upper (γ i) i) n
example (i : Bool) (n : ℕ) := probeAppendUpperLoop_unitColumn D Sc m ν i (upper ν i) n
example (i : Bool) (n : ℕ) := probeAppendUpperLoop_unitColumn D Sc m [] i (List.Perm.refl [i]) n
example (i : Bool) (n : ℕ) := probeAppendToUnitColumn_total_native D Sc m (γ i) i (upper (γ i) i) n (N (γ i))
example (i : Bool) (n : ℕ) := probeAppendToUnitColumn_total_native D Sc m ν i (upper ν i) n (shifted ν)
example : D.parity false = 0 := by decide
example : D.parity true = 1 := by decide
end ProbeAppendUpperLoopConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendUpperLoop
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
