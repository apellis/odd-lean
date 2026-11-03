import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexLoopAction
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeReindexLoopActionConsumer
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
private def shifted (i : Bool) : ProbeEvaluatedModules D Sc m (i :: ν) :=
  ⟨supermoduleParityObj (N (i :: ν)).obj,
    probeEvaluatesCoefficients_parity D Sc m (i :: ν) (N (i :: ν)).obj
      (N (i :: ν)).property⟩
example (i : Bool) (q : ZMod 2) :=
  probeEvaluatedLocalMate_app D Sc m ν i q (N (i :: ν))
example (i : Bool) (q : ZMod 2) :=
  mapped_probeEvaluatedLocalMate_app D Sc m ν i (h₁ i) q (N (i :: ν))
example (i : Bool) (q : ZMod 2) :=
  mapped_probeEvaluatedLocalMate_app D Sc m ν i (h₁ i) q (shifted i)
example (i : Bool) (q : ZMod 2) :=
  probeReindexLoopFunctor_app_hom D Sc m ν i (h₁ i)
    (probeEvaluatedLocalMate D Sc m ν i) q (N (ν ++ [i]))
end ProbeReindexLoopActionConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexLoopAction
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
