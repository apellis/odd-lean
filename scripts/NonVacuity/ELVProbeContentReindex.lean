import OddMath.QuiverHecke.CyclotomicAction.ELVProbeContentReindex
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeContentReindexConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private theorem swap (i : Bool) : [i,!i].Perm [!i,i] := List.Perm.swap _ _ []
example (i : Bool) := (probeEvaluatedReindexEquivalence D Sc m (swap i)).functor.obj (N [i,!i])
example (i : Bool) := (probeEvaluatedReindexEquivalence D Sc m (swap i)).unitIso.hom.app (N [i,!i])
example (i : Bool) := (probeEvaluatedReindexEquivalence D Sc m (swap i)).counitIso.inv.app (N [!i,i])
example (i : Bool) := probeEvaluatedReindex_comp D Sc m (swap i) (swap i).symm
example (i : Bool) := probeEvaluatedReindex_restriction D Sc m i (swap i)
example (i : Bool) := oldContentReindex_append D Sc (probeCutoff D m) i (swap i)
example (i : Bool) (v : OldContentCategory D Sc (probeCutoff D m) [i,!i]) :=
  oldContentReindex_dot D Sc (probeCutoff D m) i (swap i) v
example (i : Bool) (v : OldContentCategory D Sc (probeCutoff D m) [i,!i]) :=
  oldContentReindex_equalCross D Sc (probeCutoff D m) i (swap i) v
example (i : Bool) (v : OldContentCategory D Sc (probeCutoff D m) [i,!i])
    (c : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D (probeCutoff D m)) :=
  probeOldCoefficient_reindex D Sc m (swap i) v c
example := (probeEvaluatedReindexEquivalence D Sc m (List.Perm.refl ([] : List Bool))).unitIso.hom.app (N [])
example (i : Bool) : IsSuperfunctor ℚ (probeEvaluatedReindex D Sc m (swap i)) := inferInstance
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ProbeContentReindexConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeContentReindex
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
