import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCanonicalContent
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeCanonicalContentConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private def C (β : Multiset Bool) : ProbeCanonicalModules D Sc m β := N β.toList
private theorem target (i : Bool) : (i :: [i,!i]).Perm [i,!i,i] :=
  ((List.Perm.swap i (!i) []).cons i).symm
example (i : Bool) := (probeEvaluatedAppendTo D Sc m [i,!i] i [i,!i,i] (target i)).obj (N [i,!i])
example (i : Bool) := (probeEvaluatedRestrictTo D Sc m [i,!i] i [i,!i,i] (target i)).obj (N [i,!i,i])
example (i : Bool) := probeOldAppendToInduced_evaluatesCoefficients D Sc m [i,!i] i [i,!i,i]
  (target i) (N [i,!i]).obj (N [i,!i]).property
example (i : Bool) := probeOldAppendToRestriction_evaluatesCoefficients D Sc m [i,!i] i [i,!i,i]
  (target i) (N [i,!i,i]).obj (N [i,!i,i]).property
example (i : Bool) := (probeCanonicalRepresentativeEquivalence D Sc m [i,!i]).functor.obj (N [i,!i])
example (i : Bool) := (probeCanonicalInduction D Sc m ([i,!i] : Multiset Bool) i).obj (C [i,!i])
example (i : Bool) := (probeCanonicalRestriction D Sc m ([i,!i] : Multiset Bool) i).obj
  (C (([i,!i] : Multiset Bool) + [i]))
example (i : Bool) := (probeCanonicalInduction D Sc m 0 i).obj (C 0)
example (i : Bool) := (probeCanonicalRestriction D Sc m 0 i).obj (C [i])
example (β : Multiset Bool) := probeCanonicalPiSupercategory D Sc m β
example (i : Bool) : IsSuperfunctor ℚ (probeCanonicalInduction D Sc m 0 i) := inferInstance
example (i : Bool) : IsSuperfunctor ℚ (probeCanonicalRestriction D Sc m 0 i) := inferInstance
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
end ProbeCanonicalContentConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCanonicalContent
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
