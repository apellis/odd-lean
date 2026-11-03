import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexCrossing
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeReindexCrossingConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (ν : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) ν.length)
private def N (ν : List Bool) : ProbeEvaluatedModules D Sc m ν :=
  ⟨probeOldModule D m Sc ν (R ν), probeOldModule_evaluatesCoefficients D m Sc ν (R ν)⟩
private abbrev base : List Bool := [false,true]
private abbrev c (i : Bool) := ((i :: base : List Bool) : Multiset Bool).toList
private theorem lower (i : Bool) : (i :: base).Perm (c i) := probeCanonicalRepresentative _
private abbrev upper (i j : Bool) := ((i :: c j : List Bool) : Multiset Bool).toList
private theorem left (i j : Bool) : (i :: c j).Perm (upper i j) := probeCanonicalRepresentative _
private theorem right (i j : Bool) : (j :: c i).Perm (upper i j) :=
  ((lower i).symm.cons j).trans ((List.Perm.swap i j base).trans
    (((lower j).cons i).trans (left i j)))
private theorem upPerm (i j : Bool) : (i :: j :: base).Perm (upper i j) :=
  ((lower j).cons i).trans (left i j)

example (i j : Bool) := oldAppendToCross_supernatural D Sc cut base i j
  (lower j) (lower i) (left i j) (right i j)
example (i j : Bool) (s : OldContentCategory D Sc cut base)
    (t : OldContentCategory D Sc cut (c i)) (w : OldContentCategory D Sc cut (upper i j))
    (a : (oldContentAppendTo D Sc cut base i (c i) (lower i)).obj s ⟶ t)
    (g : (oldContentAppendTo D Sc cut (c i) j (upper i j) (right i j)).obj t ⟶ w)
    (b : (N base).obj.obj s) :=
  oldAppendToCrossLinear_tensor D Sc cut base i j (lower j) (lower i) (left i j) (right i j)
    (N base).obj s t w a g b
example (i j : Bool) (s : OldContentCategory D Sc cut base)
    (t : OldContentCategory D Sc cut (i :: base))
    (w : OldContentCategory D Sc cut (upper i j))
    (a : (oldContentAppendTo D Sc cut base i (i :: base) (List.Perm.refl _)).obj s ⟶ t)
    (g : (oldContentAppendTo D Sc cut (i :: base) j (i :: j :: base) (List.Perm.swap i j base)).obj t ⟶
      (oldContentReindex D Sc cut (upPerm i j).symm).obj w)
    (b : (N base).obj.obj s) :=
  oldAppendReindexCross_left_tensor D Sc cut base i j (lower j) (lower i) (left i j) (right i j)
    (N base).obj s t w a g b
example (i j : Bool) (w : OldContentCategory D Sc cut (upper i j)) :=
  oldAppendReindexCrossLinear D Sc cut base i j (lower j) (lower i) (left i j) (right i j)
    (N base).obj w
example (i j : Bool) :=
  oldAppendReindexCross D Sc cut base i j (lower j) (lower i) (left i j) (right i j) (N base).obj
example (i j : Bool) :=
  probeAppendToCross_mem D Sc m base i j (lower j) (lower i) (left i j) (right i j)
example (i j : Bool) :=
  probeAppendToCross_native_total D Sc m base i j (lower j) (lower i) (left i j) (right i j) (N base)
example (i j : Bool) := probeAppendToCross_cons D Sc m base i j
example (i j : Bool) :=
  probeAppendReindexCross D Sc m base i j (lower j) (lower i) (left i j) (right i j) (N base)

private def shifted : ProbeEvaluatedModules D Sc m base :=
  ⟨supermoduleParityObj (N base).obj,
    probeEvaluatesCoefficients_parity D Sc m base (N base).obj (N base).property⟩
private def oddInput : shifted ⟶ N base := ⟨(supermoduleParityIso (N base).obj).hom⟩
example (i j : Bool) :=
  ((probeAppendToCross D Sc m base i j (lower j) (lower i)
    (left i j) (right i j)).isSupernatural (D.parity i * D.parity j)).naturality_twist oddInput
end ProbeReindexCrossingConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexCrossing
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
