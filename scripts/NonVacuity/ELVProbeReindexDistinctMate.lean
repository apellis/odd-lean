import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexDistinctMate
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace ProbeReindexDistinctMateConsumer
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

private theorem diff (i : Bool) : i ≠ !i := by cases i <;> decide
example (i j : Bool) (t : OldContentCategory D Sc cut (c i)) :=
  oldReindexDistinctLinear_mate D Sc cut base i j (lower j) (lower i) (left i j) (right i j)
    (N (j :: base)).obj t
example (i : Bool) (t : OldContentCategory D Sc cut (c i)) :=
  oldAppendToDistinctMateLinear_bijective D Sc cut base i (!i) (lower (!i)) (lower i)
    (left i (!i)) (right i (!i)) (diff i) (N (c (!i))).obj t
example (i : Bool) :=
  oldAppendToDistinctMateModuleIso_hom D Sc cut base i (!i) (lower (!i)) (lower i)
    (left i (!i)) (right i (!i)) (diff i) (N (c (!i))).obj
example (i : Bool) :=
  oldAppendToDistinctMateModuleIso_inv_mem D Sc cut base i (!i) (lower (!i)) (lower i)
    (left i (!i)) (right i (!i)) (diff i) (N (c (!i))).obj
example (i : Bool) :=
  oldAppendToDistinctMateFunctorIso_hom D Sc cut base i (!i) (lower (!i)) (lower i)
    (left i (!i)) (right i (!i)) (diff i)
example (i : Bool) :=
  oldAppendToDistinctMateFunctorIso_inv_mem D Sc cut base i (!i) (lower (!i)) (lower i)
    (left i (!i)) (right i (!i)) (diff i)
example (i : Bool) :=
  probeAppendToDistinctMateModuleIso_hom D Sc m base i (!i) (lower (!i)) (lower i)
    (left i (!i)) (right i (!i)) (diff i) (N (c (!i)))
example (i : Bool) :=
  probeAppendToDistinctMateModuleIso_inv_native D Sc m base i (!i) (lower (!i)) (lower i)
    (left i (!i)) (right i (!i)) (diff i) (N (c (!i)))
example (i : Bool) :=
  probeAppendToDistinctMateIso_hom D Sc m base i (!i) (lower (!i)) (lower i)
    (left i (!i)) (right i (!i)) (diff i)
example (i : Bool) :=
  probeAppendToCrossMate_eq D Sc m base i (!i) (lower (!i)) (lower i) (left i (!i)) (right i (!i))
example (i : Bool) :=
  probeAppendToCrossMate_isIso D Sc m base i (!i) (lower (!i)) (lower i)
    (left i (!i)) (right i (!i)) (diff i)

private abbrev Do := AsymmetricParameters.datum
private abbrev So := AsymmetricParameters.scalars
private abbrev ao : Bool → Polynomial ℚ := probePolynomial (probeDotExponent Do) m
private def Ro (ν : List Bool) := SuperBimodule.regular
  (heightParity Do So ao (probePolynomial_parity Do m) ν.length)
private def No (ν : List Bool) : ProbeEvaluatedModules Do So m ν :=
  ⟨probeOldModule Do m So ν (Ro ν), probeOldModule_evaluatesCoefficients Do m So ν (Ro ν)⟩
example := probeAppendToCrossMate_isIso Do So m base false true (lower true) (lower false)
  (left false true) (right false true) (by decide)
example : (probeAppendToDistinctMateIso Do So m base false true (lower true) (lower false)
    (left false true) (right false true) (by decide)).inv ∈ parity (R := ℚ) _ _ 1 := by
  have hp : Do.parity false * Do.parity true = (1 : ZMod 2) := by decide
  simpa only [hp] using probeAppendToDistinctMateIso_inv_mem Do So m base false true (lower true) (lower false)
    (left false true) (right false true) (by decide)
example := (probeAppendToDistinctMateIso Do So m base false true (lower true) (lower false)
  (left false true) (right false true) (by decide)).hom_inv_id
example := (probeAppendToDistinctMateIso Do So m base false true (lower true) (lower false)
  (left false true) (right false true) (by decide)).inv_hom_id
private def shifted : ProbeEvaluatedModules Do So m (c true) :=
  ⟨supermoduleParityObj (No (c true)).obj,
    probeEvaluatesCoefficients_parity Do So m (c true) (No (c true)).obj (No (c true)).property⟩
private def oddInput : shifted ⟶ No (c true) := ⟨(supermoduleParityIso (No (c true)).obj).hom⟩
example := ((probeAppendToDistinctMateIso Do So m base false true (lower true) (lower false)
  (left false true) (right false true) (by decide)).inv.isSupernatural 1).naturality_twist oddInput
end ProbeReindexDistinctMateConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexDistinctMate
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
