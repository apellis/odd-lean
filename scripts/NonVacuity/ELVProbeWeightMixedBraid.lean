import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace ProbeWeightMixedBraidConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev ν : List Bool := [false,true]
private def m : Bool → ℕ := fun _ => 6
private def N (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ) (v : List Bool) :
    ProbeEvaluatedModules D₀ (parameterTwist D₀ Sc₀) m v :=
  let a := probePolynomial (probeDotExponent D₀) m
  let R := SuperBimodule.regular
    (heightParity D₀ (parameterTwist D₀ Sc₀) a (probePolynomial_parity D₀ m) v.length)
  ⟨probeOldModule D₀ m (parameterTwist D₀ Sc₀) v R,
    probeOldModule_evaluatesCoefficients D₀ m (parameterTwist D₀ Sc₀) v R⟩
private def Λ (D₀ : SKM.Datum Bool (Bool → ℤ)) : Bool → ℤ := fun i => probeCutoff D₀ m i
private def W (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ) (x : Bool → ℤ) :
    ProbeOldWeightProduct D₀ (parameterTwist D₀ Sc₀) m (Λ D₀) x := fun β => N D₀ Sc₀ β.1.toList
private def w (D₀ : SKM.Datum Bool (Bool → ℤ)) (v : List Bool) := (v.map D₀.α).sum - Λ D₀
private def base (D₀ : SKM.Datum Bool (Bool → ℤ)) (v : List Bool) :
    WeightBlocks D₀ (Λ D₀) (w D₀ v) := ⟨v,rfl⟩
private abbrev check (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ)
    (i j : Bool) (hne : i ≠ j) :=
  probeOldRouquierData_braidEq D₀ Sc₀ m i j (Λ D₀) (a := w D₀ ν)
    rfl rfl rfl rfl (by abel) rfl (by abel) hne
example := check D Sc true false (by decide)
example := check D Sc false true (by decide)
example := check AsymmetricParameters.datum AsymmetricParameters.scalars true false (by decide)
example := check AsymmetricParameters.datum AsymmetricParameters.scalars false true (by decide)
example (i j : Bool) (hne : i ≠ j) := probeOldWeightMixedBraid_component D Sc m i j (Λ D)
  rfl rfl rfl rfl (by abel) rfl (by abel) (base D ν) hne (W D Sc (w D ν))
example (i j : Bool) (hne : i ≠ j) := probeOldActionCross_mixedBraid D Sc m i j (Λ D)
  (a := -Λ D - D.α i - D.α j - D.α i) rfl rfl rfl rfl (by abel) rfl (by abel) hne
/-- A nonzero admissible interior parameter in the mixed symmetrizable datum. -/
private def interiorSc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun i j p q => if i = j then 0 else
    if p = (if i then 2 else 1) ∧ q = (if j then 2 else 1) then 3 else 0
  s_symm := by
    intro i j p q
    by_cases hij : i = j
    · subst j
      simp
    · simp only [hij, Ne.symm hij, ↓reduceIte, and_comm]
  s_eq_zero := by
    intro i j p q hp
    cases i
    · simp [D, WeightedAppendFixture.datum] at hp
    · cases j
      · change (if p = 2 ∧ q = 1 then (3 : ℚ) else 0) = 0
        by_cases hp2 : p = 2
        · subst p
          exact False.elim ((by decide : ¬ (((2 : ℕ) : ZMod 2) * D.parity true = 1)) hp)
        · simp [hp2]
      · rfl
  two_isUnit := by intro _; norm_num

example : interiorSc.s false true 1 2 = 3 := by decide
example : interiorSc.s true false 2 1 = 3 := by decide
example : (parameterTwist D interiorSc).s false true 1 2 = -3 := by
  change SKM.zsign ℚ (parameterSignExponent D false true 1 2) * 3 = -3
  have hp : parameterSignExponent D false true 1 2 = 1 := by decide
  rw [hp]
  norm_num [SKM.zsign]
example : (parameterTwist D interiorSc).s true false 2 1 = -3 := by
  change SKM.zsign ℚ (parameterSignExponent D true false 2 1) * 3 = -3
  have hp : parameterSignExponent D true false 2 1 = 1 := by decide
  rw [hp]
  norm_num [SKM.zsign]
example : interiorSc.Homogeneous := by
  intro i j p q _ _ _ _ h
  cases i <;> cases j
  · simp [interiorSc] at h
  · have he : p = 1 ∧ q = 2 := by simpa [interiorSc] using h
    rcases he with ⟨rfl, rfl⟩
    decide
  · have he : p = 2 ∧ q = 1 := by simpa [interiorSc] using h
    rcases he with ⟨rfl, rfl⟩
    decide
  · simp [interiorSc] at h

example := check D interiorSc true false (by decide)
example := check D interiorSc false true (by decide)
example (i : Bool) : probeOldVacuumAppendVector D interiorSc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D interiorSc m i (by cases i <;> decide)
end ProbeWeightMixedBraidConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedBraid
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
