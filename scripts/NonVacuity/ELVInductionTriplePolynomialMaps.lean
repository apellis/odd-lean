import OddMath.QuiverHecke.CyclotomicAction.ELVInductionTriplePolynomialMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixEntries
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace InductionTriplePolynomialMapsConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 12
private abbrev A (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ) (i : Bool) :=
  append D₀ (parameterTwist D₀ Sc₀) cut i
private abbrev F (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ) (i j : Bool) :=
  (A D₀ Sc₀ i ⋙ A D₀ Sc₀ j) ⋙ A D₀ Sc₀ i
private def source (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ) :
    OldCategory D₀ (parameterTwist D₀ Sc₀) cut := ⟨[false,true]⟩
private def N (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ) :=
  oldRepresentable D₀ (parameterTwist D₀ Sc₀) cut (source D₀ Sc₀)

/-- The three actual OLD append dots use the chosen ordinary triple chart. -/
private abbrev chartCheck (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ)
    (i j : Bool) (hij : i ≠ j) :=
  inductionTripleFlattening_polynomial D₀ Sc₀ i j
    (A D₀ Sc₀ i) (A D₀ Sc₀ j) (A D₀ Sc₀ i)
    (oldAppendDot_supernatural D₀ (parameterTwist D₀ Sc₀) cut i)
    (oldAppendDot_supernatural D₀ (parameterTwist D₀ Sc₀) cut j)
    (oldAppendDot_supernatural D₀ (parameterTwist D₀ Sc₀) cut i)
    hij (N D₀ Sc₀)
example := chartCheck D Sc true false (by decide)
example := chartCheck D Sc false true (by decide)
example := chartCheck CyclotomicAction.AsymmetricParameters.datum
  CyclotomicAction.AsymmetricParameters.scalars true false (by decide)

private abbrev J (ν : List Bool) (i : Bool) := oldContentAppend D Sc cut ν i
private abbrev ν : List Bool := [false,true]
private def R := (restriction (oldContentInclusion D Sc cut ν)).obj
  (oldRepresentable D Sc cut (⟨ν⟩ : OldCategory D Sc cut))
example := inductionTripleFlattening_polynomial D Sc true false
  (J ν true) (J (true :: ν) false) (J (false :: true :: ν) true)
  (oldContentAppendDot_supernatural D Sc cut ν true)
  (oldContentAppendDot_supernatural D Sc cut (true :: ν) false)
  (oldContentAppendDot_supernatural D Sc cut (false :: true :: ν) true)
  (by decide) R

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


example := chartCheck D interiorSc true false (by decide)
example := chartCheck D interiorSc false true (by decide)
example (i : Bool) : probeOldVacuumAppendVector D interiorSc (fun _ => 5) i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D interiorSc (fun _ => 5) i (by decide)
end InductionTriplePolynomialMapsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionTriplePolynomialMaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
