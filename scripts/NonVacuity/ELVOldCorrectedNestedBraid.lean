import OddMath.QuiverHecke.CyclotomicAction.ELVOldCorrectedNestedBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace OldCorrectedNestedBraidConsumer
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

private abbrev value (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ) (i j : Bool) :=
  induced (A D₀ Sc₀ i) (induced (A D₀ Sc₀ j) (induced (A D₀ Sc₀ i) (N D₀ Sc₀)))
private def vector (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ)
    (i j : Bool) (w : OldCategory D₀ (parameterTwist D₀ Sc₀) cut)
    (g : (F D₀ Sc₀ i j).obj (source D₀ Sc₀) ⟶ w) : (value D₀ Sc₀ i j).obj w :=
  tensor (A D₀ Sc₀ i) (induced (A D₀ Sc₀ j) (induced (A D₀ Sc₀ i) (N D₀ Sc₀))).toFunctor
    ((A D₀ Sc₀ j).obj ((A D₀ Sc₀ i).obj (source D₀ Sc₀))) g
    (tensor (A D₀ Sc₀ j) (induced (A D₀ Sc₀ i) (N D₀ Sc₀)).toFunctor
      ((A D₀ Sc₀ i).obj (source D₀ Sc₀)) (𝟙 _)
      (tensor (A D₀ Sc₀ i) (N D₀ Sc₀).toFunctor (source D₀ Sc₀) (𝟙 _) (𝟙 _)))

/-- The actual independent nested crossings and dots, on the literal three-level tensor. -/
private abbrev check (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ)
    (i j : Bool) (hij : i ≠ j) (w : OldCategory D₀ (parameterTwist D₀ Sc₀) cut)
    (g : (F D₀ Sc₀ i j).obj (source D₀ Sc₀) ⟶ w) :=
  congrArg (fun f : End (value D₀ Sc₀ i j) => f.total w (vector D₀ Sc₀ i j w g))
    (oldNestedMixedBraidMap_polynomial D₀ Sc₀ cut hij (N D₀ Sc₀))


example (w : OldCategory D (parameterTwist D Sc) cut)
    (g : (F D Sc true false).obj (source D Sc) ⟶ w) := check D Sc true false (by decide) w g
example (w : OldCategory D (parameterTwist D Sc) cut)
    (g : (F D Sc false true).obj (source D Sc) ⟶ w) := check D Sc false true (by decide) w g
example := check D Sc true false (by decide) ((F D Sc true false).obj (source D Sc)) (𝟙 _)
example := check CyclotomicAction.AsymmetricParameters.datum
  CyclotomicAction.AsymmetricParameters.scalars true false (by decide)
  ((F CyclotomicAction.AsymmetricParameters.datum CyclotomicAction.AsymmetricParameters.scalars
    true false).obj (source CyclotomicAction.AsymmetricParameters.datum
      CyclotomicAction.AsymmetricParameters.scalars)) (𝟙 _)

example := oldNestedMixedBraidMap_normalized D (parameterTwist D Sc) cut
  (i := true) (j := false) (by decide) (N D Sc)
example (w : OldCategory D (parameterTwist D Sc) cut) (z : (value D Sc true false).obj w) :=
  congrArg (fun f : End (value D Sc true false) => f.total w z)
    (oldNestedMixedBraidMap_polynomial D Sc cut (i := true) (j := false) (by decide) (N D Sc))

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
  ((F D interiorSc true false).obj (source D interiorSc)) (𝟙 _)
example := check D interiorSc false true (by decide)
  ((F D interiorSc false true).obj (source D interiorSc)) (𝟙 _)
/-- The whole coefficient kernel may be odd; it is not replaced by its even projection. -/
example := check D interiorSc true false (by decide)
  ((F D interiorSc true false).obj (source D interiorSc))
  (oldAppendDotComponent D (parameterTwist D interiorSc) cut true
    ((A D interiorSc true ⋙ A D interiorSc false).obj (source D interiorSc)))
example (i : Bool) : probeOldVacuumAppendVector D interiorSc (fun _ => 5) i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D interiorSc (fun _ => 5) i (by decide)
end OldCorrectedNestedBraidConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldCorrectedNestedBraid
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
