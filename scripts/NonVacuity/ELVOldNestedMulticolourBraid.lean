import OddMath.QuiverHecke.CyclotomicAction.ELVOldNestedMulticolourBraid
import OddMath.QuiverHecke.CyclotomicAction.ParameterTransport
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace OldNestedMulticolourBraidConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 12
private def N := oldRepresentable D Sc cut (⟨[false,true]⟩ : OldCategory D Sc cut)

example := nestedTripleCross_braid D Sc cut false false true (by decide) N
example := normalizedNestedTripleCross_braid D Sc cut false false true (by decide) N
example := normalizedNestedTripleCross_braid D Sc cut true true false (by decide) N
example := normalizedNestedTripleCross_braid D Sc cut true true true (by simp) N
example := normalizedNestedTripleCross_braid D Sc cut true false false (by decide)
  (supermoduleParityObj N)
example := normalizedNestedTripleCross_braid CyclotomicAction.AsymmetricParameters.datum
  CyclotomicAction.AsymmetricParameters.scalars cut true true false (by decide)
  (oldRepresentable CyclotomicAction.AsymmetricParameters.datum
    CyclotomicAction.AsymmetricParameters.scalars cut ⟨[false,true]⟩)
example (i l : Bool) := normalizedNestedPrefix_equal D Sc cut i l N
example (i j : Bool) := normalizedNestedSuffix_equal D Sc cut i j N
example := normalizedNestedPrefix_distinct D Sc cut true false true (by decide) N
example := normalizedNestedSuffix_distinct D Sc cut true true false (by decide) N

private abbrev A (i : Bool) := append D Sc cut i
private def source : OldCategory D Sc cut := ⟨[false,true]⟩
private abbrev value (i j l : Bool) := induced (A l) (induced (A j) (induced (A i) N))
private abbrev upper (i j l : Bool) := (A l).obj ((A j).obj ((A i).obj source))
private def vector (i j l : Bool) : (value i j l).obj (upper i j l) :=
  tensor (A l) (induced (A j) (induced (A i) N)).toFunctor
    ((A j).obj ((A i).obj source)) (𝟙 _)
    (tensor (A j) (induced (A i) N).toFunctor ((A i).obj source) (𝟙 _)
      (tensor (A i) N.toFunctor source (𝟙 _) (𝟙 _)))

/-- The actual normalized nested equation holds on arbitrary induced vectors. -/
example (i j l : Bool) (hb : ¬ (i = l ∧ i ≠ j)) (t : OldCategory D Sc cut)
    (v : (value l j i).obj t) :=
  congrArg (fun f => f.total t v) (normalizedNestedTripleCross_braid D Sc cut i j l hb N)

/-- Both moving parities, at the literal three-level unit tensor in nonempty old context. -/
example (i : Bool) := congrArg
  (fun f => f.total (upper i i (!i)) (vector i i (!i)))
  (normalizedNestedTripleCross_braid D Sc cut (!i) i i (by cases i <;> decide) N)

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


example := normalizedNestedTripleCross_braid D interiorSc cut true true false (by decide)
  (oldRepresentable D interiorSc cut ⟨[false,true]⟩)
example := normalizedNestedTripleCross_braid D (parameterTwist D interiorSc) cut false false true (by decide)
  (oldRepresentable D (parameterTwist D interiorSc) cut ⟨[false,true]⟩)
example (i : Bool) : probeOldVacuumAppendVector D interiorSc (fun _ => 5) i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D interiorSc (fun _ => 5) i (by decide)
end OldNestedMulticolourBraidConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldNestedMulticolourBraid
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
