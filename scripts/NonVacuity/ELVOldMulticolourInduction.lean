import OddMath.QuiverHecke.CyclotomicAction.ELVOldMulticolourInduction
import OddMath.QuiverHecke.CyclotomicAction.ParameterTransport
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace OldMulticolourInductionConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 12
private def N := oldRepresentable D Sc cut (⟨[false,true]⟩ : OldCategory D Sc cut)

example := directTripleCross_braid D Sc cut false false true (by decide) N
example := directTripleCross_braid D Sc cut true true false (by decide) N
example := directTripleCross_braid D Sc cut true true true (by simp) N
example := directTripleCross_braid D Sc cut true false false (by decide) (supermoduleParityObj N)
example := directTripleCross_braid CyclotomicAction.AsymmetricParameters.datum
  CyclotomicAction.AsymmetricParameters.scalars cut true true false (by decide)
  (oldRepresentable CyclotomicAction.AsymmetricParameters.datum
    CyclotomicAction.AsymmetricParameters.scalars cut ⟨[false,true]⟩)

/-- The whole-map relation acts on every vector of the actual direct induced module. -/
example (i j l : Bool) (hb : ¬ (i = l ∧ i ≠ j))
    (t : OldCategory D Sc cut) (v : (induced (tripleAppend D Sc cut l j i) N).obj t) :=
  congrArg (fun f => f.total t v) (directTripleCross_braid D Sc cut i j l hb N)

/-- Its value on the literal canonical unit tensor, with nonempty old context. -/
example (i : Bool) := congrArg
  (fun f => f.total (⟨[false,true,i,i,!i]⟩ : OldCategory D Sc cut)
    (tensor (tripleAppend D Sc cut i i (!i)) N.toFunctor
      (⟨[false,true]⟩ : OldCategory D Sc cut) (𝟙 _) (𝟙 _)))
  (directTripleCross_braid D Sc cut (!i) i i (by cases i <;> decide) N)

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


example := directTripleCross_braid D interiorSc cut true true false (by decide)
  (oldRepresentable D interiorSc cut ⟨[false,true]⟩)
example := directTripleCross_braid D (parameterTwist D interiorSc) cut false false true (by decide)
  (oldRepresentable D (parameterTwist D interiorSc) cut ⟨[false,true]⟩)
example (i : Bool) : probeOldVacuumAppendVector D interiorSc (fun _ => 5) i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D interiorSc (fun _ => 5) i (by decide)
end OldMulticolourInductionConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldMulticolourInduction
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
