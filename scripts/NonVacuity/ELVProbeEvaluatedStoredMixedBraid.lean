import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedStoredMixedBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor OddMath.QuiverHecke.CyclotomicAction
namespace ProbeEvaluatedStoredMixedBraidConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev ν : List Bool := [false,true]
private def m : Bool → ℕ := fun _ => 6
private theorem moveFront (v : List Bool) (i : Bool) : (i :: v).Perm (v ++ [i]) := by
  simpa using (List.perm_append_comm : ([i] ++ v).Perm (v ++ [i]))
private theorem hI (i : Bool) : (i :: ν).Perm (ν ++ [i]) := moveFront ν i
private theorem hII (i : Bool) : (i :: (ν ++ [i])).Perm (ν ++ [i,i]) := by
  simpa [List.append_assoc] using moveFront (ν ++ [i]) i
private theorem hIJ (i j : Bool) : (j :: (ν ++ [i])).Perm (ν ++ [i,j]) := by
  simpa [List.append_assoc] using moveFront (ν ++ [i]) j
private theorem hJI (i j : Bool) : (i :: (ν ++ [j])).Perm (ν ++ [i,j]) := by
  have h₁ : (i :: (ν ++ [j])).Perm (ν ++ [j,i]) := by
    simpa [List.append_assoc] using moveFront (ν ++ [j]) i
  exact h₁.trans ((List.Perm.refl ν).append (List.Perm.swap i j []))
private theorem hTopJ (i j : Bool) : (j :: (ν ++ [i,i])).Perm (ν ++ [i,j,i]) := by
  have h₁ : (j :: (ν ++ [i,i])).Perm (ν ++ [i,i,j]) := by
    simpa [List.append_assoc] using moveFront (ν ++ [i,i]) j
  exact h₁.trans ((List.Perm.refl ν).append (List.Perm.cons i (List.Perm.swap j i [])))
private theorem hTopI (i j : Bool) : (i :: (ν ++ [i,j])).Perm (ν ++ [i,j,i]) := by
  simpa [List.append_assoc] using moveFront (ν ++ [i,j]) i

private def N (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ) :
    ProbeEvaluatedModules D₀ (parameterTwist D₀ Sc₀) m ν :=
  let a := probePolynomial (probeDotExponent D₀) m
  let R := SuperBimodule.regular
    (heightParity D₀ (parameterTwist D₀ Sc₀) a (probePolynomial_parity D₀ m) ν.length)
  ⟨probeOldModule D₀ m (parameterTwist D₀ Sc₀) ν R,
    probeOldModule_evaluatesCoefficients D₀ m (parameterTwist D₀ Sc₀) ν R⟩

/-- All six stored representatives differ from the cons indexing; all seven permutations are proved. -/
private abbrev check (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ)
    (i j : Bool) (hne : i ≠ j) :=
  probeStoredMixedBraid_polynomial D₀ Sc₀ m ν i j (hI i) (hI j)
    (hII i) (hIJ i j) (hJI i j) (hTopJ i j) (hTopI i j) hne (N D₀ Sc₀)
example := check D Sc true false (by decide)
example := check D Sc false true (by decide)
example := check CyclotomicAction.AsymmetricParameters.datum
  CyclotomicAction.AsymmetricParameters.scalars true false (by decide)
example := probeStoredMixedBraid_native D Sc m ν true false (hI true) (hI false)
  (hII true) (hIJ true false) (hJI true false) (hTopJ true false) (hTopI true false) (N D Sc)
example := probeStoredFirstDot_native D Sc m ν true false (hI true) (hIJ true false)
  (hTopI true false) (N D Sc)
example := probeStoredMiddleDot_native D Sc m ν true false (hI true) (hIJ true false)
  (hTopI true false) (N D Sc)
example := probeStoredLastDot_native D Sc m ν true false (hI true) (hIJ true false)
  (hTopI true false) (N D Sc)

private abbrev output :=
  (probeEvaluatedAppendTo D (parameterTwist D Sc) m (ν ++ [true,false]) true
    (ν ++ [true,false,true]) (hTopI true false)).obj
    ((probeEvaluatedAppendTo D (parameterTwist D Sc) m (ν ++ [true]) false
      (ν ++ [true,false]) (hIJ true false)).obj
      ((probeEvaluatedAppendTo D (parameterTwist D Sc) m ν true (ν ++ [true]) (hI true)).obj (N D Sc)))
example (w : OldContentCategory D (parameterTwist D Sc) (probeCutoff D m) (ν ++ [true,false,true]))
    (z : output.obj.obj w) :=
  congrArg (fun f : End output => f.hom.total w z) (check D Sc true false (by decide))

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
end ProbeEvaluatedStoredMixedBraidConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedStoredMixedBraid
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
