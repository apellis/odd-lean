import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedStoredBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor OddMath.QuiverHecke.CyclotomicAction
namespace ProbeEvaluatedStoredBraidConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun _ => 6
private theorem one (v : List Bool) (i : Bool) : (i :: v).Perm (v ++ [i]) := by
  simpa using (List.perm_append_comm : ([i] ++ v).Perm (v ++ [i]))
private theorem pair (v : List Bool) (i j : Bool) : (j :: (v ++ [i])).Perm (v ++ [i,j]) := by
  simpa [List.append_assoc] using one (v ++ [i]) j
private theorem pairRev (v : List Bool) (i j : Bool) : (i :: (v ++ [j])).Perm (v ++ [i,j]) := by
  exact (pair v j i).trans ((List.Perm.refl v).append (List.Perm.swap i j []))
private theorem topL (v : List Bool) (i j l : Bool) :
    (l :: (v ++ [i,j])).Perm (v ++ [i,j,l]) := by
  simpa [List.append_assoc] using one (v ++ [i,j]) l
private theorem topJ (v : List Bool) (i j l : Bool) :
    (j :: (v ++ [i,l])).Perm (v ++ [i,j,l]) := by
  exact (topL v i l j).trans ((List.Perm.refl v).append (List.Perm.cons i (List.Perm.swap j l [])))
private theorem topI (v : List Bool) (i j l : Bool) :
    (i :: (v ++ [j,l])).Perm (v ++ [i,j,l]) := by
  refine (topL v j l i).trans ((List.Perm.refl v).append ?_)
  simpa using (List.perm_append_comm : ([i] ++ [j,l]).Perm ([j,l] ++ [i])).symm

private def N (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ) (v : List Bool) :
    ProbeEvaluatedModules D₀ (parameterTwist D₀ Sc₀) m v :=
  let a := probePolynomial (probeDotExponent D₀) m
  let R := SuperBimodule.regular
    (heightParity D₀ (parameterTwist D₀ Sc₀) a (probePolynomial_parity D₀ m) v.length)
  ⟨probeOldModule D₀ m (parameterTwist D₀ Sc₀) v R,
    probeOldModule_evaluatesCoefficients D₀ m (parameterTwist D₀ Sc₀) v R⟩

private abbrev check (D₀ : SKM.Datum Bool (Bool → ℤ)) (Sc₀ : SKM.Scalars D₀ ℚ)
    (v : List Bool) (i j l : Bool) (hb : ¬ (i = l ∧ i ≠ j)) :=
  probeStoredBraid D₀ Sc₀ m v i j l (one v i) (one v j) (one v l)
    (pair v i j) (pairRev v i j) (pair v i l) (pairRev v i l)
    (pair v j l) (pairRev v j l) (topL v i j l) (topJ v i j l) (topI v i j l) hb (N D₀ Sc₀ v)

-- Connected mixed even/odd adjacent repeats; every representative is append-indexed.
example := check D Sc [false,true] false false true (by decide)
example := check D Sc [false,true] false true true (by decide)
example := check D Sc [false,true] true true false (by decide)
example := check D Sc [false,true] true false false (by decide)
example (i : Bool) := check D Sc [] i i i (by simp)
-- Two odd colours test both possible adjacent repeats and the negative equal crossing.
example := check AsymmetricParameters.datum AsymmetricParameters.scalars
  [false,true] false false true (by decide)
example := check AsymmetricParameters.datum AsymmetricParameters.scalars
  [false,true] false true true (by decide)

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


example := check D interiorSc [false,true] true true false (by decide)
example := check D interiorSc [false,true] true false false (by decide)
example := check D interiorSc [] true true false (by decide)

private abbrev actingSc := parameterTwist D interiorSc
private abbrev actualSource :=
  (probeEvaluatedAppendTo D actingSc m [true,false] true [true,true,false]
    (topI [] true true false)).obj
    ((probeEvaluatedAppendTo D actingSc m [false] true [true,false]
      (pairRev [] true false)).obj
      ((probeEvaluatedAppendTo D actingSc m [] false [false] (one [] false)).obj
        (N D interiorSc [])))
private abbrev actualTarget :=
  (probeEvaluatedAppendTo D actingSc m [true,true] false [true,true,false]
    (topL [] true true false)).obj
    ((probeEvaluatedAppendTo D actingSc m [true] true [true,true] (pair [] true true)).obj
      ((probeEvaluatedAppendTo D actingSc m [] true [true] (one [] true)).obj
        (N D interiorSc [])))

/-- The two actual three-crossing operators agree on every output coordinate and vector. -/
example (w : OldContentCategory D actingSc (probeCutoff D m) [true,true,false])
    (z : actualSource.obj.obj w) :=
  congrArg (fun f : actualSource ⟶ actualTarget => f.hom.total w z)
    (check D interiorSc [] true true false (by decide))

-- This is a nonzero vector in the actual regular probe input used by the empty-base test.
example : (show (N D interiorSc []).obj.obj
    (probeOldVacuumObject D (parameterTwist D interiorSc) m) from
      probeOldVacuumVector D (parameterTwist D interiorSc) m) ≠ 0 :=
  probeOldVacuumVector_ne_zero D (parameterTwist D interiorSc) m
example (i : Bool) : probeOldVacuumAppendVector D interiorSc m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D interiorSc m i (by cases i <;> decide)

end ProbeEvaluatedStoredBraidConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVInductionBraidCube,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbeStoredBraid,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedStoredBraid] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
