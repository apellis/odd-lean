/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.RegularCoefficientBound
import StringDiagrams.Super.KrullSchmidtExamples

/-! The rational regular bimodule is nonzero and has coefficient bound one. This tests
construction of the coefficient grading and its bound, rather than supplying them as
hypotheses. It does not claim a nonzero positive coefficient in the rational algebra. -/

noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct
open OddMath.QuiverHecke.SwappedAssembly
open RegularReservoir ProbeWindow

namespace RegularCoefficientBoundConsumer

def rationalReservoir : GSuperAlg ℚ where
  carrier := ℚ
  grading := KrullSchmidtExamples.rationalGradedAlgebra.parity
  degree := KrullSchmidtExamples.rationalGradedAlgebra.degree
  decompose_mem := KrullSchmidtExamples.rationalGradedAlgebra.decompose_mem

lemma support_bound (n : ℤ) (hn : (1 : ℤ) ≤ n) : rationalReservoir.degree n = ⊥ := by
  change UnitSupercat.trivialDegree ℚ n = ⊥
  simp [UnitSupercat.trivialDegree, show n ≠ 0 by omega]

example (n : ℤ) (hn : (1 : ℤ) ≤ n)
    (c : 𝟙 rationalReservoir.toSuperAlg ⟶ 𝟙 rationalReservoir.toSuperAlg)
    (hc : c ∈ (coeffGrading rationalReservoir).deg n) : c = 0 :=
  coefficient_eq_zero rationalReservoir 1 support_bound n hn c hc

example : (𝟙 (𝟙 rationalReservoir.toSuperAlg) :
    𝟙 rationalReservoir.toSuperAlg ⟶ 𝟙 rationalReservoir.toSuperAlg) ≠ 0 := by
  intro h
  have h' := congrArg (fun f => f.1 (1 : ℚ)) h
  change (1 : ℚ) = 0 at h'
  exact one_ne_zero h'

example : (𝟙 (𝟙 rationalReservoir.toSuperAlg) :
    𝟙 rationalReservoir.toSuperAlg ⟶ 𝟙 rationalReservoir.toSuperAlg) ∈
    (coeffGrading rationalReservoir).deg 0 :=
  (mem_coeffGrading_iff rationalReservoir 0 _).mpr SetLike.GradedOne.one_mem

example (T : SuperAlg ℚ) {X Y : Mat_ (T ⟶ rationalReservoir.toSuperAlg)}
    (F G : X ⟶ Y) [IsIso G]
    (h : ∀ i j, (F - G) i j ∈ coeffIdeal (coeffGrading rationalReservoir) 1 _ _) : IsIso F :=
  isIso_of_coefficient_error rationalReservoir T 1 support_bound F G h

#print axioms RegularReservoir.coefficient_eq_zero
#print axioms RegularReservoir.mem_coeffGrading_iff
#print axioms RegularReservoir.closure_mem_coefficientIdeal
#print axioms RegularReservoir.isIso_of_coefficient_error

end RegularCoefficientBoundConsumer
