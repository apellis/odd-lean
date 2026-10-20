/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.SerreDeriv
import OddMath.CoveringQuantum.Coefficients

/-!
# Infinite-colour Serre-ideal derivative examples

The orthogonal all-even datum on `ℕ`, with symmetrizer one, is not bar consistent.
Both skew derivatives preserve its Serre ideal over the generic covering ring,
including a relation in a nonempty left and right word context. This exercises
the ideal descent used for the lowering operators, not nondegeneracy or a
construction of the modified form of Brundan–Ellis Theorem 10.3.
-/

noncomputable section

namespace OddMath.CoveringQuantum.SerreDerivExamples

/-- Countably many orthogonal even simple roots with symmetrizer one. -/
def orthogonalEven : SuperCartanDatum ℕ where
  a i j := if i = j then 2 else 0
  isGCM := {
    diag := fun i ↦ by simp
    offDiag_nonpos := fun i j hij ↦ by simp [hij]
    zero_comm := fun i j ↦ by simp [eq_comm] }
  d _ := 1
  d_pos _ := by decide
  d_mul_symm i j := by simp [eq_comm]
  parity _ := 0
  even_of_odd _ _ h := by simp at h

/-- This datum fails the parity condition on its symmetrizer. -/
theorem orthogonalEven_not_barConsistent : ¬ orthogonalEven.BarConsistent := by
  intro h
  have h0 := h 0
  norm_num [orthogonalEven] at h0

/-- The ambient colour type is infinite, rather than a finite subtype. -/
theorem infinite_colours : Infinite ℕ := inferInstance

open Coefficients

/-- A two-colour Serre relation between nonempty words on other colours. -/
def contextualRelation : PreF Coefficients.Ring ℕ :=
  PreF.monomial Coefficients.Ring [2, 3] *
    orthogonalEven.serreElt Coefficients.q pi 0 1 *
      PreF.monomial Coefficients.Ring [4, 5]

/-- The contextual relation lies in the actual presentation ideal. -/
theorem contextualRelation_mem :
    contextualRelation ∈ orthogonalEven.serreIdeal Coefficients.q pi := by
  apply TwoSidedIdeal.mul_mem_right
  apply TwoSidedIdeal.mul_mem_left
  exact (orthogonalEven.mem_serreIdeal Coefficients.q pi _).mpr
    (orthogonalEven.toSerreF_serreElt Coefficients.q pi (by decide : (0 : ℕ) ≠ 1))

/-- Right differentiation is valid at every colour of the infinite datum. -/
theorem rDeriv_contextualRelation (i : ℕ) :
    PreF.rDeriv (orthogonalEven.chi Coefficients.q pi) i contextualRelation ∈
      orthogonalEven.serreIdeal Coefficients.q pi :=
  orthogonalEven.rDeriv_mem_serreIdeal Coefficients.q pi pi_sq i contextualRelation_mem

/-- Left differentiation is valid at every colour of the infinite datum. -/
theorem lDeriv_contextualRelation (i : ℕ) :
    PreF.lDeriv (orthogonalEven.chi Coefficients.q pi) i contextualRelation ∈
      orthogonalEven.serreIdeal Coefficients.q pi :=
  orthogonalEven.lDeriv_mem_serreIdeal Coefficients.q pi pi_sq i contextualRelation_mem

end OddMath.CoveringQuantum.SerreDerivExamples
