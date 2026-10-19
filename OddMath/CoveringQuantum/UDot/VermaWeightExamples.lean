/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.VermaWeights

/-!
# Weight projections with infinitely many even colours

An orthogonal datum on `ℕ` has symmetrizer one and even parity, hence is not
bar-consistent. Its weight projections preserve the Serre ideal, including a
relation with nonempty words on both sides. The matching projection fixes this
free-algebra element and a different projection kills it. No assertion of
nonzero image in the Serre quotient is made.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.VermaWeightExamples
open PreF

/-- Countably many orthogonal even roots in the finitely supported weight group. -/
def datum : RootDatum ℕ (ℕ →₀ ℤ) where
  a i j := if i = j then 2 else 0
  isGCM := {
    diag := by intro i; simp
    offDiag_nonpos := by intro i j hij; simp [hij]
    zero_comm := by intro i j; simp [eq_comm] }
  d _ := 1
  d_pos _ := by decide
  d_mul_symm := by intro i j; simp [eq_comm]
  parity _ := 0
  even_of_odd := by intro i j h; exact (zero_ne_one h).elim
  cd := {
    root := fun i ↦ (2 : ℤ) • Finsupp.single i 1
    coroot := fun i ↦ Finsupp.lapply i
    coroot_root_self := by intro i; simp }
  coroot_root := by intro i j; simp [Finsupp.single_apply, eq_comm]

/-- The ambient colour type is infinite, not a finite subtype. -/
theorem infinite_colours : Infinite ℕ := inferInstance

/-- The all-even datum with odd symmetrizer is not bar-consistent. -/
theorem not_barConsistent : ¬ datum.toSuperCartanDatum.BarConsistent := by
  intro h
  have h0 := h 0
  norm_num [datum] at h0

variable {k : Type*} [CommRing k] (q : kˣ) (π : k)

/-- A Serre generator with nonempty words on both sides. -/
def contextualRelation : PreF k ℕ :=
  monomial k [2, 0] * datum.serreElt q π 0 1 * monomial k [1, 3]

/-- Its weight in the given weight group. -/
def contextualWeight : ℕ →₀ ℤ :=
  halfWeight datum true (wordWeight [2, 0]) +
    (datum.serreDeg 0 1 • datum.α 0 + datum.α 1) +
      halfWeight datum true (wordWeight [1, 3])

/-- Membership uses both sides of the two-sided Serre ideal. -/
theorem contextualRelation_mem_serreIdeal :
    contextualRelation q π ∈ datum.serreIdeal q π := by
  apply TwoSidedIdeal.mul_mem_right
  apply TwoSidedIdeal.mul_mem_left
  exact (datum.mem_serreIdeal q π _).mpr
    (datum.toSerreF_serreElt q π (by decide : (0 : ℕ) ≠ 1))

/-- Projection preservation in a genuinely infinite, non-bar-consistent example. -/
theorem contextual_projection_mem (Λ μ : ℕ →₀ ℤ) :
    weightProjectFree datum Λ μ (contextualRelation q π) ∈ datum.serreIdeal q π :=
  weightProjectFree_mem_serreIdeal datum q π Λ μ (contextualRelation_mem_serreIdeal q π)

private theorem contextual_grading :
    rootGrading datum (contextualRelation q π) =
      AddMonoidAlgebra.single contextualWeight (contextualRelation q π) := by
  simp only [contextualRelation, map_mul, rootGrading_monomial, rootGrading_serreElt,
    AddMonoidAlgebra.single_mul_single, contextualWeight]

/-- Projection to the matching module weight fixes the free relation in context. -/
theorem contextual_projection_matching (Λ : ℕ →₀ ℤ) :
    weightProjectFree datum Λ (Λ - contextualWeight) (contextualRelation q π) =
      contextualRelation q π := by
  simp [weightProjectFree, contextual_grading]

/-- A distinct projected module weight kills the same free relation in context. -/
theorem contextual_projection_other (Λ : ℕ →₀ ℤ) :
    weightProjectFree datum Λ (Λ - (contextualWeight + Finsupp.single 4 1))
      (contextualRelation q π) = 0 := by
  simp [weightProjectFree, contextual_grading]

end OddMath.CoveringQuantum.UDot.VermaWeightExamples
