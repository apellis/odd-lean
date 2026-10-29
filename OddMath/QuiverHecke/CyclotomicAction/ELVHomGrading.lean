/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleELVGrading
import OddMath.SKM.BubbleELVPolynomialGrading
import OddMath.QuiverHecke.Grading
import OddMath.QuiverHecke.CyclotomicAction.ELVOldCyclotomicTarget
import StringDiagrams.Super.BoxProductGraded

/-! # Integer grading of the ELV coefficient diagram category

The full coefficient quotient retains exterior parity independently of integer
 degree. The affine relations use `Sc.Homogeneous`. The first-position
cyclotomic relations have their prescribed symmetrizer degree. This supplies
Hom gradings for the coefficient action in `DeformedGradedAction.md`; it does
not assert bounded support at positive strand content.
-/

noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous) (cutoff : I → ℕ)

/-- Integer grading on the coefficient one-object category, with its existing parity. -/
@[instance_reducible]
def elvCoefficientCategoryGrading : GradedSupercategory k
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := k) D cutoff)) :=
  SuperalgebraCat.instGradedSupercategory (SKM.SYM.elvCoefficientGSuperAlg D sy cutoff).gsa

/-- The full coefficient diagram category has the tensor-sum integer grading. -/
@[instance_reducible]
def elvHomGrading : GradedSupercategory k (ELVCoefficientCategory D Sc cutoff) := by
  letI := elvCoefficientCategoryGrading (k := k) D sy cutoff
  letI := gradedSupercategory D sy Sc hc
  exact BoxProd.instGradedSupercategory

/-- The integer homogeneous parts of the existing coefficient quotient Homs. -/
abbrev elvHomDegree (v w : List I) (n : ℤ) : Submodule k (ELVOld.hom D Sc cutoff v w) :=
  letI := elvHomGrading D sy Sc hc cutoff
  GradedSupercategory.degree (R := k) (ELVOld.obj D Sc cutoff v) (ELVOld.obj D Sc cutoff w) n

/-- These parts form a direct sum, not merely a filtration. -/
theorem elvHomDegree_internal (v w : List I) :
    DirectSum.IsInternal (elvHomDegree D sy Sc hc cutoff v w) :=
by
  let _ := elvHomGrading D sy Sc hc cutoff
  exact GradedSupercategory.isInternal_degree _ _

/-- A coefficient and an affine diagram contribute additively to integer degree. -/
theorem elvQuotientMap_source_mem_degree {v w : List I} {a : SKM.SYM D k}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)} {r s : ℤ}
    (ha : a ∈ SKM.SYM.coefficientDegreePart D k sy r)
    (hf : f ∈ homDegree D sy Sc v w s) :
    elvQuotientMap D Sc cutoff _ _ (sourceCoefficientHom D Sc a f) ∈
      elvHomDegree D sy Sc hc cutoff v w (r + s) := by
  rw [elvQuotientMap_source]
  let _ := elvCoefficientCategoryGrading (k := k) D sy cutoff
  let _ := gradedSupercategory D sy Sc hc
  exact BoxProd.tmulHom_mem_degree (X := ELVOld.obj D Sc cutoff v)
    (Y := ELVOld.obj D Sc cutoff w) (Submodule.mem_map_of_mem ha) hf

/-- Dot powers on a nonempty word have their affine symmetrizer degree. -/
theorem firstDotPower_mem_gdeg (j : I) (v : List I) (n : ℕ) :
    firstDotPower D Sc (j :: v) n ∈ homDegree D sy Sc (j :: v) (j :: v)
      (2 * sy.d j * n) := by
  apply Presentation.diag_mem_homDeg'
  rw [degree_gdeg_mkD]
  simp only [List.map_replicate]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, pl_cons, PG.ld, PG.act, List.drop_zero,
      List.take_zero, List.singleton_append, List.map_cons, List.sum_cons]
    rw [ih]
    simp only [gdeg, Nat.cast_add, Nat.cast_one]
    ring

/-- A coefficient polynomial with complementary coefficient degrees is homogeneous. -/
theorem deformedCyclotomic_mem_elvHomDegree (j : I) (v : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k)
    (hcoeff : ∀ a, c a ∈ SKM.SYM.coefficientDegreePart D k sy
      (2 * sy.d j * ((N : ℤ) - a.val))) :
    (elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (j :: v) N c) ∈
      elvHomDegree D sy Sc hc cutoff (j :: v) (j :: v) (2 * sy.d j * N) := by
  change elvQuotientMap D Sc cutoff _ _ _ ∈ _
  unfold deformedCyclotomic
  rw [map_sum]
  apply Submodule.sum_mem
  intro a _
  have h := elvQuotientMap_source_mem_degree D sy Sc hc cutoff (hcoeff a)
    (firstDotPower_mem_gdeg D sy Sc j v a.val)
  have he : 2 * sy.d j * ((N : ℤ) - a.val) + 2 * sy.d j * a.val =
      2 * sy.d j * N := by ring
  rw [he] at h
  exact h

/-- Both parity cases of the first-position cyclotomic relation have degree
`2 d_j cutoff_j`, with the original exterior coefficients. -/
theorem ELVOld.relation_mem_degree (j : I) (v : List I) :
    ELVOld.relation D Sc cutoff j v ∈
      elvHomDegree D sy Sc hc cutoff (j :: v) (j :: v) (2 * sy.d j * cutoff j) := by
  unfold ELVOld.relation
  split_ifs with hj
  · exact deformedCyclotomic_mem_elvHomDegree D sy Sc hc cutoff j v (cutoff j) _
      (SKM.SYM.elvMonicCoefficient_mem_coefficientDegreePart D k sy ⟨j, hj⟩ (cutoff j))
  · have he : D.parity j = 0 := (Supercategory.parity_eq_zero_or_one (D.parity j)).resolve_right hj
    exact deformedCyclotomic_mem_elvHomDegree D sy Sc hc cutoff j v (cutoff j) _
      (SKM.SYM.evenMonicCoefficient_mem_coefficientDegreePart D k sy j he (cutoff j))

end OddMath.QuiverHecke
