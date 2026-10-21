/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.MatrixGrading
import StringDiagrams.Super.SOp

/-! Finite-support Hom matrices of the super-opposite category realize the super-opposite algebra. -/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams
namespace OddMath.FiniteHomMatrix
universe u v w t
variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
  [Preadditive C] [Linear k C] [Supercategory k C] {J : Type t} {obj : J → C}

/-- Transpose a super-opposite matrix and remove `sop` from each entry. -/
def unsopLinear : Mat (fun i => SOp.mk (R := k) (obj i)) →ₗ[k] Mat obj :=
  DFinsupp.lsum k fun p =>
    (DFinsupp.lsingle (p.2,p.1)).comp (SOp.unsopₗ _ _)

/-- Transpose a matrix and put each entry in the super-opposite category. -/
def sopLinear : Mat obj →ₗ[k] Mat (fun i => SOp.mk (R := k) (obj i)) :=
  DFinsupp.lsum k fun p => (DFinsupp.lsingle (p.2,p.1)).comp
    ({ toFun := SOp.sop
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } :
      (obj p.2 ⟶ obj p.1) →ₗ[k]
        ((SOp.mk (obj p.1) : SOp k C) ⟶ SOp.mk (obj p.2)))

@[simp] theorem unsopLinear_single (i j : J)
    (f : (SOp.mk (obj j) : SOp k C) ⟶ SOp.mk (obj i)) :
    unsopLinear (single i j f) = single j i (SOp.unsop f) := by
  simp [unsopLinear, single, SOp.unsopₗ]

@[simp] theorem sopLinear_single (i j : J) (f : obj j ⟶ obj i) :
    sopLinear (k := k) (single i j f) =
      single (obj := fun i => SOp.mk (R := k) (obj i)) j i (SOp.sop f) := by
  simp [sopLinear, single]

@[simp] theorem unsopLinear_sopLinear (a : Mat obj) :
    unsopLinear (sopLinear (k := k) a) = a := by
  induction a using induction with
  | hz => simp
  | ha a b ha hb => simp [ha, hb]
  | hs i j f => simp

@[simp] theorem sopLinear_unsopLinear (a : Mat (fun i => SOp.mk (R := k) (obj i))) :
    sopLinear (unsopLinear a) = a := by
  induction a using induction with
  | hz => simp
  | ha a b ha hb => simp [ha, hb]
  | hs i j f => simp

/-- The underlying linear identification with the super-opposite algebra. -/
def unsopEquiv : Mat (fun i => SOp.mk (R := k) (obj i)) ≃ₗ[k] Mat obj where
  toLinearMap := unsopLinear
  invFun := sopLinear
  left_inv := sopLinear_unsopLinear
  right_inv := unsopLinear_sopLinear

/-- Reversed multiplication acquires exactly the Koszul sign. -/
theorem unsopLinear_mul {p q : ZMod 2}
    {a b : Mat (fun i => SOp.mk (R := k) (obj i))}
    (ha : ∀ r, SOp.unsop (a r) ∈ Supercategory.parity (R := k) (obj r.1) (obj r.2) p)
    (hb : ∀ r, SOp.unsop (b r) ∈ Supercategory.parity (R := k) (obj r.1) (obj r.2) q) :
    unsopLinear (a * b) = Supercategory.sign k (p * q) • (unsopLinear b * unsopLinear a) := by
  rw [eq_sum_single a, eq_sum_single b]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  obtain ⟨i,j⟩ := r
  obtain ⟨l,m⟩ := s
  by_cases h : m = i
  · subst i
    simp only [single_mul_single, unsopLinear_single]
    rw [SOp.comp_of_mem (hb (m,j)) (ha (l,m))]
    simp [single, DFinsupp.single_smul, mul_comm]
  · simp [h, Ne.symm h]

end OddMath.FiniteHomMatrix
