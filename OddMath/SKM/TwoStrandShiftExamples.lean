/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.TwoStrandShifts

/-! Concrete integral even rank-one consumers of both shift directions and the splitting. -/

noncomputable section

namespace TwoStrandShiftConsumer

open CategoryTheory CategoryTheory.Limits StringDiagrams OddMath.SKM
open OddMath.SKM.TwoStrand

/-- The even rank-one datum on integral weights. -/
def datum : Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 0
  even_of_odd := fun _ _ _ => even_two

/-- The integral coefficient ring needs no inverse of two in the even case. -/
def scalars : Scalars datum ℤ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by
    rintro ⟨i, hi⟩
    exact (zero_ne_one hi).elim

theorem homogeneous : scalars.Homogeneous := fun _ _ _ _ _ _ _ _ h => absurd rfl h

/-- Unit symmetrizer. -/
def symmetrizer : Symmetrizer datum where
  d := fun _ => 1
  pos := fun _ => one_pos
  symm := fun _ _ => rfl


/-- Positive exponent two in the existing Q equivalence. -/
def positiveShift (ν : ℤ) :=
  qPowRawIso scalars symmetrizer homogeneous () ν rfl 2 0

/-- Negative exponent three uses the actual inverse Q equivalence. -/
def negativeShift (ν : ℤ) :=
  qPowRawIso scalars symmetrizer homogeneous () ν rfl (-3) 0

/-- Both inverse equations at positive shift. -/
theorem positive_inverse_equations (ν : ℤ) :
    (positiveShift ν).hom ≫ (positiveShift ν).inv = 𝟙 _ ∧
      (positiveShift ν).inv ≫ (positiveShift ν).hom = 𝟙 _ :=
  ⟨(positiveShift ν).hom_inv_id, (positiveShift ν).inv_hom_id⟩

/-- Both inverse equations at negative shift. -/
theorem negative_inverse_equations (ν : ℤ) :
    (negativeShift ν).hom ≫ (negativeShift ν).inv = 𝟙 _ ∧
      (negativeShift ν).inv ≫ (negativeShift ν).hom = 𝟙 _ :=
  ⟨(negativeShift ν).hom_inv_id, (negativeShift ν).inv_hom_id⟩

/-- The transported two-strand splitting has both inverse laws. -/
theorem splitting_inverse_equations (ν : ℤ) :
    (qDecomposition scalars symmetrizer homogeneous () ν rfl).hom ≫
      (qDecomposition scalars symmetrizer homogeneous () ν rfl).inv = 𝟙 _ ∧
    (qDecomposition scalars symmetrizer homogeneous () ν rfl).inv ≫
      (qDecomposition scalars symmetrizer homogeneous () ν rfl).hom = 𝟙 _ :=
  ⟨(qDecomposition scalars symmetrizer homogeneous () ν rfl).hom_inv_id,
    (qDecomposition scalars symmetrizer homogeneous () ν rfl).inv_hom_id⟩

end TwoStrandShiftConsumer
