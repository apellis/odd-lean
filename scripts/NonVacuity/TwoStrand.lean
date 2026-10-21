import OddMath

/-! Non-vacuity checks in `NonVacuity.TwoStrand`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.TwoStrand

open CategoryTheory CategoryTheory.Limits StringDiagrams OddMath.SKM
open OddMath.SKM.TwoStrand

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

def symmetrizer : Symmetrizer datum where
  d := fun _ => 1
  pos := fun _ => one_pos
  symm := fun _ _ => rfl

noncomputable def splitting (ν : ℤ) :
    whole scalars symmetrizer homogeneous () ν ≅
      raw scalars symmetrizer homogeneous () ν rfl 0 ⊞
        raw scalars symmetrizer homogeneous () ν rfl 2 :=
  decomposition scalars symmetrizer homogeneous () ν rfl

theorem crossing_projection (ν : ℤ) :
    ((proj1 scalars symmetrizer homogeneous () ν rfl).f PUnit.unit PUnit.unit).val.val =
      t scalars symmetrizer homogeneous () ν := rfl

theorem dot_inclusion (ν : ℤ) :
    ((incl1 scalars symmetrizer homogeneous () ν rfl).f PUnit.unit PUnit.unit).val.val =
      xl scalars symmetrizer homogeneous () ν * e scalars symmetrizer homogeneous () ν := rfl

theorem inverse_equations (ν : ℤ) :
    (splitting ν).hom ≫ (splitting ν).inv = 𝟙 _ ∧
      (splitting ν).inv ≫ (splitting ν).hom = 𝟙 _ :=
  ⟨(splitting ν).hom_inv_id, (splitting ν).inv_hom_id⟩

end NonVacuity.TwoStrand
