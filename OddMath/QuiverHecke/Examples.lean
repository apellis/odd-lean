/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.OddNilHecke
import OddMath.QuiverHecke.LabelRelations

/-! Concrete odd rank-one consumers of the independent quiver Hecke presentation. -/
noncomputable section
namespace OddMath.QuiverHecke.Examples
open CategoryTheory StringDiagrams

/-- The odd rank-one Cartan datum. -/
def datum : SKM.Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two

/-- Rational parameters; two is invertible, as required for an odd colour. -/
def scalars : SKM.Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

theorem homogeneous : scalars.Homogeneous := fun _ _ _ _ _ _ _ _ h => absurd rfl h

def symmetrizer : SKM.Symmetrizer datum where
  d := fun _ => 1
  pos := fun _ => one_pos
  symm := fun _ _ => rfl

example : MonoidalSupercategory ℚ (H datum scalars) := inferInstance
example : GradedSupercategory ℚ (H datum scalars) :=
  gradedSupercategory datum symmetrizer scalars homogeneous
example : letI := gradedSupercategory datum symmetrizer scalars homogeneous
    GradedMonoidalSupercategory ℚ (H datum scalars) :=
  gradedMonoidalSupercategory datum symmetrizer scalars homogeneous
example : gdeg datum symmetrizer (.dot ()) = 2 := rfl
example : gdeg datum symmetrizer (.cross () ()) = -2 := rfl
example : (Shape.dot ()).parity datum = 1 := rfl
example : (Shape.cross () ()).parity datum = 1 := rfl
example : (pres datum scalars).lin (relation datum scalars (.quadEq ())) = 0 :=
  (pres datum scalars).lin_rel_self _
example : Diagrams.OddNilHecke.ONH ℚ ⥤ H datum scalars :=
  oddFunctor datum scalars () rfl
example (n : ℕ) : Frontier.NilHeckeAction.Presented n →+* Corner datum scalars () (n + 2) :=
  oddNilHecke datum scalars () rfl n
example (n : ℕ) : oddNilHecke datum scalars () rfl n 1 = 1 :=
  (oddNilHecke datum scalars () rfl n).map_one

#print axioms isParityHomogeneous
#print axioms isHomogeneous_gdeg
#print axioms gradedMonoidalSupercategory
#print axioms oddColour_rel
#print axioms oddFunctor
#print axioms oddNilHecke
#print axioms label_rel

end OddMath.QuiverHecke.Examples
