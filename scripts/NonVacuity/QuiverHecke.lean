import OddMath

/-! BE2 §11: concrete rational odd rank-one quiver Hecke category and same-colour map. -/
noncomputable section
open CategoryTheory StringDiagrams OddMath
open QuiverHecke QuiverHecke.Examples

example : MonoidalSupercategory ℚ (H datum scalars) := inferInstance
example : GradedSupercategory ℚ (H datum scalars) :=
  gradedSupercategory datum symmetrizer scalars homogeneous
example : letI := gradedSupercategory datum symmetrizer scalars homogeneous
    GradedMonoidalSupercategory ℚ (H datum scalars) :=
  gradedMonoidalSupercategory datum symmetrizer scalars homogeneous
example (a b : Frontier.NilHeckeAction.Presented 1) :
    oddNilHecke datum scalars () rfl 1 (a * b) =
      oddNilHecke datum scalars () rfl 1 a * oddNilHecke datum scalars () rfl 1 b :=
  (oddNilHecke datum scalars () rfl 1).map_mul a b

#print axioms QuiverHecke.gradedMonoidalSupercategory
#print axioms QuiverHecke.oddNilHecke
