import OddMath

/-! # Consumers of the basis theorem for the quiver Hecke supercategory -/

noncomputable section
open OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples

/-- Mixed parities and three strands: the normal forms are a basis of the Hom space. -/
example : Module.Basis (NFIdx [0, 1, 0] [1, 0, 0]) ℚ
    ((pres datum scalars).obj (ob datum [0, 1, 0]) ⟶
      (pres datum scalars).obj (ob datum [1, 0, 0])) :=
  basisNF datum scalars [0, 1, 0] [1, 0, 0]

/-- No normal form vanishes. -/
example (i : NFIdx [0, 1, 0] [1, 0, 0]) :
    i.nf (D := datum) (Sc := scalars) ≠ 0 := by
  rw [← basisNF_apply]
  exact (basisNF datum scalars _ _).ne_zero i

#print axioms OddMath.QuiverHecke.linearIndependent_nf
#print axioms OddMath.QuiverHecke.basisNF
