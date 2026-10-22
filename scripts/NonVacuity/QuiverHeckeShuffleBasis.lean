import OddMath

/-! # Consumers of the shuffle basis (Hill–Wang, Proposition 6.4) -/

noncomputable section
open OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples

/-- Three strands split as `1 + 2`: the shuffle elements are a basis of the Hom space. -/
example : Module.Basis (ShIdx (t := [0, 1, 0]) (u' := [1]) (v' := [0, 0]) rfl) ℚ
    ((pres datum scalars).obj (ob datum [0, 1, 0]) ⟶
      (pres datum scalars).obj (ob datum ([1] ++ [0, 0]))) :=
  shuffleBasis datum scalars rfl

/-- No shuffle element vanishes. -/
example (x : ShIdx (t := [0, 1, 0]) (u' := [1]) (v' := [0, 0]) rfl) :
    shElt datum scalars x ≠ 0 := by
  rw [← shuffleBasis_apply]
  exact (shuffleBasis datum scalars rfl).ne_zero x

#print axioms OddMath.QuiverHecke.shuffleBasis
