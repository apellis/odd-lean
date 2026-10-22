import OddMath

/-! # Consumers of the basis theorem for `H_n` -/

noncomputable section
open OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples

/-- Mixed parities, three strands: the normal-form matrix entries are a basis of `H_3`. -/
example : Module.Basis (HnIdx ℕ 3) ℚ (Hn datum scalars 3) := Hn.basis datum scalars 3

/-- No basis element of `H_3` vanishes. -/
example (a b : Word ℕ 3) (i : NFIdx b.val a.val) :
    Hn.single (D := datum) (Sc := scalars) a b i.nf ≠ 0 := by
  rw [← Hn.basis_apply]
  exact (Hn.basis datum scalars 3).ne_zero _

#print axioms OddMath.QuiverHecke.Hn.basis
#print axioms OddMath.QuiverHecke.Hn.basis_apply
