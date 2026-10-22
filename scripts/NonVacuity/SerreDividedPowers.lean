import OddMath

/-! # BE2 Lemma 11.6, positive Serre relation, on a rank-two datum

The datum of `scripts/NonVacuity/SerreClass.lean` (type `B₂`, `true` odd, `d_{true,false} = 2`,
`d_{false,true} = 1`) with the symmetrizer `d_true = 1`, `d_false = 2`, at the weight `0`. Both
orders of the two colours are exercised: an odd colour with `M = 3` and an even one with `M = 2`.
-/

noncomputable section
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.SerreComplex

namespace NonVacuity.SerreDividedPowers

/-- A rank-two datum: `true` is odd, `a_{true,false} = -2`, `a_{false,true} = -1`. -/
def datum : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else if i then -2 else -1
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by
        cases i <;> cases j <;> simp_all [CartanDatum.cartanMatrix_apply]
      zero_comm := fun i j => by
        cases i <;> cases j <;> simp [CartanDatum.cartanMatrix_apply] }
  parity := fun i => if i then 1 else 0
  even_of_odd := by
    intro i j hi
    cases i
    · simp at hi
    · cases j <;> simp

def scalars : SKM.Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

theorem dn_true_false : datum.dn true false = 2 := by decide

theorem dn_false_true : datum.dn false true = 1 := by decide

def symmetrizer : SKM.Symmetrizer datum where
  d := fun i => if i then 1 else 2
  pos := fun i => by cases i <;> decide
  symm := by
    intro i j
    cases i <;> cases j <;> simp [SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, datum]

theorem homogeneous : scalars.Homogeneous := fun _ _ _ _ _ _ _ _ h => absurd rfl h

/-- `i` odd, `M = 3`. -/
example := serre_E (i := true) (j := false) (M := 3) symmetrizer homogeneous 0 (by decide)
  (by rw [dn_true_false])

/-- `i` even, `M = 2`. -/
example := serre_E (i := false) (j := true) (M := 2) symmetrizer homogeneous 0 (by decide)
  (by rw [dn_false_true])

#print axioms OddMath.QuiverHecke.SerreComplex.serre_E

end NonVacuity.SerreDividedPowers
