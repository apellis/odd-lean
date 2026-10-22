import OddMath

/-! # BE2 Lemma 11.5 in the Grothendieck ring, on a rank-two datum

The datum of `scripts/NonVacuity/SerreDividedPowers.lean` (type `B₂`, `true` odd) with the
symmetrizer `d_true = 1`, `d_false = 2`, at the weight `0`: both class equations for an odd and an
even colour, with three strands.
-/

noncomputable section
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.SerreComplex

namespace NonVacuity.GrothendieckDividedPowers

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

def symmetrizer : SKM.Symmetrizer datum where
  d := fun i => if i then 1 else 2
  pos := fun i => by cases i <;> decide
  symm := by
    intro i j
    cases i <;> cases j <;> simp [SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, datum]

theorem homogeneous : scalars.Homogeneous := fun _ _ _ _ _ _ _ _ h => absurd rfl h

/-- `E_i^{(3)}`, `i` odd. -/
example := cls_power_eq_dividedPower symmetrizer homogeneous true 3 (0 : Bool → ℤ)

/-- `E_i^{(3)}`, `i` even. -/
example := cls_power_eq_dividedPower symmetrizer homogeneous false 3 (0 : Bool → ℤ)

/-- `F_i^{(3)}`, `i` odd. -/
example := cls_power_eq_dividedPower_down symmetrizer homogeneous true 3 (0 : Bool → ℤ)

/-- `F_i^{(3)}`, `i` even. -/
example := cls_power_eq_dividedPower_down symmetrizer homogeneous false 3 (0 : Bool → ℤ)

#print axioms OddMath.QuiverHecke.SerreComplex.cls_power_eq_dividedPower
#print axioms OddMath.QuiverHecke.SerreComplex.cls_power_eq_dividedPower_down

end NonVacuity.GrothendieckDividedPowers
