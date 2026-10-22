import OddMath

/-! # Endomorphisms of divided-power projectives in degrees `≤ 0` (input to BE2 Theorem 11.3)

The rank-two datum of `scripts/NonVacuity/SerreClass.lean` (`true` odd, `false` even), over `ℚ`.
The corner statements are applied to the identity of `iʳ` (degree `0`), for an even colour with
`r = 3` and an odd colour with `r = 4` and `r = 1`.
-/

noncomputable section
open OddMath OddMath.QuiverHecke

namespace NonVacuity.DividedPowerCorner

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

/-- Even colour, `r = 3`. -/
example := evenCornerProjector_mul_mul_mem datum scalars symmetrizer false (by decide) 3
  homogeneous le_rfl (one_mem_cornerDeg datum scalars (gdeg datum symmetrizer) false 3)

/-- Odd colour, `r = 4`. -/
example := oddCornerProjector_mul_mul_mem datum scalars symmetrizer true (by decide)
  homogeneous 4 le_rfl (one_mem_cornerDeg datum scalars (gdeg datum symmetrizer) true 4)

/-- Odd colour, `r = 1`. -/
example := oddCornerProjector_mul_mul_mem datum scalars symmetrizer true (by decide)
  homogeneous 1 le_rfl (one_mem_cornerDeg datum scalars (gdeg datum symmetrizer) true 1)

end NonVacuity.DividedPowerCorner

#print axioms OddMath.QuiverHecke.evenCornerProjector_mul_mul_mem
#print axioms OddMath.QuiverHecke.oddCornerProjector_mul_mul_mem
