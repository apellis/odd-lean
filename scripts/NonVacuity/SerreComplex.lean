import OddMath

/-! # BE2 Proposition 11.2 on a rank-two datum with an odd colour

The colours are `true` (odd) and `false` (even), with `d_{true,false} = 2` and
`d_{false,true} = 1` (a Cartan matrix of type `B₂`, with the odd colour on the root for which
(1.4) asks `d` to be even). Scalars over `ℚ`: all `tᵢⱼ = 1`, `sᵢⱼ^{pq} = 0`. Both orders of the
two colours are exercised: `i` odd with `M = 3`, and `i` even with `M = 2`.
-/

noncomputable section
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.SerreComplex

namespace NonVacuity.SerreComplex

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

/-- `i` odd, `M = 3`: the Serre complex on `i^a j i^{3-a}` in `H_4` splits. -/
example : ∃ cp cm : ℕ → ℚ, SplitComplex.IsSplit 3
    (fun a => (eH datum scalars true false 3 a : DividedPowerModules.ModuleRing datum scalars 4))
    (fun a => (fH datum scalars true false 3 a : DividedPowerModules.ModuleRing datum scalars 4))
    (fun a => (gH datum scalars true false 3 a : DividedPowerModules.ModuleRing datum scalars 4))
    cp cm :=
  isSplit (by decide) (by rw [dn_true_false])

/-- `i` even, `M = 2`: the even/odd isomorphism of BE2 Proposition 11.2 in `H_3`. -/
example : (∀ a : SplitComplex.terms 2 true,
      DividedPowerModules.principal datum scalars (eH datum scalars false true 2 a)) ≃ₗ[
      DividedPowerModules.ModuleRing datum scalars 3]
    (∀ b : SplitComplex.terms 2 false,
      DividedPowerModules.principal datum scalars (eH datum scalars false true 2 b)) :=
  serreEquiv (by decide) (by rw [dn_false_true])

#print axioms OddMath.QuiverHecke.SerreComplex.isSplit
#print axioms OddMath.QuiverHecke.SerreComplex.serreEquiv

end NonVacuity.SerreComplex
