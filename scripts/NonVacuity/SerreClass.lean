import OddMath

/-! # BE2 Proposition 11.2 in `K₀(Ḣ_{q,π})` and `K₀(𝔘̇_{q,π}(𝔤))` on a rank-two datum

The datum of `scripts/NonVacuity/SerreComplex.lean` (type `B₂`, `true` odd, `d_{true,false} = 2`,
`d_{false,true} = 1`) with the symmetrizer `d_true = 1`, `d_false = 2`. The scalars `s` vanish,
so (1.31) holds. Both orders of the two colours are exercised.
-/

noncomputable section
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.SerreComplex

namespace NonVacuity.SerreClass

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

/-- `i` odd, `M = 3`: `∑_a (-1)^a [term a] = 0` for the terms `i^{(a)} j i^{(3-a)}`. -/
example : ∑ a ∈ Finset.range 4, ((-1 : ℤ) ^ a) •
    StringDiagrams.K₀.mk (term symmetrizer homogeneous true false 3 a) = 0 :=
  class_alternating_sum symmetrizer homogeneous (by decide) (by rw [dn_true_false])

/-- `i` even, `M = 2`: the even and odd terms have the same class. -/
example : ∑ a ∈ SplitComplex.terms 2 true,
      StringDiagrams.K₀.mk (term symmetrizer homogeneous false true 2 a) =
    ∑ a ∈ SplitComplex.terms 2 false,
      StringDiagrams.K₀.mk (term symmetrizer homogeneous false true 2 a) :=
  class_even_eq_odd symmetrizer homogeneous (by decide) (by rw [dn_false_true])

/-- `i` odd, `M = 3`, in `𝔘̇_{q,π}(𝔤)` at the weight `0`. -/
example : ∑ a : Fin 4, ((-1 : ℤ) ^ (a : ℕ)) •
    StringDiagrams.K₀.mk (termUp symmetrizer homogeneous true false 3 0 a
      (Nat.le_of_lt_succ a.2)) = 0 :=
  class_alternating_sum_up symmetrizer homogeneous (by decide) (by rw [dn_true_false]) 0

#print axioms OddMath.QuiverHecke.SerreComplex.class_alternating_sum
#print axioms OddMath.QuiverHecke.SerreComplex.class_alternating_sum_up
#print axioms OddMath.QuiverHecke.SerreComplex.class_even_eq_odd

end NonVacuity.SerreClass
