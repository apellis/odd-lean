import OddMath.SKM.SerrePolynomial
import OddMath.SKM.Grading
import OddMath.QuiverHecke.CyclotomicAction.LocalRelationExamples

/-!
# An asymmetric odd Cartan quadratic requires a parameter comparison

For the symmetrizable all-odd datum with off-diagonal entries -2 and -4,
the homogeneous polynomial is `u²+v⁴`. Signed right multiplication changes
the signs of dot squares but not fourth powers. No common scalar on the
quadratic polynomial absorbs that discrepancy. This excludes only the
fixed-dot, unchanged-parameter scalar-crossing prescription, not an action
with transported parameters.
-/
namespace OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
open SKM SKM.SerrePolynomial

/-- Both vertices are odd; the off-diagonal exponents differ. -/
def datum : Datum Bool (Bool → ℤ) where
  cd := {
    root := fun j i => if i = j then 2 else if i then -4 else -2
    coroot := fun i => LinearMap.proj i
    coroot_root_self := fun i => by simp }
  isGCM := {
    diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
    offDiag_nonpos := by
      intro i j hij
      cases i <;> cases j <;> simp_all [CartanDatum.cartanMatrix_apply]
    zero_comm := by
      intro i j
      cases i <;> cases j <;> norm_num [CartanDatum.cartanMatrix_apply] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else if i then -4 else -2)
    cases i <;> cases j <;> norm_num [even_iff_two_dvd]

/-- Positive symmetrizer `(2,1)`. -/
def symmetrizer : Symmetrizer datum where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl

def scalars : Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

theorem homogeneous : scalars.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim

theorem quadratic (u v : ℚ) :
    quadraticValue scalars false true u v = u ^ 2 + v ^ 4 := by
  have h₂ : datum.dn false true = 2 := rfl
  have h₄ : datum.dn true false = 4 := rfl
  simp [quadraticValue, scalars, h₂, h₄]

/-- The parameter family required by the mixed-square calculation. -/
def transportedScalars : Scalars datum ℚ where
  t := fun i j => if i = j then 1 else if i then -1 else 1
  t_self := by intro i; simp
  t_symm_of_d_eq_zero := by
    intro i j h
    have hz : datum.d i j ≠ 0 := by
      cases i <;> cases j <;> decide
    exact (hz h).elim
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

theorem transported_homogeneous : transportedScalars.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim

theorem transported_quadratic (u v : ℚ) :
    quadraticValue transportedScalars false true u v = u ^ 2 - v ^ 4 := by
  have h₂ : datum.dn false true = 2 := rfl
  have h₄ : datum.dn true false = 4 := rfl
  simp [quadraticValue, transportedScalars, h₂, h₄, sub_eq_add_neg]

/-- The two terms have the same weighted degree for the displayed symmetrizer. -/
theorem equal_weighted_degree :
    2 * symmetrizer.d false = 4 * symmetrizer.d true := by rfl

/-- In square coordinates, no crossing-product scalar repairs unchanged parameters. -/
theorem no_common_quadratic_scalar :
    ¬ ∃ c : ℚ, ∀ z w : ℚ, c * (z + w ^ 2) = -z + w ^ 2 := by
  rintro ⟨c, hc⟩
  have h₁ := hc 1 0
  have h₂ := hc 0 1
  norm_num at h₁ h₂
  linarith

/-- A sign on either individual dot does not change the source polynomial. -/
theorem dot_signs_do_not_repair (u v : ℚ) :
    quadraticValue scalars false true (-u) (-v) = quadraticValue scalars false true u v := by
  rw [quadratic, quadratic]
  ring

/-- Four signed odd right multiplications have positive sign. -/
theorem oddRight_fourth {A : Type*} [Ring A] (σ : A →+* A)
    (hσ : Function.Involutive σ) (y : A) (hy : σ y = -y) (h : A) :
    oddRight σ y (oddRight σ y (oddRight σ y (oddRight σ y h))) = h * y ^ 4 := by
  rw [oddRight_comp σ hσ y y hy, oddRight_comp σ hσ y y hy]
  noncomm_ring

/-- The signed right-multiplier mixed square passes after changing the quartic parameter.
This is an algebraic relation transfer, not an induced-projective functor. -/
theorem transported_mixed_square {A : Type*} [Ring A] (σ : A →+* A)
    (hσ : Function.Involutive σ) (x y u v : A)
    (hx : σ x = -x) (hy : σ y = -y) (hv : σ v = -v)
    (hquad : v * u = x * x - y ^ 4) (h : A) :
    -oddRight σ u (-oddRight σ v h) =
      oddRight σ x (oddRight σ x h) +
        oddRight σ y (oddRight σ y (oddRight σ y (oddRight σ y h))) := by
  rw [neg_oddRight_comp σ hσ u v hv, oddRight_comp σ hσ x x hx,
    oddRight_fourth σ hσ y hy, hquad]
  noncomm_ring

#print axioms homogeneous
#print axioms transported_mixed_square
#print axioms quadratic
#print axioms no_common_quadratic_scalar

end OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
