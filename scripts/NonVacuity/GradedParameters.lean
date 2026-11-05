import OddMath

/-! # Lower-degree parameters that are not homogeneous

The even datum on two vertices with off-diagonal Cartan entries `-3`, symmetrizer `(1, 1)`, and
parameters `Qᵢⱼ(u, v) = u³ + uv + v³` over `ℚ` (only `s^{11}` is nonzero). The monomial `uv`
has degree `4 < 6`, so the parameters are lower-degree (`Scalars.LowerDegree`) but violate the
homogeneity condition (1.31). The Rees parameters are graded homogeneous, and
`nondegeneracyConjecture_of_lowerDegree` applies with every hypothesis proved except the
graded-coefficient statement, which is its explicit hypothesis; no instance of the conjecture
is asserted.
-/

noncomputable section
namespace NonVacuity.GradedParameters
open OddMath OddMath.SKM

/-- Two even vertices with Cartan entries `-3`. -/
def datum : Datum Bool (Bool → ℤ) where
  cd := {
    root := fun j i => if i = j then 2 else -3
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
  parity := fun _ => 0
  even_of_odd := by
    intro i j h
    exact absurd h (by decide)

theorem d_ne {i j : Bool} (h : i ≠ j) : datum.d i j = 3 := by
  cases i <;> cases j <;> first | exact absurd rfl h | rfl

/-- The symmetrizer `(1, 1)`. -/
def symmetrizer : Symmetrizer datum where
  d := fun _ => 1
  pos := by intro i; norm_num
  symm := by intro i j; simp

/-- `sᵢⱼ^{11} = 1` for `i ≠ j`, all other mixed coefficients zero. -/
def scalars : Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun i j p q => if i ≠ j ∧ p = 1 ∧ q = 1 then 1 else 0
  s_symm := by
    intro i j p q
    by_cases h : i = j
    · subst h; simp [and_comm]
    · simp [h, Ne.symm h, and_comm]
  s_eq_zero := by
    intro i j p q h
    simp [datum] at h
  two_isUnit := by intro _; norm_num

theorem lowerDegree : scalars.LowerDegree symmetrizer := by
  intro i j p q _ _ _ _ hs
  have h : i ≠ j ∧ p = 1 ∧ q = 1 := by
    by_contra h
    exact hs (by simp [scalars, h])
  obtain ⟨hij, rfl, rfl⟩ := h
  simp [coefficientDegree, symmetrizer, d_ne hij]

theorem not_homogeneous : ¬ scalars.Homogeneous := by
  intro hh
  have := hh false true 1 1 (by norm_num) (by rw [d_ne (by decide)]; norm_num) (by norm_num)
    (by rw [d_ne (by decide)]; norm_num) (by simp [scalars])
  rw [d_ne (by decide), d_ne (by decide)] at this
  norm_num at this

/-- The coefficient degree of `s^{11}` is `2`. -/
example : coefficientDegree symmetrizer false true 1 1 = 2 := by
  simp [coefficientDegree, symmetrizer, d_ne (show false ≠ true by decide)]

/-- The Rees parameters over `ℚ[h]` are graded homogeneous. -/
example : (ReesParameters.scalars symmetrizer scalars).GradedHomogeneous symmetrizer
    (MvPolynomial.homogeneousSubmodule Unit ℚ) :=
  ReesParameters.gradedHomogeneous symmetrizer lowerDegree

/-- The reduction applies to these inhomogeneous parameters, for every normalization. -/
example (hG : GradedCoefficientNondegeneracy.{0, 0, 0} datum symmetrizer)
    (cs : CScalars scalars) : NondegeneracyConjecture cs :=
  nondegeneracyConjecture_of_lowerDegree hG (IsUnit.mk0 _ two_ne_zero) lowerDegree cs

#print axioms OddMath.SKM.nondegeneracyConjecture_of_lowerDegree

end NonVacuity.GradedParameters
