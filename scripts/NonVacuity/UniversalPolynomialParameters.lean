import OddMath.SKM.UniversalPolynomialParameters

/-! Interior and unused coefficient specialization over ZMod 9, and separate
odd-support tests. The dependent-root unit fixture is retained in the
UniversalCoefficientRing consumer. -/

noncomputable section

namespace NonVacuity.UniversalPolynomialParameters

open OddMath.SKM
open OddMath.SKM.UniversalPolynomialParameters

/-- Affine rank two, with both off-diagonal entries -2. -/
def datum (odd : Bool) : Datum Bool ℤ where
  cd := {
    root := fun i => if i then -1 else 1
    coroot := fun i => (if i then -2 else 2) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
    coroot_root_self := by intro i; cases i <;> norm_num }
  isGCM := {
    diag := by intro i; cases i <;> norm_num [CartanDatum.cartanMatrix_apply]
    offDiag_nonpos := by
      intro i j h
      cases i <;> cases j <;> simp_all [CartanDatum.cartanMatrix_apply]
    zero_comm := by
      intro i j
      cases i <;> cases j <;> norm_num [CartanDatum.cartanMatrix_apply] }
  parity := fun _ => if odd then 1 else 0
  even_of_odd := by
    intro i j _
    cases i <;> cases j
    · exact ⟨1, by norm_num⟩
    · exact ⟨-1, by norm_num⟩
    · exact ⟨-1, by norm_num⟩
    · exact ⟨1, by norm_num⟩

def symmetrizer (odd : Bool) : Symmetrizer (datum odd) where
  d := fun _ => 1
  pos := fun _ => by norm_num
  symm := by
    intro i j
    cases i <;> cases j <;> norm_num [Datum.d, Datum.h, Datum.α, datum]

theorem two_unit : IsUnit (2 : ZMod 9) := by
  refine ⟨⟨2, 5, ?_, ?_⟩, rfl⟩ <;> decide

/-- The used coefficient is 3, while unused boundary coefficients are 4. -/
def supplied : Scalars (datum false) (ZMod 9) where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ p q => if p = 1 ∧ q = 1 then 3 else if p = 0 ∨ q = 0 then 4 else 0
  s_symm := by intros; simp only [and_comm, or_comm]
  s_eq_zero := by intros i j p q h; simp [datum] at h
  two_isUnit := fun _ => two_unit

theorem supplied_homogeneous : supplied.Homogeneous := by
  intro i j p q hp hp' hq hq' _
  cases i <;> cases j <;> norm_num [Datum.d, Datum.h, Datum.α, datum] at hp' hq' ⊢ <;> omega

def suppliedNormalizations : CScalars supplied where
  c := fun _ _ => 1
  shift := by intros; simp [supplied]

def evaluation : ParameterRing (datum false) →+* ZMod 9 :=
  specialize two_unit suppliedNormalizations

example : 0 < (1 : ℕ) ∧ (1 : ℤ) < (datum false).d false true ∧
    0 < (1 : ℕ) ∧ (1 : ℤ) < (datum false).d true false := by
  norm_num [Datum.d, Datum.h, Datum.α, datum]

/-- A genuinely nonzero interior coefficient, in a ring with zero divisors. -/
theorem interior_image : evaluation ((scalars (datum false)).s false true 1 1) = 3 :=
  specialize_coefficient two_unit suppliedNormalizations supplied_homogeneous ⟨false, true, 1, 1⟩

theorem interior_ne_zero : (scalars (datum false)).s false true 1 1 ≠ 0 := by
  intro h
  have he := interior_image
  rw [h, map_zero] at he
  exact (by decide : (0 : ZMod 9) ≠ 3) he

/-- This slot is not in a used rectangle, and fails its degree equation;
it must nevertheless specialize to the supplied nonzero value. -/
theorem unused_image : evaluation ((scalars (datum false)).s false true 0 5) = 4 :=
  specialize_coefficient two_unit suppliedNormalizations supplied_homogeneous ⟨false, true, 0, 5⟩

example : (0 : ℤ) * (datum false).d true false + 5 * (datum false).d false true ≠
    (datum false).d false true * (datum false).d true false := by
  norm_num [Datum.d, Datum.h, Datum.α, datum]

example : evaluation ((scalars (datum false)).s true false 5 0) = 4 := by
  rw [(scalars (datum false)).s_symm]
  exact unused_image

/-- Diagonal unused coefficients also survive. -/
example : evaluation ((scalars (datum false)).s false false 0 5) = 4 :=
  specialize_coefficient two_unit suppliedNormalizations supplied_homogeneous ⟨false, false, 0, 5⟩

example : (scalars (datum false)).Homogeneous := homogeneous _

example : Units.map evaluation.toMonoidHom ((scalars (datum false)).t false true) = 1 :=
  specialize_t two_unit suppliedNormalizations false true

example (μ : ℤ) : Units.map evaluation.toMonoidHom
    ((normalizations (datum false)).c μ false) = 1 :=
  specialize_c two_unit suppliedNormalizations μ false

example (f : ParameterRing (datum false) →+* ZMod 9)
    (ht : ∀ i j, Units.map f.toMonoidHom ((scalars (datum false)).t i j) = supplied.t i j)
    (hc : ∀ μ i, Units.map f.toMonoidHom ((normalizations (datum false)).c μ i) =
      suppliedNormalizations.c μ i)
    (hs : ∀ i j p q, f ((scalars (datum false)).s i j p q) = supplied.s i j p q) :
    f = evaluation := specialize_unique two_unit suppliedNormalizations supplied_homogeneous f ht hc hs

/-- Both odd exponents are forbidden separately, even outside used rectangles. -/
example : (scalars (datum true)).s false true 1 0 = 0 :=
  (scalars (datum true)).s_eq_zero _ _ _ _ (by norm_num [datum])

example : (scalars (datum true)).s false true 0 1 = 0 := by
  rw [(scalars (datum true)).s_symm]
  exact (scalars (datum true)).s_eq_zero _ _ _ _ (by norm_num [datum])

example : (scalars (datum true)).s false true 1 1 = 0 :=
  (scalars (datum true)).s_eq_zero _ _ _ _ (by norm_num [datum])

/-- Specializing to the universal family itself is the identity on the entire ring. -/
example : specialize (two_isUnit (datum false)) (normalizations (datum false)) =
    RingHom.id (ParameterRing (datum false)) := by
  symm
  apply specialize_unique _ _ (homogeneous _)
  · intro i j
    apply Units.ext
    rfl
  · intro μ i
    apply Units.ext
    rfl
  · intros
    rfl

#print axioms OddMath.SKM.UniversalPolynomialParameters.two_isUnit
#print axioms OddMath.SKM.UniversalPolynomialParameters.allowed_swap
#print axioms OddMath.SKM.UniversalPolynomialParameters.slot_swap
#print axioms OddMath.SKM.UniversalPolynomialParameters.coefficient_swap
#print axioms OddMath.SKM.UniversalPolynomialParameters.scalars
#print axioms OddMath.SKM.UniversalPolynomialParameters.homogeneous
#print axioms OddMath.SKM.UniversalPolynomialParameters.normalizations
#print axioms OddMath.SKM.UniversalPolynomialParameters.allowed_of_ne_zero
#print axioms OddMath.SKM.UniversalPolynomialParameters.specialize
#print axioms OddMath.SKM.UniversalPolynomialParameters.specialize_C
#print axioms OddMath.SKM.UniversalPolynomialParameters.specialize_coefficient
#print axioms OddMath.SKM.UniversalPolynomialParameters.specialize_t
#print axioms OddMath.SKM.UniversalPolynomialParameters.specialize_c
#print axioms OddMath.SKM.UniversalPolynomialParameters.hom_ext
#print axioms OddMath.SKM.UniversalPolynomialParameters.specialize_unique
#print axioms interior_image
#print axioms interior_ne_zero
#print axioms unused_image

end NonVacuity.UniversalPolynomialParameters
