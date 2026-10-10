import OddMath.CoveringQuantum.UDot.Symmetries
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.AdjoinRoot

/-!
# Generic covering coefficients and normalization units

The coefficient ring in [BE2] §9 is `ℚ(q)[π]/(π² - 1)`. We use Mathlib's
`AdjoinRoot` of `X² - 1` over `RatFunc ℚ`, so the formalization is the polynomial
quotient itself. The parameter `q` is the image of the rational-function variable.
`Coefficients.bar` is the involution fixing `π` and replacing `q` by its inverse;
`Coefficients.barData` supplies the scalar hypotheses for the symmetries.

`Coefficients.denominator_isUnit` proves that all denominators in the normalization
of the half-algebra form are units. This discharges the inverse caveat of
`SuperCartanDatum.norm` for the generic covering coefficients; it does not establish
nondegeneracy of the Serre presentation.
-/

noncomputable section

namespace OddMath.CoveringQuantum

namespace Coefficients

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- The relation defining the covering coefficient ring. -/
def relation : Polynomial (RatFunc ℚ) := Polynomial.X ^ 2 - 1

/-- The ring `ℚ(q)[π]/(π² - 1)`, as the actual polynomial quotient. -/
abbrev Ring := AdjoinRoot relation

/-- The covering parameter `π`. -/
def pi : Ring := AdjoinRoot.root relation

@[simp] theorem pi_sq : pi ^ 2 = 1 := by
  have h := AdjoinRoot.eval₂_root relation
  simpa only [pi, relation, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_one, sub_eq_zero] using h

/-- The generic quantum parameter, a unit in the covering coefficient ring. -/
def q : Ringˣ := Units.map (algebraMap (RatFunc ℚ) Ring).toMonoidHom
  (Units.mk0 RatFunc.X RatFunc.X_ne_zero)

@[simp] theorem coe_q : (q : Ring) = algebraMap (RatFunc ℚ) Ring RatFunc.X := rfl

/-- Specialization of the covering parameter to a scalar with square one. -/
def specialize (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) : Ring →ₐ[RatFunc ℚ] RatFunc ℚ :=
  AdjoinRoot.liftAlgHom relation (Algebra.ofId _ _) ε (by simp [relation, hε])

@[simp] theorem specialize_pi (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) : specialize ε hε pi = ε := by
  apply AdjoinRoot.liftAlgHom_root

@[simp] theorem specialize_q (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) : specialize ε hε (q : Ring) = RatFunc.X := by
  rw [coe_q, AlgHom.commutes]
  rfl

instance : Nontrivial Ring := by
  have h : (0 : Ring) ≠ 1 := by
    intro h
    have he := congrArg (specialize 1 (one_pow 2)) h
    exact zero_ne_one (by simpa only [map_zero, map_one] using he)
  exact ⟨⟨0, 1, h⟩⟩

private theorem ratFunc_pow_ne_one {n : ℕ} (hn : 0 < n) : (RatFunc.X : RatFunc ℚ) ^ n ≠ 1 := by
  intro h
  have hd := congrArg RatFunc.intDegree h
  rw [← RatFunc.algebraMap_X, ← map_pow, RatFunc.intDegree_polynomial, Polynomial.natDegree_X_pow,
    RatFunc.intDegree_one] at hd
  omega

/-- The generic factor `1 - ε qⁿ` is invertible when `ε² = 1` and `n > 0`. -/
theorem one_sub_isUnit (ε : Ring) (hε : ε ^ 2 = 1) {n : ℕ} (hn : 0 < n) :
    IsUnit (1 - ε * (q : Ring) ^ n) := by
  have hbase : IsUnit (1 - (RatFunc.X : RatFunc ℚ) ^ (2 * n)) :=
    isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (ratFunc_pow_ne_one (by omega)).symm)
  have hprod : (1 - ε * (q : Ring) ^ n) * (1 + ε * (q : Ring) ^ n) =
      algebraMap (RatFunc ℚ) Ring (1 - RatFunc.X ^ (2 * n)) := by
    rw [map_sub, map_one, map_pow, ← coe_q]
    linear_combination -((q : Ring) ^ (2 * n)) * hε
  exact isUnit_of_mul_isUnit_left (hprod.symm ▸ hbase.map (algebraMap (RatFunc ℚ) Ring))

private theorem inv_X_transcendental : Transcendental ℚ ((RatFunc.X : RatFunc ℚ)⁻¹) := by
  intro h
  apply RatFunc.transcendental_X (K := ℚ)
  simpa only [inv_inv] using h.inv

/-- Substitution `q ↦ q⁻¹` on rational functions. -/
def ratBar : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.liftRingHom (Polynomial.aeval ((RatFunc.X : RatFunc ℚ)⁻¹)).toRingHom (by
    intro p hp
    change (Polynomial.aeval ((RatFunc.X : RatFunc ℚ)⁻¹)) p ∈ nonZeroDivisors (RatFunc ℚ)
    rw [mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    exact fun h ↦ hp ((transcendental_iff.mp inv_X_transcendental) p h))

@[simp] theorem ratBar_X : ratBar RatFunc.X = (RatFunc.X : RatFunc ℚ)⁻¹ := by
  rw [← RatFunc.algebraMap_X, ratBar, RatFunc.liftRingHom_algebraMap]
  simp

/-- Rational-function inversion of the variable is involutive. -/
theorem ratBar_ratBar (x : RatFunc ℚ) : ratBar (ratBar x) = x := by
  let inclusion := algebraMap (Polynomial ℚ) (RatFunc ℚ)
  have hp : (ratBar.comp ratBar).comp inclusion = inclusion := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · change ratBar (ratBar RatFunc.X) = RatFunc.X
      rw [ratBar_X, map_inv₀, ratBar_X, inv_inv]
  have hpoly (p : Polynomial ℚ) : ratBar (ratBar (algebraMap _ (RatFunc ℚ) p)) =
      algebraMap _ (RatFunc ℚ) p := congrArg (fun f : Polynomial ℚ →+* RatFunc ℚ ↦ f p) hp
  rw [← RatFunc.num_div_denom x, map_div₀, map_div₀, hpoly, hpoly]

/-- The scalar bar on the covering ring, fixing `π` and sending `q` to `q⁻¹`. -/
def bar : Ring →+* Ring :=
  AdjoinRoot.lift ((algebraMap (RatFunc ℚ) Ring).comp ratBar) pi (by simp [relation])

@[simp] theorem bar_pi : bar pi = pi := AdjoinRoot.lift_root _

@[simp] theorem bar_algebraMap (x : RatFunc ℚ) :
    bar (algebraMap (RatFunc ℚ) Ring x) = algebraMap (RatFunc ℚ) Ring (ratBar x) :=
  AdjoinRoot.lift_of _

@[simp] theorem bar_q : bar (q : Ring) = ((q⁻¹ : Ringˣ) : Ring) := by
  rw [coe_q, bar_algebraMap, ratBar_X]
  rfl

/-- The bar involution of the generic covering ring. -/
theorem bar_bar (x : Ring) : bar (bar x) = x := by
  have h : bar.comp bar = RingHom.id Ring := by
    apply AdjoinRoot.ringHom_ext
    · ext c
      change bar (bar (algebraMap (RatFunc ℚ) Ring c)) = algebraMap (RatFunc ℚ) Ring c
      rw [bar_algebraMap, bar_algebraMap, ratBar_ratBar]
    · change bar (bar pi) = pi
      rw [bar_pi, bar_pi]
  exact congrArg (fun f : Ring →+* Ring ↦ f x) h

/-- The concrete coefficient ring supplies the bar data used by the covering-group symmetries. -/
theorem barData : UDot.BarData q pi bar := ⟨bar_q, bar_pi, pi_sq⟩

variable {I : Type*} (C : SuperCartanDatum I)

/-- Every denominator `1 - πᵢ qᵢ²` in the half-form normalization is a unit. -/
theorem denominator_isUnit (i : I) :
    IsUnit (1 - C.pii pi i * ((C.qi q i : Ringˣ) : Ring) ^ 2) := by
  rw [SuperCartanDatum.qi, Units.val_pow_eq_pow_val, ← pow_mul]
  exact one_sub_isUnit _ (C.pii_sq pi pi_sq i) (Nat.mul_pos (C.d_pos i) (by decide))

/-- On the generic coefficient ring, `norm` is an actual multiplicative inverse. -/
theorem denominator_mul_norm (i : I) :
    (1 - C.pii pi i * ((C.qi q i : Ringˣ) : Ring) ^ 2) * C.norm q pi i = 1 :=
  _root_.Ring.mul_inverse_cancel _ (denominator_isUnit C i)

/-- The normalized value on each simple generator is itself a unit. -/
theorem norm_isUnit (i : I) : IsUnit (C.norm q pi i) := by
  rw [SuperCartanDatum.norm, _root_.Ring.inverse_of_isUnit (denominator_isUnit C i)]
  exact Units.isUnit _

end Coefficients

end OddMath.CoveringQuantum
