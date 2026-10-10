import OddMath.CoveringQuantum.Coefficients
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Splitting the generic covering coefficients

Evaluation at `π = 1` and `π = -1` identifies the polynomial quotient with the
product of two rational-function fields. This is the scalar decomposition used
in CFLW, arXiv:1307.7056v2, §2.1. The theorem below concerns
coefficients; base change of the half-algebra presentation is a separate step.
-/

noncomputable section

namespace OddMath.CoveringQuantum.Coefficients

@[simp] theorem specialize_of (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) (x : RatFunc ℚ) :
    specialize ε hε ((AdjoinRoot.of relation) x) = x :=
  (specialize ε hε).commutes x

/-- Both specializations together. -/
def split : Ring →ₐ[RatFunc ℚ] RatFunc ℚ × RatFunc ℚ :=
  (specialize 1 (one_pow 2)).prod (specialize (-1) (by norm_num))

@[simp] theorem split_pi : split pi = (1, -1) := by
  ext <;> simp [split]

@[simp] theorem split_q : split (q : Ring) = (RatFunc.X, RatFunc.X) := by
  ext <;> simp [split]

/-- A coefficient vanishing at both signs is zero. -/
theorem split_injective : Function.Injective split := by
  apply (injective_iff_map_eq_zero split).mpr
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    have hp : p.eval 1 = 0 ∧ p.eval (-1) = 0 := by
      have h1 := congrArg Prod.fst hx
      have h2 := congrArg Prod.snd hx
      simpa [split, specialize, AdjoinRoot.liftAlgHom, AdjoinRoot.lift_mk] using And.intro h1 h2
    apply AdjoinRoot.mk_eq_zero.mpr
    have hc : IsCoprime (Polynomial.X - Polynomial.C (1 : RatFunc ℚ))
        (Polynomial.X - Polynomial.C (-1 : RatFunc ℚ)) :=
      Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by norm_num)
    have hr : relation = (Polynomial.X - Polynomial.C (1 : RatFunc ℚ)) *
        (Polynomial.X - Polynomial.C (-1 : RatFunc ℚ)) := by
      simp [relation]
      ring
    rw [hr]
    exact hc.mul_dvd (Polynomial.dvd_iff_isRoot.mpr hp.1)
      (Polynomial.dvd_iff_isRoot.mpr hp.2)

/-- Every pair is interpolated by a polynomial of degree at most one in `π`. -/
theorem split_surjective : Function.Surjective split := by
  rintro ⟨a, b⟩
  refine ⟨algebraMap (RatFunc ℚ) Ring ((a + b) / 2) +
    algebraMap (RatFunc ℚ) Ring ((a - b) / 2) * pi, ?_⟩
  ext <;> simp [split] <;> ring

/-- The actual covering coefficient quotient is the product of its two specializations. -/
def splitEquiv : Ring ≃ₐ[RatFunc ℚ] RatFunc ℚ × RatFunc ℚ :=
  AlgEquiv.ofBijective split ⟨split_injective, split_surjective⟩

/-- Equality of coefficients can be checked independently at the two signs. -/
theorem eq_iff_specialize_eq (a b : Ring) : a = b ↔
    specialize 1 (one_pow 2) a = specialize 1 (one_pow 2) b ∧
    specialize (-1) (by norm_num) a = specialize (-1) (by norm_num) b := by
  rw [← split_injective.eq_iff]
  exact Prod.ext_iff

end OddMath.CoveringQuantum.Coefficients
