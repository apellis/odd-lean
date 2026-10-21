/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Polynomial
import OddMath.Frontier.NilHeckeBasis

/-!
# The all-odd polynomial specialization

Compatibility of the mixed polynomial coefficient algebra with the existing
integral odd polynomial model and its faithful nilHecke action (Ellis–Khovanov–Lauda,
arXiv:1111.1320v1, §2.1 and Proposition 2.11). This supplies the same-odd-colour
coefficient-model comparison needed for Hill–Wang, arXiv:1202.2769v2,
Proposition 4.5. The source of the action is the existing integral presented
odd nilHecke ring, not a quiver Hecke algebra `Hn`.
-/

noncomputable section
namespace OddMath.QuiverHecke.Polynomial

/-- With all positions odd, the normal-ordering signs agree with EKL. -/
theorem sign_allOdd {n : ℕ} (a b : Fin n → ℕ) :
    sign (R := ℤ) (fun _ => true) a b = OddMath.skewSign a b := rfl

/-- The all-odd coefficient algebra is the existing integral odd polynomial ring.
The comparison preserves coefficients rather than changing monomial order. -/
def allOddEquiv (n : ℕ) :
    Polynomial ℤ n (fun _ => true) ≃+* SkewPolynomial.SkewPolynomial n where
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' f g := by
    change (f * g : Polynomial ℤ n (fun _ => true)) = SkewPolynomial.mul f g
    induction f using induction_on (fun _ => true) with
    | hz => simp only [zero_mul, SkewPolynomial.zero_mul]
    | ha f₁ f₂ h₁ h₂ =>
      change ((f₁ + f₂) * g : Polynomial ℤ n (fun _ => true)) =
        SkewPolynomial.mul (f₁ + f₂) g
      rw [add_mul, SkewPolynomial.add_mul, h₁, h₂]
    | hm a r =>
      induction g using induction_on (fun _ => true) with
      | hz => simp only [mul_zero, SkewPolynomial.mul_zero]
      | ha g₁ g₂ h₁ h₂ =>
        change (monomial (fun _ => true) a r * (g₁ + g₂) : Polynomial ℤ n (fun _ => true)) =
          SkewPolynomial.mul (SkewPolynomial.monomial a r) (g₁ + g₂)
        rw [mul_add, SkewPolynomial.mul_add, h₁, h₂]
        rfl
      | hm b s =>
        change (monomial (fun _ => true) a r * monomial (fun _ => true) b s :
          Polynomial ℤ n (fun _ => true)) =
          SkewPolynomial.mul (SkewPolynomial.monomial a r) (SkewPolynomial.monomial b s)
        rw [monomial_mul, SkewPolynomial.mul_monomial, sign_allOdd]
        rfl

@[simp] theorem allOddEquiv_monomial {n : ℕ} (a : Fin n → ℕ) (r : ℤ) :
    allOddEquiv n (monomial (fun _ => true) a r) = SkewPolynomial.monomial a r := rfl

@[simp] theorem allOddEquiv_X {n : ℕ} (i : Fin n) :
    allOddEquiv n (X (fun _ => true) i) = SkewPolynomial.generator i := rfl

/-- Reuse of the proved integral odd nilHecke action on the all-odd coefficient module.
The rank convention of the existing presented ring is `n + 2`. -/
def oddNilHeckeAction (n : ℕ) : Frontier.NilHeckeAction.Presented n →+*
    Module.End ℤ (Polynomial ℤ (n + 2) (fun _ => true)) :=
  Frontier.NilHeckeAction.action n

/-- Faithfulness is transported from the existing odd PBW theorem, not assumed. -/
theorem oddNilHeckeAction_injective (n : ℕ) : Function.Injective (oddNilHeckeAction n) :=
  Frontier.NilHeckeBasis.action_injective n

/-- The transported dot is multiplication in the mixed coefficient algebra. -/
theorem oddNilHeckeAction_dot_apply (n : ℕ) (i : Fin (n + 2))
    (f : Polynomial ℤ (n + 2) (fun _ => true)) :
    oddNilHeckeAction n (Frontier.NilHeckeAction.dot n i) f = X (fun _ => true) i * f := by
  apply (allOddEquiv (n + 2)).injective
  change Frontier.NilHeckeAction.action n (Frontier.NilHeckeAction.dot n i) f =
    allOddEquiv (n + 2) (X (fun _ => true) i * f)
  rw [map_mul, allOddEquiv_X]
  exact Frontier.NilHeckeAction.action_dot_apply n i f

/-- The transported crossing is the existing odd divided-difference operator. -/
theorem oddNilHeckeAction_crossing_apply (n : ℕ) (i : Fin (n + 1))
    (f : Polynomial ℤ (n + 2) (fun _ => true)) :
    allOddEquiv (n + 2) (oddNilHeckeAction n (Frontier.NilHeckeAction.crossing n i) f) =
      Frontier.AllRankDivided.divided i (allOddEquiv (n + 2) f) :=
  Frontier.NilHeckeAction.action_crossing_apply n i f

end OddMath.QuiverHecke.Polynomial
