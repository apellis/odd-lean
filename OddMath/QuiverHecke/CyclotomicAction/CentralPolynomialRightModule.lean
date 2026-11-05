/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.CentralPolynomialModule
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Right central polynomial modules

Restriction of the central polynomial action to the opposite of the ordinary
polynomial ring, for the right polynomial modules in the cyclotomic construction.
No commutativity of the coefficient ring is assumed.
-/

noncomputable section

namespace OddMath.QuiverHecke.CyclotomicAction

open MulOpposite

universe u v w

variable (R : Type u) [Ring R]

/-- Coefficientwise opposition, viewed as a homomorphism of rings. -/
def polynomialOpHom : (Polynomial R)ᵐᵒᵖ →+* Polynomial Rᵐᵒᵖ :=
  (RingEquiv.opOp (Polynomial Rᵐᵒᵖ)).symm.toRingHom.comp
    (RingHom.op (Polynomial.eval₂RingHom'
      ((RingHom.op (Polynomial.C (R := Rᵐᵒᵖ))).comp (RingEquiv.opOp R).toRingHom)
      (op Polynomial.X) (fun r => by
        change Commute (op (Polynomial.C (op r))) (op Polynomial.X)
        exact (Polynomial.commute_X (Polynomial.C (op r))).symm.op)))

@[simp] theorem polynomialOpHom_C (r : R) :
    polynomialOpHom R (op (Polynomial.C r)) = Polynomial.C (op r) := by
  simp [polynomialOpHom, Polynomial.eval₂RingHom']

@[simp] theorem polynomialOpHom_X :
    polynomialOpHom R (op Polynomial.X) = Polynomial.X := by
  simp [polynomialOpHom, Polynomial.eval₂RingHom']

@[simp] theorem polynomialOpHom_monomial (n : ℕ) (r : R) :
    polynomialOpHom R (op (Polynomial.monomial n r)) = Polynomial.monomial n (op r) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp [op_mul, ← Polynomial.C_mul_X_pow_eq_monomial]

/-- The ring homomorphism takes the opposite of every coefficient. -/
@[simp] theorem polynomialOpHom_coeff (p : Polynomial R) (n : ℕ) :
    (polynomialOpHom R (op p)).coeff n = op (p.coeff n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [op_add, map_add, Polynomial.coeff_add, hp, hq]
  | monomial k r =>
      rw [polynomialOpHom_monomial]
      by_cases hk : k = n <;> simp [Polynomial.coeff_monomial, hk]

variable {R} {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- A right module over the ordinary central polynomial ring. -/
def RightCentralPolynomialModule (f : M →ₗ[Rᵐᵒᵖ] M) := CentralPolynomialModule f

namespace RightCentralPolynomialModule

variable (f : M →ₗ[Rᵐᵒᵖ] M)

instance : AddCommGroup (RightCentralPolynomialModule f) :=
  inferInstanceAs (AddCommGroup (CentralPolynomialModule f))

instance : Module (Polynomial R)ᵐᵒᵖ (RightCentralPolynomialModule f) :=
  Module.compHom (CentralPolynomialModule f) (polynomialOpHom R)

/-- The additive identification with the underlying right coefficient module. -/
def of : M ≃+ RightCentralPolynomialModule f := CentralPolynomialModule.of f

@[simp] theorem smul_of (p : (Polynomial R)ᵐᵒᵖ) (m : M) :
    p • of f m = of f (CentralPolynomialModule.actionHom f (polynomialOpHom R p) m) := rfl

@[simp] theorem C_smul_of (r : R) (m : M) :
    op (Polynomial.C r) • of f m = of f (op r • m) := by simp

@[simp] theorem X_smul_of (m : M) :
    op (Polynomial.X : Polynomial R) • of f m = of f (f m) := by simp

variable {N : Type w} [AddCommGroup N] [Module Rᵐᵒᵖ N]
variable (g : N →ₗ[Rᵐᵒᵖ] N) (h : M →ₗ[Rᵐᵒᵖ] N)

/-- Restrict an intertwining central-polynomial map to right ordinary polynomials. -/
def map (hf : ∀ m, h (f m) = g (h m)) :
    RightCentralPolynomialModule f →ₗ[(Polynomial R)ᵐᵒᵖ] RightCentralPolynomialModule g where
  toFun := CentralPolynomialModule.map f g h hf
  map_add' := (CentralPolynomialModule.map f g h hf).map_add
  map_smul' p m := (CentralPolynomialModule.map f g h hf).map_smul (polynomialOpHom R p) m

@[simp] theorem map_of (hf : ∀ m, h (f m) = g (h m)) (m : M) :
    map f g h hf (of f m) = of g (h m) := rfl

end RightCentralPolynomialModule
end OddMath.QuiverHecke.CyclotomicAction
