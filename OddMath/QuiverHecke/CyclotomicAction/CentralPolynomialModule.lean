/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Central polynomial modules

The central polynomial extension of an ordinary (possibly noncommutative) ring acts
on a module equipped with a linear endomorphism. This is infrastructure for the
polynomial actions in the cyclotomic construction.
-/

noncomputable section

namespace OddMath.QuiverHecke.CyclotomicAction

universe u v w

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The underlying additive group, with its polynomial action specified by `f`. -/
def CentralPolynomialModule (_f : M →ₗ[R] M) := M

namespace CentralPolynomialModule

variable (f : M →ₗ[R] M)

instance : AddCommGroup (CentralPolynomialModule f) := inferInstanceAs (AddCommGroup M)

/-- Canonical additive identification with the original module. -/
def of : M ≃+ CentralPolynomialModule f := AddEquiv.refl M

/-- Evaluation in additive endomorphisms; linearity supplies centrality of `X`. -/
def actionHom : Polynomial R →+* AddMonoid.End M :=
  Polynomial.eval₂RingHom' (Module.toAddMonoidEnd R M) f.toAddMonoidHom (fun r => by
    apply AddMonoidHom.ext
    intro m
    exact (f.map_smul r m).symm)

instance : Module (Polynomial R) (CentralPolynomialModule f) :=
  Module.compHom M (actionHom f)

@[simp] theorem smul_of (p : Polynomial R) (m : M) :
    p • of f m = of f (actionHom f p m) := rfl

@[simp] theorem of_symm_smul (p : Polynomial R) (m : CentralPolynomialModule f) :
    (of f).symm (p • m) = actionHom f p ((of f).symm m) := rfl

@[simp] theorem actionHom_C (r : R) (m : M) :
    actionHom f (Polynomial.C r) m = r • m := by
  change (Polynomial.eval₂ (Module.toAddMonoidEnd R M) f.toAddMonoidHom
    (Polynomial.C r)) m = r • m
  rw [Polynomial.eval₂_C]
  rfl

@[simp] theorem actionHom_X (m : M) :
    actionHom f Polynomial.X m = f m := by
  change (Polynomial.eval₂ (Module.toAddMonoidEnd R M) f.toAddMonoidHom
    Polynomial.X) m = f m
  rw [Polynomial.eval₂_X]
  rfl

@[simp] theorem C_smul_of (r : R) (m : M) :
    Polynomial.C r • of f m = of f (r • m) := by simp

@[simp] theorem X_smul_of (m : M) :
    (Polynomial.X : Polynomial R) • of f m = of f (f m) := by simp

variable {N : Type w} [AddCommGroup N] [Module R N]
variable (g : N →ₗ[R] N) (h : M →ₗ[R] N)

/-- Intertwining the distinguished endomorphisms implies intertwining every polynomial. -/
theorem map_actionHom (hf : ∀ m, h (f m) = g (h m)) (p : Polynomial R) (m : M) :
    h (actionHom f p m) = actionHom g p (h m) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add]
    change h (actionHom f p m + actionHom f q m) = _ + _
    rw [map_add, hp, hq]
  | monomial n r =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow]
    change h (actionHom f (Polynomial.C r) ((actionHom f Polynomial.X ^ n) m)) =
      actionHom g (Polynomial.C r) ((actionHom g Polynomial.X ^ n) (h m))
    rw [actionHom_C, actionHom_C, h.map_smul]
    congr 1
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change h (actionHom f Polynomial.X ((actionHom f Polynomial.X ^ n) m)) =
        actionHom g Polynomial.X ((actionHom g Polynomial.X ^ n) (h m))
      rw [actionHom_X, actionHom_X, hf, ih]

/-- An intertwining linear map, bundled over the central polynomial ring. -/
def map (hf : ∀ m, h (f m) = g (h m)) :
    CentralPolynomialModule f →ₗ[Polynomial R] CentralPolynomialModule g where
  toFun := fun m => of g (h ((of f).symm m))
  map_add' := by intros; exact h.map_add _ _
  map_smul' := by intros; exact map_actionHom f g h hf _ _

@[simp] theorem map_of (hf : ∀ m, h (f m) = g (h m)) (m : M) :
    map f g h hf (of f m) = of g (h m) := rfl

end CentralPolynomialModule
end OddMath.QuiverHecke.CyclotomicAction
