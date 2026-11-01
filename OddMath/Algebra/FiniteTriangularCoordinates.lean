import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic

/-! # Finite triangular operators on module-valued coordinates

The negative crossing matrix in DeformedRouquierMatrix §4 uses this
finite elimination result over an arbitrary commutative scalar ring.
Only the strict finite-coordinate error is nilpotent; no coefficient
commutativity beyond the ground ring or finite-dimensionality is assumed.
-/
noncomputable section
namespace OddMath.FiniteTriangularCoordinates
open scoped BigOperators

private def pointwiseEquiv {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]
    (m : ℕ) (L : M ≃ₗ[k] M) : (Fin m → M) ≃ₗ[k] (Fin m → M) where
  toFun f i := L (f i)
  invFun f i := L.symm (f i)
  left_inv f := by ext i; exact L.symm_apply_apply (f i)
  right_inv f := by ext i; exact L.apply_symm_apply (f i)
  map_add' f g := by ext i; exact map_add L (f i) (g i)
  map_smul' c f := by ext i; exact map_smul L c (f i)

/-- Finite lower-triangular elimination for module-valued coordinates.
The concrete cap operator below supplies both hypotheses. -/
theorem bijective {k M : Type*}
    [CommRing k] [AddCommGroup M] [Module k M] (m : ℕ)
    (F : (Fin m → M) →ₗ[k] (Fin m → M)) (L : M ≃ₗ[k] M)
    (hzero : ∀ a b : Fin m, a < b → ∀ x : M, F (Pi.single b x) a = 0)
    (hdiag : ∀ a : Fin m, ∀ x : M, F (Pi.single a x) a = L x) :
    Function.Bijective F := by
  classical
  let D := pointwiseEquiv m L
  let N : Module.End k (Fin m → M) := 1 - D.symm.toLinearMap.comp F
  have hsingle (a b : Fin m) (hab : a ≤ b) (x : M) :
      N (Pi.single b x) a = 0 := by
    change Pi.single b x a - L.symm (F (Pi.single b x) a) = 0
    by_cases he : a = b
    · subst b
      rw [Pi.single_eq_same, hdiag, LinearEquiv.symm_apply_apply, sub_self]
    · have hlt : a < b := lt_of_le_of_ne hab he
      simp only [Pi.single_eq_of_ne he, hzero a b hlt x, map_zero, sub_self]
  have hrow (a : Fin m) (f : Fin m → M)
      (hf : ∀ b : Fin m, b < a → f b = 0) : N f a = 0 := by
    have hs : f = ∑ b : Fin m, Pi.single b (f b) := by
      ext b
      simp [Pi.single_apply]
    rw [hs, map_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : b < a
    · simp only [hf b hb, Pi.single_zero, map_zero, Pi.zero_apply]
    · exact hsingle a b (le_of_not_gt hb) (f b)
  have hp : ∀ n : ℕ, ∀ f : Fin m → M, ∀ a : Fin m,
      a.val < n → ((N ^ n) f) a = 0 := by
    intro n
    induction n with
    | zero => intro f a ha; omega
    | succ n ih =>
      intro f a ha
      rw [pow_succ']
      change N ((N ^ n) f) a = 0
      apply hrow
      intro b hb
      exact ih f b (by have : b.val < a.val := hb; omega)
  have hn : N ^ m = 0 := by
    ext f a
    exact hp m f a a.isLt
  have hu := (show IsNilpotent N from ⟨m, hn⟩).isUnit_one_sub
  have ht : IsUnit (D.symm.toLinearMap.comp F) := by
    simpa only [N, sub_sub_cancel] using hu
  have hb := (Module.End.isUnit_iff (D.symm.toLinearMap.comp F)).mp ht
  constructor
  · intro f g hfg
    apply hb.1
    change D.symm (F f) = D.symm (F g)
    rw [hfg]
  · intro f
    obtain ⟨g, hg⟩ := hb.2 (D.symm f)
    exact ⟨g, D.symm.injective hg⟩

end OddMath.FiniteTriangularCoordinates
