import OddMath.SKM.OrientedReduction
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! Finite coefficient-dependent closure corrections.
The correction need not depend right-linearly on the coefficient. -/
noncomputable section
namespace OddMath.SKM.OrientedReduction
open scoped BigOperators

/-- Finite correction vectors strictly increasing dot count cannot cancel a
nonzero input relation. The columns may depend arbitrarily on each coefficient. -/
theorem eq_zero_of_positive_corrections {A R : Type*} [AddCommMonoid R]
    (dots : A → ℕ) (f : A →₀ R) (r : A → A →₀ R)
    (hr : ∀ i j, j ∈ (r i).support → dots i < dots j)
    (hz : (∑ i ∈ f.support, (Finsupp.single i (f i) + r i)) = 0) : f = 0 := by
  classical
  apply eq_zero_of_crossing_dot_coefficients (fun _ : A => 0) dots
    (fun i j p => (Finsupp.single j p + r j) i)
  · intro i j p h; omega
  · intro i j p _ hij
    have hne : i ≠ j := by intro h; subst j; omega
    have hr0 : r j i = 0 := by
      by_contra hne
      have hi := Finsupp.mem_support_iff.mpr hne
      have := hr j i hi
      omega
    simp [Finsupp.single_eq_of_ne hne, hr0]
  · intro i j p _ hij hne
    have hr0 : r j i = 0 := by
      by_contra hne
      have hi := Finsupp.mem_support_iff.mpr hne
      have := hr j i hi
      omega
    simp [Finsupp.single_eq_of_ne (Ne.symm hne), hr0]
  · intro i p hp
    have hr0 : r i i = 0 := by
      by_contra hne
      have hi := Finsupp.mem_support_iff.mpr hne
      exact (Nat.lt_irrefl _) (hr i i hi)
    simpa [hr0] using hp
  · intro i
    have H := congrArg (fun g : A →₀ R => g i) hz
    simpa only [Finsupp.finsetSum_apply, Finsupp.zero_apply] using H

/-- Injectivity descends through a linear closure with finite strictly
positive-dot corrections. Correction lifts may depend on the entire input
coefficient; no right-coefficient linearity is assumed. -/
theorem injective_of_positive_closure
    {k R A M N : Type*} [CommRing k] [AddCommGroup R] [Module k R]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (dots : A → ℕ) (weak : (A →₀ R) →ₗ[k] M) (strong : (A →₀ R) →ₗ[k] N)
    (closure : M →ₗ[k] N) (hinj : Function.Injective strong)
    (h : ∀ i p, ∃ r : A →₀ R, (∀ j ∈ r.support, dots i < dots j) ∧
      closure (weak (Finsupp.single i p)) = strong (Finsupp.single i p + r)) :
    Function.Injective weak := by
  classical
  have hz : ∀ f, weak f = 0 → f = 0 := by
    intro f hf
    choose r hr he using fun i => h i (f i)
    have H : strong (∑ i ∈ f.support, (Finsupp.single i (f i) + r i)) = 0 := by
      calc
        _ = ∑ i ∈ f.support, closure (weak (Finsupp.single i (f i))) := by
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact (he i).symm
        _ = closure (weak (∑ i ∈ f.support, Finsupp.single i (f i))) := by
          simp only [map_sum]
        _ = closure (weak f) := by
          change closure (weak (f.sum Finsupp.single)) = _
          rw [Finsupp.sum_single]
        _ = 0 := by rw [hf, map_zero]
    have H0 : (∑ i ∈ f.support, (Finsupp.single i (f i) + r i)) = 0 :=
      hinj (H.trans strong.map_zero.symm)
    exact eq_zero_of_positive_corrections dots f r hr H0
  intro f g hfg
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hfg, sub_self]

end OddMath.SKM.OrientedReduction
