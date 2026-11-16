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

end OddMath.SKM.OrientedReduction
