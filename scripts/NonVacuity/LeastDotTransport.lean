import OddMath.SKM.BubbleSpecialization
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
Least-dot and greatest-pivot detection for finite coefficient families.
These are the additive triangular arguments used by elementary and contextual sorting.
These checks neither construct SKM transport nor prove upward independence.
-/

open scoped BigOperators
namespace NonVacuity.LeastDotTransport

/-- If transport fixes the constant coefficient and sends zero to zero, a
finite family with every transported coefficient zero is itself zero.
No multiplication, commutativity, domain or finite-dimensionality is needed. -/
theorem eq_zero_of_coefficients {M : Type*} [AddCommMonoid M]
    (rho : M → ℕ → M) (hzero : ∀ n, rho 0 n = 0)
    (hconstant : ∀ p, rho p 0 = p) (f : ℕ →₀ M)
    (h : ∀ n, (∑ a ∈ f.support, if a ≤ n then rho (f a) (n - a) else 0) = 0) :
    f = 0 := by
  classical
  ext n
  change f n = 0
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := h n
    rw [Finset.sum_eq_single n] at hn
    · simpa only [le_refl, ite_true, Nat.sub_self, hconstant] using hn
    · intro a _ han
      by_cases hle : a ≤ n
      · have ha : f a = 0 := ih a (by omega)
        simp only [hle, ite_true, ha, hzero]
      · simp only [hle, ite_false]
    · intro hn
      have ha : f n = 0 := Finsupp.notMem_support_iff.mp hn
      simp only [ha, hzero, ite_self]

/-- An upper triangular coefficient array with zero-reflecting diagonal
detects every nonzero finite family by its greatest occupied row.
The coefficient object may itself be an infinite residual-label module. -/
theorem eq_zero_of_upper_coefficients {M : Type*} [AddCommMonoid M]
    (entry : ℕ → ℕ → M → M)
    (hbelow : ∀ i j p, j < i → entry i j p = 0)
    (hdiag : ∀ i p, entry i i p = 0 → p = 0) (f : ℕ →₀ M)
    (h : ∀ i, (∑ j ∈ f.support, entry i j (f j)) = 0) : f = 0 := by
  classical
  by_contra hf
  have hs := Finsupp.support_nonempty_iff.mpr hf
  let b := f.support.max' hs
  have hb : b ∈ f.support := Finset.max'_mem _ hs
  have hz := h b
  rw [Finset.sum_eq_single b] at hz
  · exact (Finsupp.mem_support_iff.mp hb) (hdiag b (f b) hz)
  · intro j hj hjb
    have hjle : j ≤ b := Finset.le_max' _ j hj
    exact hbelow b j (f j) (by omega)
  · intro hnot
    exact False.elim (hnot hb)

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ
private def A : Mat := !![1, 1; 0, 0]
private def B : Mat := !![0, 0; 1, 0]

/-- A concrete coefficient transport with a positive-degree correction. -/
private def rhoMatrix (p : Mat) (n : ℕ) : Mat :=
  if n = 0 then p else if n = 2 then A * p else 0

private theorem rhoMatrix_zero (n : ℕ) : rhoMatrix 0 n = 0 := by
  simp [rhoMatrix]

private theorem rhoMatrix_constant (p : Mat) : rhoMatrix p 0 = p := by
  simp [rhoMatrix]

/-- The matrix coefficients do not commute; no scalar-domain argument applies. -/
example : A * B ≠ B * A := by decide

private noncomputable def family : ℕ →₀ Mat :=
  Finsupp.single 0 B - Finsupp.single 2 (A * B)

/-- Apply the detection theorem to a concrete nonzero finite family, with
all transport hypotheses discharged. This is an additive matrix example,
not an odd SKM action over the integers. -/
theorem matrix_family_detected : ∃ n,
    (∑ a ∈ family.support,
      if a ≤ n then rhoMatrix (family a) (n - a) else 0) ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ n, (∑ a ∈ family.support,
      if a ≤ n then rhoMatrix (family a) (n - a) else 0) = 0 := by
    intro n
    exact Classical.byContradiction (fun hn => h ⟨n, hn⟩)
  have hf := eq_zero_of_coefficients rhoMatrix rhoMatrix_zero rhoMatrix_constant family hz
  have he := congrArg (fun f : ℕ →₀ Mat => f 0 1 0) hf
  norm_num [family, B, Finsupp.single_apply] at he

#print axioms eq_zero_of_coefficients
#print axioms matrix_family_detected

private def upperMatrix (i j : ℕ) (p : Mat) : Mat :=
  if j < i then 0 else if j = i then p else A * p

/-- A concrete upper triangular application with noncommuting coefficient
corrections, discharging both the support and diagonal conditions. -/
theorem matrix_upper_detected : ∃ i,
    (∑ j ∈ family.support, upperMatrix i j (family j)) ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ i, (∑ j ∈ family.support, upperMatrix i j (family j)) = 0 := by
    intro i
    exact Classical.byContradiction (fun hi => h ⟨i, hi⟩)
  have hf := eq_zero_of_upper_coefficients upperMatrix
    (fun i j p hij => by simp [upperMatrix, hij])
    (fun i p hp => by simpa [upperMatrix] using hp) family hz
  have he := congrArg (fun f : ℕ →₀ Mat => f 0 1 0) hf
  norm_num [family, B, Finsupp.single_apply] at he

#print axioms eq_zero_of_upper_coefficients
#print axioms matrix_upper_detected
end NonVacuity.LeastDotTransport
