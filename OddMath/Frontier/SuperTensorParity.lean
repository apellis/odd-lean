import OddMath.Frontier.SuperTensor

/-!
# Parity submodules and the homogeneous super tensor law

Ellis arXiv:1111.3932v1 §2.1, unnumbered tensor multiplication display.
The degree used here is the sum of exponents (odd parity), not the doubled
integer grading. All products are the inherited named skew multiplication.
-/

noncomputable section
open scoped TensorProduct
open OddMath.SkewPolynomial
open OddMath.Frontier.SuperTensor

namespace OddMath.Frontier.SuperTensorParity

abbrev Parity := Fin 2

def exponentParity {n : ℕ} (a : Fin n → ℕ) : Parity :=
  ⟨degree a % 2, Nat.mod_lt _ (by decide)⟩

def parityAdd (p q : Parity) : Parity :=
  ⟨(p.val + q.val) % 2, Nat.mod_lt _ (by decide)⟩

/-- Support containment, allowing cancellation and allowing zero in both pieces. -/
def paritySubmodule (n : ℕ) (p : Parity) : Submodule ℤ (SkewPolynomial n) where
  carrier := {f | ∀ a, f a ≠ 0 → degree a % 2 = p.val}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg a ha
    by_cases hfa : f a = 0
    · apply hg a
      simpa [Finsupp.add_apply, hfa] using ha
    · exact hf a hfa
  smul_mem' := by
    intro r f hf a ha
    apply hf a
    intro hfa
    apply ha
    simp [Finsupp.smul_apply, hfa]

@[simp] theorem mem_paritySubmodule {n : ℕ} {p : Parity} {f : SkewPolynomial n} :
    f ∈ paritySubmodule n p ↔ ∀ a, f a ≠ 0 → degree a % 2 = p.val := Iff.rfl

theorem zero_mem (n : ℕ) (p : Parity) : (0 : SkewPolynomial n) ∈ paritySubmodule n p :=
  (paritySubmodule n p).zero_mem

theorem add_mem {n : ℕ} {p : Parity} {f g : SkewPolynomial n}
    (hf : f ∈ paritySubmodule n p) (hg : g ∈ paritySubmodule n p) :
    f + g ∈ paritySubmodule n p := (paritySubmodule n p).add_mem hf hg

theorem smul_mem {n : ℕ} {p : Parity} (r : ℤ) {f : SkewPolynomial n}
    (hf : f ∈ paritySubmodule n p) : r • f ∈ paritySubmodule n p :=
  (paritySubmodule n p).smul_mem r hf

theorem degree_add {n : ℕ} (a b : Fin n → ℕ) : degree (a+b) = degree a + degree b := by
  simp [degree, Finset.sum_add_distrib]

theorem monomial_mem {n : ℕ} {p : Parity} (a : Fin n → ℕ) (r : ℤ)
    (ha : degree a % 2 = p.val) : monomial a r ∈ paritySubmodule n p := by
  intro b hb
  by_cases h : a = b
  · subst b
    exact ha
  · exact False.elim (hb (Finsupp.single_eq_of_ne h))

/-- Each summand has the desired parity; sums may cancel without harming containment. -/
theorem mul_mem {n : ℕ} {p q : Parity} {f g : SkewPolynomial n}
    (hf : f ∈ paritySubmodule n p) (hg : g ∈ paritySubmodule n q) :
    mul f g ∈ paritySubmodule n (parityAdd p q) := by
  classical
  unfold mul Finsupp.sum
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.sum_mem
  intro b hb
  apply monomial_mem
  rw [degree_add, Nat.add_mod, hf a (Finsupp.mem_support_iff.mp ha),
    hg b (Finsupp.mem_support_iff.mp hb)]
  rfl

/-- Reduce only supported middle exponents to their given parities. -/
theorem koszul_of_parity {m n : ℕ} (b : Fin n → ℕ) (c : Fin m → ℕ)
    {p q : Parity} (hb : degree b % 2 = p.val) (hc : degree c % 2 = q.val) :
    koszul b c = (-1 : ℤ) ^ (p.val * q.val) := by
  unfold koszul
  rw [neg_one_pow_eq_pow_mod_two, Nat.mul_mod, hb, hc]
  exact (neg_one_pow_eq_pow_mod_two _).symm

/-- The existing multiplication expanded in products of supported monomials. -/
theorem mul_eq_sum {n : ℕ} (f h : SkewPolynomial n) :
    mul f h = ∑ a ∈ f.support, ∑ c ∈ h.support,
      mul (monomial a (f a)) (monomial c (h c)) := by
  simp only [mul_monomial]
  rfl

/-- Source super tensor rule. Only the first right and second left factors
need a parity; the outer factors are entirely arbitrary. -/
theorem tensorMul_tmul_of_parity {m n : ℕ}
    (f h : SkewPolynomial m) (g k : SkewPolynomial n) {p q : Parity}
    (hg : g ∈ paritySubmodule n p) (hh : h ∈ paritySubmodule m q) :
    tensorMul (f ⊗ₜ[ℤ] g) (h ⊗ₜ[ℤ] k) =
      (-1 : ℤ) ^ (p.val * q.val) • (mul f h ⊗ₜ[ℤ] mul g k) := by
  classical
  rw [tensorMul_tmul]
  simp only [Finsupp.sum]
  have signs :
      (∑ a ∈ f.support, ∑ b ∈ g.support, ∑ c ∈ h.support, ∑ d ∈ k.support,
        koszul b c • (mul (monomial a (f a)) (monomial c (h c)) ⊗ₜ[ℤ]
          mul (monomial b (g b)) (monomial d (k d)))) =
      ∑ a ∈ f.support, ∑ b ∈ g.support, ∑ c ∈ h.support, ∑ d ∈ k.support,
        (-1 : ℤ) ^ (p.val * q.val) •
          (mul (monomial a (f a)) (monomial c (h c)) ⊗ₜ[ℤ]
            mul (monomial b (g b)) (monomial d (k d))) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d _
    rw [koszul_of_parity b c (hg b (Finsupp.mem_support_iff.mp hb))
      (hh c (Finsupp.mem_support_iff.mp hc))]
  rw [signs]
  simp only [← Finset.smul_sum]
  congr 1
  rw [mul_eq_sum f h, mul_eq_sum g k]
  simp only [TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

end OddMath.Frontier.SuperTensorParity
