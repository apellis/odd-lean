import OddMath.SkewPolynomial
import Mathlib.Order.Hom.Basic

/-!
# Order-preserving variable embeddings of the integer skew-polynomial model

Zero extension along any order embedding preserves the actual natural crossing
count and hence the multiplication of `OddMath.SkewPolynomial`.
Source convention: EKL arXiv:1111.1320v1 §2.1.1 (2.1), p.3; increasing-index
normal order in the sign convention and the translation table.
This is a model-side result, not a quotient/PBW theorem.
-/
namespace OddMath.Frontier.VariableEmbedding

open scoped BigOperators
open OddMath.SkewPolynomial

variable {m n : ℕ}

/-- Extend exponent vectors by zero outside the chosen ordered variables. -/
noncomputable def expEmbed (e : Fin m ↪o Fin n) (a : Fin m → ℕ) : Fin n → ℕ :=
  Function.extend e a 0

@[simp] theorem expEmbed_apply (e : Fin m ↪o Fin n) (a : Fin m → ℕ) (i : Fin m) :
    expEmbed e a (e i) = a i :=
  e.injective.extend_apply a 0 i

theorem expEmbed_not_mem_range (e : Fin m ↪o Fin n) (a : Fin m → ℕ)
    (j : Fin n) (h : j ∉ Set.range e) : expEmbed e a j = 0 :=
  Function.extend_apply' (f := e) a (0 : Fin n → ℕ) j h

@[simp] theorem expEmbed_zero (e : Fin m ↪o Fin n) : expEmbed e 0 = 0 := by
  funext j
  by_cases h : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := h
    simp
  · exact expEmbed_not_mem_range e 0 j h

@[simp] theorem expEmbed_add (e : Fin m ↪o Fin n) (a b : Fin m → ℕ) :
    expEmbed e (a + b) = expEmbed e a + expEmbed e b := by
  funext j
  by_cases h : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := h
    simp
  · simp [Pi.add_apply, expEmbed_not_mem_range e _ j h]

theorem expEmbed_injective (e : Fin m ↪o Fin n) : Function.Injective (expEmbed e) := by
  intro a b h
  funext i
  simpa using congrFun h (e i)

/-- Reindex a finite sum whose summands vanish outside the image. -/
theorem sum_range (e : Fin m ↪o Fin n) (f : Fin n → ℕ)
    (hf : ∀ j, j ∉ Set.range e → f j = 0) :
    ∑ j, f j = ∑ i, f (e i) := by
  classical
  calc
    ∑ j, f j = ∑ j ∈ Finset.univ.image e, f j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      exact hf j (by simpa using hj)
    _ = ∑ i, f (e i) := Finset.sum_image (fun _ _ _ _ h => e.injective h)

/-- Exact crossing counts, not merely parity, survive zero extension. -/
theorem crossingCount_expEmbed (e : Fin m ↪o Fin n) (a b : Fin m → ℕ) :
    OddMath.crossingCount (expEmbed e a) (expEmbed e b) =
      OddMath.crossingCount a b := by
  classical
  simp only [OddMath.crossingCount, Finset.sum_filter]
  rw [sum_range e _ (by
    intro i hi
    simp [expEmbed_not_mem_range e a i hi])]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_range e _ (by
    intro j hj
    simp [expEmbed_not_mem_range e b j hj])]
  simp

@[simp] theorem skewSign_expEmbed (e : Fin m ↪o Fin n) (a b : Fin m → ℕ) :
    OddMath.skewSign (expEmbed e a) (expEmbed e b) = OddMath.skewSign a b := by
  simp only [OddMath.skewSign, crossingCount_expEmbed]

/-- Transport finite-support integer coefficients by the injective exponent map. -/
noncomputable def embed (e : Fin m ↪o Fin n) (f : SkewPolynomial m) : SkewPolynomial n :=
  Finsupp.embDomain ⟨expEmbed e, expEmbed_injective e⟩ f

@[simp] theorem embed_monomial (e : Fin m ↪o Fin n) (a : Fin m → ℕ) (c : ℤ) :
    embed e (monomial a c) = monomial (expEmbed e a) c :=
  Finsupp.embDomain_single _ _ _

@[simp] theorem embed_zero (e : Fin m ↪o Fin n) : embed e 0 = 0 :=
  Finsupp.embDomain_zero _

@[simp] theorem embed_add (e : Fin m ↪o Fin n) (f g : SkewPolynomial m) :
    embed e (f + g) = embed e f + embed e g :=
  Finsupp.embDomain_add _ _ _

@[simp] theorem embed_one (e : Fin m ↪o Fin n) : embed e one = one := by
  simp [one]

theorem embed_injective (e : Fin m ↪o Fin n) : Function.Injective (embed e) :=
  Finsupp.embDomain_injective _

/-- Multiplicativity for arbitrary finite-support polynomials and all ranks. -/
@[simp] theorem embed_mul (e : Fin m ↪o Fin n) (f g : SkewPolynomial m) :
    embed e (mul f g) = mul (embed e f) (embed e g) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [zero_mul]
  | add f₁ f₂ ih₁ ih₂ => simp only [add_mul, embed_add, ih₁, ih₂]
  | single a r =>
    induction g using Finsupp.induction_linear with
    | zero => simp [mul_zero]
    | add g₁ g₂ ih₁ ih₂ => simp only [mul_add, embed_add, ih₁, ih₂]
    | single b s =>
      change embed e (mul (monomial a r) (monomial b s)) =
        mul (embed e (monomial a r)) (embed e (monomial b s))
      simp only [mul_monomial, embed_monomial, expEmbed_add, skewSign_expEmbed]

end OddMath.Frontier.VariableEmbedding
