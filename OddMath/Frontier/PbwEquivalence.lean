import OddMath.Frontier.PbwRealization
import OddMath.Frontier.PbwNormalization
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Integral PBW equivalence in every rank

The actual EKL presentation (arXiv:1111.1320v1, §2.1.1, (2.1)) is equivalent
to the integer skew-polynomial model. We combine quotient-side normal-order
spanning with the exact model image of each increasing canonical word.
No uniqueness of normal forms is assumed. Repeated indices are retained.
-/

namespace OddMath.Frontier.PbwEquivalence

open PbwL2 PbwL3 PbwNormalization
open OddMath.SkewPolynomial

variable {n : ℕ}

/-- The normalization parent's canonical monomial has coefficient +1.
The two parent word evaluators agree definitionally; their chosen sorted
lists need not agree definitionally, and no such equality is used here. -/
@[simp] theorem Phi_orderedMonomial (a : Fin n → ℕ) :
    Phi n (orderedMonomial a) = monomial a 1 := by
  have h := PbwRealization.Phi_word_of_sorted (canonicalWord a) (canonicalWord_sorted a)
  have he : PbwRealization.exponents (canonicalWord a) = a := by
    funext i
    exact canonicalWord_count a i
  simpa only [he] using h

/-- Explicit finite coefficient-linear combination in the actual quotient. -/
noncomputable def lift (n : ℕ) : SkewPolynomial n →ₗ[ℤ] Presented n :=
  Finsupp.linearCombination ℤ orderedMonomial

theorem lift_apply (f : SkewPolynomial n) :
    lift n f = f.sum (fun a c => c • orderedMonomial a) := rfl

@[simp] theorem lift_monomial (a : Fin n → ℕ) (c : ℤ) :
    lift n (monomial a c) = c • orderedMonomial a :=
  Finsupp.linearCombination_single ℤ c a

/-- Model-side coefficient induction proves a right inverse without any
quotient independence assumption. -/
@[simp] theorem Phi_lift (f : SkewPolynomial n) : Phi n (lift n f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single a c =>
    change Phi n (lift n (monomial a c)) = monomial a c
    rw [lift_monomial, map_zsmul, Phi_orderedMonomial, ← PbwL4.monomial_smul]

/-- The indispensable quotient-side step: every quotient element has the
parent's finite ordered expansion, so the explicit lift is also a left inverse. -/
@[simp] theorem lift_Phi (x : Presented n) : lift n (Phi n x) = x := by
  obtain ⟨c, hc⟩ := exists_ordered_expansion x
  change lift n c = x at hc
  rw [← hc, Phi_lift]

/-- Injectivity for every rank, including rank zero. -/
theorem Phi_injective (n : ℕ) : Function.Injective (Phi n) :=
  Function.LeftInverse.injective (lift_Phi (n := n))

/-- The earlier surjectivity result now joins genuine quotient injectivity. -/
theorem Phi_bijective (n : ℕ) : Function.Bijective (Phi n) :=
  ⟨Phi_injective n, PbwRealization.Phi_surjective n⟩

/-- Ring equivalence on the existing source and target ring instances.
Its forward map is precisely the original presentation map. -/
noncomputable def presentedEquiv (n : ℕ) : Presented n ≃+* SkewPolynomial n :=
  RingEquiv.ofBijective (Phi n) (Phi_bijective n)

@[simp] theorem presentedEquiv_apply (x : Presented n) :
    presentedEquiv n x = Phi n x := rfl

theorem presentedEquiv_toRingHom (n : ℕ) : (presentedEquiv n).toRingHom = Phi n := rfl

@[simp] theorem presentedEquiv_symm_apply (f : SkewPolynomial n) :
    (presentedEquiv n).symm f = lift n f := by
  apply Phi_injective n
  exact (presentedEquiv n).apply_symm_apply f |>.trans (Phi_lift f).symm

/-- The same forward map as an integer-linear coordinate equivalence,
with the explicit coefficient lift as inverse. -/
noncomputable def coefficientEquiv (n : ℕ) : Presented n ≃ₗ[ℤ] SkewPolynomial n where
  toFun := Phi n
  invFun := lift n
  left_inv := lift_Phi
  right_inv := Phi_lift
  map_add' := map_add (Phi n)
  map_smul' := fun c x => map_zsmul (Phi n) c x

/-- Transport the genuine coefficient basis, not an assumed quotient basis. -/
noncomputable def orderedBasis (n : ℕ) : Basis (Fin n → ℕ) ℤ (Presented n) :=
  Finsupp.basisSingleOne.map (coefficientEquiv n).symm

@[simp] theorem orderedBasis_apply (a : Fin n → ℕ) :
    orderedBasis n a = orderedMonomial a := by
  change lift n (monomial a 1) = orderedMonomial a
  rw [lift_monomial, one_smul]

/-- The PBW coordinates are exactly the existing Phi coefficients. -/
@[simp] theorem orderedBasis_repr (x : Presented n) :
    (orderedBasis n).repr x = Phi n x := rfl

/-- Uniqueness is a conclusion, not an assumption of normalization. -/
theorem ordered_expansion_unique (c d : (Fin n → ℕ) →₀ ℤ)
    (h : c.sum (fun a r => r • orderedMonomial a) =
      d.sum (fun a r => r • orderedMonomial a)) : c = d := by
  have he := congrArg (Phi n) h
  change Phi n (lift n c) = Phi n (lift n d) at he
  simpa only [Phi_lift] using he

end OddMath.Frontier.PbwEquivalence
