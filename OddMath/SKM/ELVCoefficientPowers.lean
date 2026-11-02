/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleELVSpecialization

/-! # The coefficient-power ideal and the coefficient weight filtration

The finite reservoir quotient in `SwappedDetectingFamily.md` §2 uses powers
of the positive even elementary generators. This is a different ideal from
the weighted coefficient ideal. The bounds here give the two inclusions
needed to compare their quotients, retaining all exterior generators.
-/

noncomputable section
open scoped Classical TensorProduct
namespace OddMath.SKM.SYM
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k]

/-- The paper's powers of the even elementary coefficient generators. -/
def coefficientPowerIdeal (L : I × ℕ → ℕ) : TwoSidedIdeal (SYM D k) :=
  TwoSidedIdeal.span {x | ∃ a : I × ℕ, x = e D k a.1 a.2 ^ L a}

theorem elementary_pow_mem_coefficientAtLeast (a : I × ℕ) (n : ℕ) :
    e D k a.1 a.2 ^ n ∈ CoefficientAtLeast D k (n * elementaryWeight D a) := by
  induction n with
  | zero => simpa using mem_coefficientAtLeast_zero D k (1 : SYM D k)
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact coefficientAtLeast_mul D k ih (elementary_mem_coefficientAtLeast D k a.1 a.2)

/-- High-weight power generators generate a subideal of the weight ideal. -/
theorem coefficientPowerIdeal_le_weight (L : I × ℕ → ℕ) (N : ℕ)
    (hL : ∀ a, N ≤ L a * elementaryWeight D a) :
    coefficientPowerIdeal D k L ≤ coefficientIdeal D k N := by
  apply TwoSidedIdeal.span_le.mpr
  rintro x ⟨a, rfl⟩
  exact (mem_coefficientIdeal_iff D k _ _).mpr
    (coefficientAtLeast_antitone D k (hL a)
      (elementary_pow_mem_coefficientAtLeast D k a (L a)))

/-- A coefficient monomial factors by the entire power of a selected
elementary variable; its exterior factor is kept in its original order. -/
theorem coefficientBasis_factor_elementary (b : CoefficientIndex D) (a : I × ℕ) :
    coefficientBasis D k b = e D k a.1 a.2 ^ b.1 a *
      coefficientBasis D k (b.1.erase a, b.2) := by
  apply (polynomialExteriorEquiv D k).injective
  rw [map_mul, map_pow, coefficientBasis_projection, coefficientBasis_projection]
  change MvPolynomial.monomial b.1 1 ⊗ₜ[k] oddExteriorBasis D k b.2 =
    (polynomialExteriorProjection D k (e D k a.1 a.2)) ^ b.1 a * _
  rw [polynomialExteriorProjection_e, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul,
    Finsupp.single_add_erase]

/-- A power dividing a monomial puts that monomial in the same ideal. -/
theorem coefficientBasis_mem_of_elementary_pow (J : TwoSidedIdeal (SYM D k))
    (b : CoefficientIndex D) (a : I × ℕ) (n : ℕ)
    (hn : n ≤ b.1 a) (hJ : e D k a.1 a.2 ^ n ∈ J) :
    coefficientBasis D k b ∈ J := by
  have hp : e D k a.1 a.2 ^ b.1 a =
      e D k a.1 a.2 ^ n * e D k a.1 a.2 ^ (b.1 a - n) := by
    rw [← pow_add, Nat.add_sub_of_le hn]
  rw [coefficientBasis_factor_elementary D k b a, hp, mul_assoc]
  exact J.mul_mem_right _ _ hJ

theorem coefficientBasis_mem_powerIdeal (L : I × ℕ → ℕ)
    (b : CoefficientIndex D) (a : I × ℕ) (ha : L a ≤ b.1 a) :
    coefficientBasis D k b ∈ coefficientPowerIdeal D k L :=
  coefficientBasis_mem_of_elementary_pow D k _ b a (L a) ha
    (TwoSidedIdeal.subset_span ⟨a, rfl⟩)

theorem coefficientBasis_mem_elvIdeal (cutoff : I → ℕ)
    (b : CoefficientIndex D) (a : I × ℕ)
    (ha : elvElementaryRank D cutoff a.1 ≤ a.2) (hb : 0 < b.1 a) :
    coefficientBasis D k b ∈ elvCoefficientIdeal D k cutoff := by
  apply coefficientBasis_mem_of_elementary_pow D k _ b a 1 hb
  rw [pow_one]
  exact TwoSidedIdeal.subset_span (Or.inl ⟨a.1, a.2, ha, rfl⟩)

variable [Fintype I]

/-- The elementary variables surviving the ELV coefficient relations. -/
def elvPolynomialKeys (cutoff : I → ℕ) : Finset (I × ℕ) :=
  Finset.univ.biUnion fun i =>
    (Finset.range (elvElementaryRank D cutoff i)).image fun r => (i, r)

@[simp] theorem mem_elvPolynomialKeys (cutoff : I → ℕ) (a : I × ℕ) :
    a ∈ elvPolynomialKeys D cutoff ↔ a.2 < elvElementaryRank D cutoff a.1 := by
  simp [elvPolynomialKeys, Prod.ext_iff]

/-- An explicit upper weight of surviving polynomial/exterior monomials. -/
def elvPowerWeightBound (cutoff : I → ℕ) (L : I × ℕ → ℕ) : ℕ :=
  (∑ a ∈ elvPolynomialKeys D cutoff, (L a - 1) * elementaryWeight D a) +
    Fintype.card {i : I // D.parity i = 1}

/-- Every monomial above the finite power bound is killed by the ELV
relations or an elementary power, including all independent exterior factors. -/
theorem coefficientBasis_mem_elv_sup_power (cutoff : I → ℕ) (L : I × ℕ → ℕ)
    (b : CoefficientIndex D)
    (hb : elvPowerWeightBound D cutoff L < coefficientWeight D b) :
    coefficientBasis D k b ∈ elvCoefficientIdeal D k cutoff ⊔ coefficientPowerIdeal D k L := by
  by_contra hmem
  have hsupp : b.1.support ⊆ elvPolynomialKeys D cutoff := by
    intro a ha
    by_contra hkey
    have hr : elvElementaryRank D cutoff a.1 ≤ a.2 := by
      simpa only [mem_elvPolynomialKeys, not_lt] using hkey
    exact hmem ((le_sup_left : elvCoefficientIdeal D k cutoff ≤
      elvCoefficientIdeal D k cutoff ⊔ coefficientPowerIdeal D k L)
      (coefficientBasis_mem_elvIdeal D k cutoff b a hr
        (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha))))
  have he (a : I × ℕ) : b.1 a ≤ L a - 1 := by
    have hlt : b.1 a < L a := by
      by_contra h
      exact hmem ((le_sup_right : coefficientPowerIdeal D k L ≤
        elvCoefficientIdeal D k cutoff ⊔ coefficientPowerIdeal D k L)
        (coefficientBasis_mem_powerIdeal D k L b a (Nat.le_of_not_gt h)))
    omega
  have hp : b.1.sum (fun a n => n * elementaryWeight D a) ≤
      ∑ a ∈ elvPolynomialKeys D cutoff, (L a - 1) * elementaryWeight D a := by
    calc
      b.1.sum (fun a n => n * elementaryWeight D a) ≤
          ∑ a ∈ elvPolynomialKeys D cutoff, b.1 a * elementaryWeight D a :=
        Finset.sum_le_sum_of_subset hsupp
      _ ≤ _ := Finset.sum_le_sum fun a _ => Nat.mul_le_mul_right _ (he a)
  have ho : b.2.card ≤ Fintype.card {i : I // D.parity i = 1} := Finset.card_le_univ _
  exact (Nat.not_lt_of_ge (Nat.add_le_add hp ho)) hb

/-- The upper side of the power/weight ideal sandwich, before taking any
coefficient quotient. It does not assert equality of the two ideals. -/
theorem coefficientIdeal_le_elv_sup_power (cutoff : I → ℕ) (L : I × ℕ → ℕ) :
    coefficientIdeal D k (elvPowerWeightBound D cutoff L + 1) ≤
      elvCoefficientIdeal D k cutoff ⊔ coefficientPowerIdeal D k L := by
  intro x hx
  have hx' : x ∈ CoefficientAtLeast D k (elvPowerWeightBound D cutoff L + 1) :=
    (mem_coefficientIdeal_iff D k _ _).mp hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    change elvPowerWeightBound D cutoff L + 1 ≤ coefficientWeight D b at hb
    exact coefficientBasis_mem_elv_sup_power D k cutoff L b (by omega)
  | zero => exact TwoSidedIdeal.zero_mem _
  | add x y _ _ hx hy => exact TwoSidedIdeal.add_mem _ hx hy
  | smul r x _ hx =>
    simpa only [Algebra.smul_def] using
      (elvCoefficientIdeal D k cutoff ⊔ coefficientPowerIdeal D k L).mul_mem_left
        (algebraMap k _ r) x hx

omit [Fintype I] in
/-- The lower side of the sandwich uses the actual numerical cutoff and
power-weight hypotheses, rather than identifying power and weight truncation. -/
theorem elv_sup_power_le_coefficientIdeal (cutoff : I → ℕ) (L : I × ℕ → ℕ) (N : ℕ)
    (hc : ∀ i, N ≤ cutoff i) (hL : ∀ a, N ≤ L a * elementaryWeight D a) :
    elvCoefficientIdeal D k cutoff ⊔ coefficientPowerIdeal D k L ≤ coefficientIdeal D k N := by
  apply sup_le
  · intro x hx
    exact (mem_coefficientIdeal_iff D k _ _).mpr
      (coefficientAtLeast_antitone D k (Nat.le_succ N)
        ((mem_coefficientIdeal_iff D k _ _).mp (elvCoefficientIdeal_le_weight D k hc hx)))
  · exact coefficientPowerIdeal_le_weight D k L N hL

omit [Fintype I] in
/-- The paper's power quotient retains the bounded polynomial/exterior
window when all its generators have sufficiently high weight. -/
theorem elvPower_quotient_injective (cutoff : I → ℕ) (L : I × ℕ → ℕ) (d N : ℕ)
    (hd : d < N) (hc : ∀ i, N ≤ cutoff i)
    (hL : ∀ a, N ≤ L a * elementaryWeight D a) :
    Function.Injective (fun x : CoefficientAtMost D k d =>
      (elvCoefficientIdeal D k cutoff ⊔ coefficientPowerIdeal D k L).ringCon.mk'
        (x : SYM D k)) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hmem : (x : SYM D k) - y ∈
      elvCoefficientIdeal D k cutoff ⊔ coefficientPowerIdeal D k L :=
    (TwoSidedIdeal.rel_iff _ _ _).mp (Quotient.exact hxy)
  have hw : (x : SYM D k) - y ∈ CoefficientAtLeast D k N :=
    (mem_coefficientIdeal_iff D k _ _).mp
      (elv_sup_power_le_coefficientIdeal D k cutoff L N hc hL hmem)
  exact Submodule.disjoint_def.mp
    (disjoint_coefficientAtMost_coefficientAtLeast D k hd) _
    (Submodule.sub_mem _ x.property y.property) hw

end OddMath.SKM.SYM
