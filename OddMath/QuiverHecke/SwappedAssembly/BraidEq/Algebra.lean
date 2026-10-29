/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SlideAssembly

/-! # The correction terms of the braid relation from a nil-Hecke slide

For the relation (1.9) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, at `Eᵢ Eⱼ Eᵢ` with `i ≠ j`, the difference of the two sides on a summand path
reduces, after conjugation by the mixed interchanges, to the commutator of a same-colour
crossing `ψ` of the two `i`-letters with the parameter polynomial `Q_ij` in a dot `x₁` (left
`i`-letter) or `x₂` (right `i`-letter) and a dot `y` on the `j`-letter. The nil-Hecke slide
`ψ x₁ - q x₂ ψ = 1` turns this commutator into the divided differences of `Q_ij`
(`comp_qExpr_sub`), which are the correction terms of (1.9) with the dots multiplied by the
sign `ε = (-1)^{pᵢ pⱼ}` of the conjugation.

## Main results

* `comp_pow_sub`: `ψ x₁ⁿ - qⁿ x₂ⁿ ψ = ∑_{a < n} qᵃ x₂ᵃ x₁ⁿ⁻¹⁻ᵃ`.
* `comp_qExpr_sub`: the commutator of `ψ` with `Q_ij` is the correction term of (1.9).
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k] {D : Datum I X}
  {Sc : Scalars D k}

namespace ProbeReservoir

section Algebra

variable {C : Type*} [Category C] [Preadditive C] [Linear k C]

/-- A slide relation `ψ x₁ - q x₂ ψ = 1` gives the divided differences of the powers. -/
theorem comp_pow_sub {A : C} (ψ x₁ x₂ : End A) (q : k)
    (h : ψ ≫ x₁ - q • (x₂ ≫ ψ) = 𝟙 A) : ∀ n : ℕ,
    ψ ≫ (x₁ ^ n : End A) - q ^ n • ((x₂ ^ n : End A) ≫ ψ) =
      ∑ a ∈ Finset.range n, q ^ a • ((x₂ ^ a : End A) ≫ (x₁ ^ (n - 1 - a) : End A))
  | 0 => by simp [End.one_def]
  | n + 1 => by
    have ih := comp_pow_sub ψ x₁ x₂ q h n
    have h' : ψ ≫ x₁ = q • (x₂ ≫ ψ) + 𝟙 A := by rw [← h]; abel
    have ih' : ψ ≫ (x₁ ^ n : End A) = q ^ n • ((x₂ ^ n : End A) ≫ ψ) +
        ∑ a ∈ Finset.range n, q ^ a • ((x₂ ^ a : End A) ≫ (x₁ ^ (n - 1 - a) : End A)) := by
      rw [← ih]; abel
    rw [Finset.sum_range_succ, show n + 1 - 1 - n = 0 by omega, pow_zero, End.one_def,
      Category.comp_id]
    have hs : ∑ a ∈ Finset.range n, q ^ a • ((x₂ ^ a : End A) ≫ (x₁ ^ (n + 1 - 1 - a) : End A)) =
        (∑ a ∈ Finset.range n, q ^ a • ((x₂ ^ a : End A) ≫ (x₁ ^ (n - 1 - a) : End A))) ≫ x₁ := by
      rw [Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_range] at ha
      rw [Linear.smul_comp, Category.assoc, show n + 1 - 1 - a = (n - 1 - a) + 1 by omega,
        pow_succ', End.mul_def]
    rw [hs, pow_succ' x₁, End.mul_def, ← Category.assoc, ih', Preadditive.add_comp,
      Linear.smul_comp, Category.assoc, h', pow_succ' x₂, End.mul_def, pow_succ]
    simp only [Preadditive.comp_add, Linear.comp_smul, Category.comp_id, smul_add, smul_smul,
      Category.assoc]
    abel

private theorem comp_pow_signed' {A : C} (g a' a : End A) (e : k)
    (h : g ≫ a = e • (a' ≫ g)) : ∀ n : ℕ, g ≫ (a ^ n : End A) = e ^ n • ((a' ^ n : End A) ≫ g)
  | 0 => by simp [End.one_def]
  | n + 1 => by
    rw [pow_succ, End.mul_def, ← Category.assoc, h, Linear.smul_comp, Category.assoc,
      comp_pow_signed' g a' a e h n, Linear.comp_smul, smul_smul, ← Category.assoc,
      pow_succ, pow_succ, End.mul_def, mul_comm]

private theorem compPow_smul {A : C} (x : End A) (e : k) :
    ∀ n : ℕ, compPow (e • x) n = e ^ n • (x ^ n : End A)
  | 0 => by simp [compPow, End.one_def]
  | n + 1 => by
    rw [compPow, compPow_smul x e n, Linear.smul_comp, Linear.comp_smul, smul_smul, pow_succ e,
      pow_succ x, End.mul_def, mul_comm]

end Algebra

section Scalars

private theorem zsign_add'' (p q : ZMod 2) : zsign k (p + q) = zsign k p * zsign k q := by
  unfold zsign
  fin_cases p <;> fin_cases q <;> simp

private theorem zsign_pow'' (p : ZMod 2) : ∀ n : ℕ, zsign k p ^ n = zsign k ((n : ZMod 2) * p)
  | 0 => by simp [zsign]
  | n + 1 => by rw [pow_succ, zsign_pow'' p n, ← zsign_add'']; push_cast; ring_nf

/-- The coefficient of the correction term: `(-1)^{pᵢ(pⱼ + a)} ε^{n-1} = qᵃ` for `a < n`
with `n pᵢ` even. -/
private theorem coeff_eq (pi pj : ZMod 2) (n a : ℕ) (ha : a < n) (hn : (n : ZMod 2) * pi = 0) :
    zsign k (pi * (pj + a)) * (zsign k (pi * pj) ^ a * zsign k (pi * pj) ^ (n - 1 - a)) =
      zsign k (pi * pi) ^ a := by
  rw [zsign_pow'', zsign_pow'', zsign_pow'', ← zsign_add'', ← zsign_add'']
  congr 1
  rw [Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  generalize (n : ZMod 2) = N at hn ⊢
  generalize (a : ZMod 2) = A
  fin_cases pi <;> fin_cases pj <;> fin_cases N <;> fin_cases A <;> simp_all

end Scalars

section Main

variable {C : Type*} [Category C] [Preadditive C] [Linear k C]

private theorem pow_comp_signed {A : C} (a g a' : End A) (e : k)
    (h : a ≫ g = e • (g ≫ a')) : ∀ n : ℕ, (a ^ n : End A) ≫ g = e ^ n • (g ≫ (a' ^ n : End A))
  | 0 => by simp [End.one_def]
  | n + 1 => by
    rw [pow_succ', End.mul_def, Category.assoc, h, Linear.comp_smul, ← Category.assoc,
      pow_comp_signed a g a' e h n, Linear.smul_comp, smul_smul, Category.assoc, pow_succ',
      pow_succ', End.mul_def]

private theorem pow_comm_signed {A : C} (y x : End A) (e : k) (h : y ≫ x = e • (x ≫ y))
    (a c : ℕ) :
    (y ^ c : End A) ≫ (x ^ a : End A) = (e ^ c) ^ a • ((x ^ a : End A) ≫ (y ^ c : End A)) :=
  comp_pow_signed' _ _ _ _ (pow_comp_signed y x y e h c) a

private theorem zmod_two_eq_zero_of_ne_one'' {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  fin_cases a
  · rfl
  · exact absurd rfl h

private theorem dn_mul_parity'' (i x : I) : (D.dn i x : ZMod 2) * D.parity i = 0 := by
  by_cases hi : D.parity i = 1
  · by_cases hix : i = x
    · subst hix
      simp [SKM.Datum.dn, D.d_self]
    · obtain ⟨m, hm⟩ := D.even_d_of_odd hi x
      have hc : (D.dn i x : ℤ) = m + m := by rw [D.dn_cast hix, hm]
      have : D.dn i x = m.toNat + m.toNat := by omega
      rw [this, hi]
      push_cast
      ring_nf
      rw [show (2 : ZMod 2) = 0 from rfl, mul_zero]
  · rw [zmod_two_eq_zero_of_ne_one'' hi, mul_zero]

variable (Sc) in
/-- **The commutator of a same-colour crossing with `Q_ij`.** If `ψ` slides past the dots
`x₁`, `x₂` of the two `i`-letters by `ψ x₁ - q x₂ ψ = 1` (`q = (-1)^{pᵢ}`), and supercommutes
with the dot `y` of the `j`-letter, which supercommutes with `x₂`, then `ψ Q_ij(x₁, y) -
Q_ij(x₂, y) ψ` is the correction term of (1.9) in the dots `εx₂`, `εy`, `εx₁`,
`ε = (-1)^{pᵢpⱼ}`. -/
theorem comp_qExpr_sub (i j : I) {A : C} (ψ x₁ x₂ y : End A)
    (h₁ : ψ ≫ x₁ - zsign k (D.parity i * D.parity i) • (x₂ ≫ ψ) = 𝟙 A)
    (h₂ : ψ ≫ y = zsign k (D.parity i * D.parity j) • (y ≫ ψ))
    (h₃ : y ≫ x₂ = zsign k (D.parity i * D.parity j) • (x₂ ≫ y)) :
    ψ ≫ qExpr Sc x₁ y i j - qExpr Sc x₂ y i j ≫ ψ =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (zsign k (D.parity i * D.parity j) • x₂) a ≫
            compPow (zsign k (D.parity i * D.parity j) • x₁) (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ c ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b c) •
          (compPow (zsign k (D.parity i * D.parity j) • x₂) a ≫
            compPow (zsign k (D.parity i * D.parity j) • y) c ≫
            compPow (zsign k (D.parity i * D.parity j) • x₁) (b - 1 - a)) := by
  have hq : ∀ n : ℕ, (n : ZMod 2) * D.parity i = 0 →
      zsign k (D.parity i * D.parity i) ^ n = 1 :=
    fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn
  have hεj : ∀ n : ℕ, (n : ZMod 2) * D.parity j = 0 →
      zsign k (D.parity i * D.parity j) ^ n = 1 :=
    fun n hn => by rw [mul_comm]; exact zsign_pow_of_mul_eq_zero _ _ n hn
  have hεi : ∀ n : ℕ, (n : ZMod 2) * D.parity i = 0 →
      zsign k (D.parity i * D.parity j) ^ n = 1 :=
    fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn
  -- the divided differences of the powers of the `i`-dots
  have E₁ : ∀ n : ℕ, (n : ZMod 2) * D.parity i = 0 →
      ψ ≫ (x₁ ^ n : End A) - (x₂ ^ n : End A) ≫ ψ =
        ∑ a ∈ Finset.range n, zsign k (D.parity i * D.parity i) ^ a •
          ((x₂ ^ a : End A) ≫ (x₁ ^ (n - 1 - a) : End A)) := by
    intro n hn
    have h := comp_pow_sub ψ x₁ x₂ _ h₁ n
    rwa [hq n hn, one_smul] at h
  unfold qExpr
  split_ifs with hd
  · have hdn : D.dn i j = 0 := by simp [SKM.Datum.dn, hd]
    simp only [hdn, Finset.range_zero, Finset.sum_empty, Finset.Ioo_self, add_zero]
    rw [End.one_def, Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp,
      sub_self]
  have hA : (Sc.t i j : k) • (ψ ≫ (x₁ ^ D.dn i j : End A) - (x₂ ^ D.dn i j : End A) ≫ ψ) =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (zsign k (D.parity i * D.parity j) • x₂) a ≫
            compPow (zsign k (D.parity i * D.parity j) • x₁) (D.dn i j - 1 - a)) := by
    rw [E₁ _ (dn_mul_parity'' i j), Finset.smul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_range] at ha
    rw [compPow_smul, compPow_smul, Linear.smul_comp, Linear.comp_smul, smul_smul, smul_smul,
      smul_smul, ← coeff_eq (D.parity i) (D.parity j) _ a ha (dn_mul_parity'' i j)]
    congr 1
    ring
  have hB : ψ ≫ (y ^ D.dn j i : End A) - (y ^ D.dn j i : End A) ≫ ψ = 0 := by
    rw [comp_pow_signed' ψ y y _ h₂, hεj _ (dn_mul_parity'' j i), one_smul, sub_self]
  have hC : ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ c ∈ Finset.Ioo 0 (D.dn j i),
      Sc.s i j b c • (ψ ≫ ((x₁ ^ b * y ^ c : End A)) - (x₂ ^ b * y ^ c : End A) ≫ ψ) =
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ c ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b c) •
          (compPow (zsign k (D.parity i * D.parity j) • x₂) a ≫
            compPow (zsign k (D.parity i * D.parity j) • y) c ≫
            compPow (zsign k (D.parity i * D.parity j) • x₁) (b - 1 - a)) := by
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    by_cases hs : Sc.s i j b c = 0
    · simp [hs]
    have hbp : (b : ZMod 2) * D.parity i = 0 :=
      zmod_two_eq_zero_of_ne_one'' fun h => hs (Sc.s_eq_zero i j b c h)
    have hcp : (c : ZMod 2) * D.parity j = 0 :=
      zmod_two_eq_zero_of_ne_one'' fun h => hs (by rw [Sc.s_symm]; exact Sc.s_eq_zero j i c b h)
    have hεc := hεj c hcp
    have h4 : ψ ≫ ((x₁ ^ b * y ^ c : End A)) - (x₂ ^ b * y ^ c : End A) ≫ ψ =
        (y ^ c : End A) ≫ (ψ ≫ (x₁ ^ b : End A) - (x₂ ^ b : End A) ≫ ψ) := by
      rw [End.mul_def, End.mul_def, ← Category.assoc, comp_pow_signed' ψ y y _ h₂, hεc,
        one_smul, Category.assoc, Category.assoc, Preadditive.comp_sub]
    rw [h4, E₁ b hbp, Preadditive.comp_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_range] at ha
    rw [Linear.comp_smul, ← Category.assoc, pow_comm_signed y x₂ _ h₃ a c, hεc, one_pow,
      one_smul, compPow_smul, compPow_smul, compPow_smul, hεc, one_smul, Linear.smul_comp,
      Linear.comp_smul, Linear.comp_smul, smul_smul, smul_smul, smul_smul, Category.assoc,
      ← coeff_eq (D.parity i) (D.parity j) b a ha hbp]
    congr 1
    ring
  have hS : ψ ≫ (∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • (x₁ ^ p * y ^ q : End A)) -
      (∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • (x₂ ^ p * y ^ q : End A)) ≫ ψ =
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ c ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j b c • (ψ ≫ ((x₁ ^ b * y ^ c : End A)) - (x₂ ^ b * y ^ c : End A) ≫ ψ) := by
    erw [Preadditive.comp_sum, Preadditive.sum_comp, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    erw [Preadditive.comp_sum, Preadditive.sum_comp, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    erw [Linear.comp_smul, Linear.smul_comp, ← smul_sub]
  have hB' : (Sc.t j i : k) • (ψ ≫ (y ^ D.dn j i : End A)) =
      (Sc.t j i : k) • ((y ^ D.dn j i : End A) ≫ ψ) := by
    rw [sub_eq_zero.mp hB]
  erw [Preadditive.comp_add, Preadditive.comp_add, Preadditive.add_comp, Preadditive.add_comp,
    Linear.comp_smul, Linear.comp_smul, Linear.smul_comp, Linear.smul_comp]
  rw [← hA, ← hC, ← hS, hB', smul_sub]
  abel

end Main

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
