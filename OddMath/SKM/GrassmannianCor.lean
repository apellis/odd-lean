/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.GrassmannianOdd

/-!
# Corollaries 5.2–5.4 of the infinite Grassmannian relations (Brundan–Ellis)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Corollary 5.2 (TeX
label `advances`, (5.11)–(5.14)), Corollary 5.3 ((5.15), (5.16)) and the curl relations (5.17) of
Corollary 5.4.

* `etaP_dots_sigma`, `sigma_dots_epsP`: the vanishing used for (5.13) (dots slid past `σ` by
  (3.3), then (2.13), resp. (2.14)).
* (5.11): `eq_5_11`, the `♦`-cup with label `n` (`0 ≤ n < ⟨hᵢ,λ⟩`) is
  `∑_{r ≥ 0} (-1)^{|i|(⟨hᵢ,λ⟩+n+r+1)}` (clockwise bubble with `-n-r-2` dots) then `η'` with `r`
  dots on its upward strand; (5.13) `eq_5_13`, (5.14) `eq_5_14`.
* (5.12): `eq_5_12`, the `♦`-cap with label `n` (`0 ≤ n < -⟨hᵢ,λ⟩`); the paper says the proof is
  "entirely similar" — it is carried out here (`eq_5_13'`, `eq_5_14'`).

Both use `bubble_key` (the consequence of (5.5)–(5.7) and (1.24)) for the off-diagonal entries.

* (5.15), (5.16): `eq_5_15`, `eq_5_16` ((5.11), (5.12) substituted into (2.12)).
* (5.17): `eq_5_17_a` (`σ ≫ ε'`), `eq_5_17_b` (`η' ≫ σ`), via `dcupRHS_epsL`, `etaL_dcapRHS`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

theorem sChain_dL (i : I) (r : ℕ) : SChain [up i, dn i] (dotsL [] i [dn i] r) [up i, dn i] :=
  sChain_dotsL [] i [dn i] r

theorem sChain_dR (i : I) (r : ℕ) : SChain [dn i, up i] (dotsL [dn i] i [] r) [dn i, up i] :=
  sChain_dotsL [dn i] i [] r

/-- The correction terms of (3.3): cap with `q` dots, then cup with `s` dots. -/
theorem cl_capcup (i : I) (μ : X) (q s : ℕ) :
    cl D Sc μ [up i, dn i] [dn i, up i]
        (dotsL [] i [dn i] q ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
          dotsL [dn i] i [] s) =
      cl D Sc μ [up i, dn i] [] (epsL i q) ≫ cl D Sc μ [] [dn i, up i] (etaL i s) := by
  rw [cl_comp (sChain_epsL i q) (sChain_etaL i s)]
  simp only [epsL, etaL, List.append_assoc, List.cons_append, List.nil_append]

theorem zsign_isUnit (p : ZMod 2) : IsUnit (zsign k p) := by
  unfold zsign; split_ifs <;> simp

/-- For `⟨hᵢ,λ⟩ > 0` and `r < ⟨hᵢ,λ⟩`: `η'` with `r` dots on its upward strand followed by `σ`
vanishes ((3.3) and (2.13)). -/
theorem etaP_dots_sigma (i : I) (μ : X) (hh : 0 < D.h i μ) (r : ℕ) (hr : (r : ℤ) < D.h i μ) :
    etaP cs i μ ≫ cl D Sc μ [up i, dn i] [dn i, up i] (dotsL [] i [dn i] r ++ sigmaL i i) = 0 := by
  have E := lemma31_eq3_eq Sc i μ r
  rw [sub_eq_iff_eq_add] at E
  have E' : zsign k (D.parity i * D.parity i * r) •
      cl D Sc μ [up i, dn i] [dn i, up i] (dotsL [] i [dn i] r ++ sigmaL i i) =
      cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] r) -
        ∑ q ∈ range r, zsign k (D.parity i * q) • cl D Sc μ [up i, dn i] [dn i, up i]
          (dotsL [] i [dn i] q ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
            dotsL [dn i] i [] (r - 1 - q)) := by
    rw [E]; abel
  have h0 : etaP cs i μ ≫ (zsign k (D.parity i * D.parity i * r) •
      cl D Sc μ [up i, dn i] [dn i, up i] (dotsL [] i [dn i] r ++ sigmaL i i)) = 0 := by
    rw [E', Preadditive.comp_sub, Preadditive.comp_sum,
      ← cl_comp (sChain_sigmaL i i) (sChain_dR i r), ← Category.assoc,
      eq_2_13_a cs i μ hh, Limits.zero_comp, zero_sub, neg_eq_zero]
    refine sum_eq_zero fun q hq => ?_
    rw [mem_range] at hq
    rw [Linear.comp_smul, cl_capcup, ← Category.assoc, eq_2_13_c cs i μ q (by omega),
      ite_eq_right (by omega), Limits.zero_comp, smul_zero]
  rw [Linear.comp_smul] at h0
  exact ((zsign_isUnit _).smul_eq_zero).mp h0

/-- For `⟨hᵢ,λ⟩ < 0` and `r < -⟨hᵢ,λ⟩`: `σ` followed by `ε'` with `r` dots on its upward strand
vanishes ((3.3) and (2.14)). -/
theorem sigma_dots_epsP (i : I) (μ : X) (hh : D.h i μ < 0) (r : ℕ) (hr : (r : ℤ) < -D.h i μ) :
    cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] r) ≫ epsP cs i μ = 0 := by
  have E := lemma31_eq3_eq Sc i μ r
  rw [sub_eq_iff_eq_add] at E
  rw [E, Preadditive.add_comp, Preadditive.sum_comp, Linear.smul_comp,
    ← cl_comp (sChain_dL i r) (sChain_sigmaL i i), Category.assoc,
    eq_2_14_a cs i μ hh, Limits.comp_zero, smul_zero, add_zero]
  refine sum_eq_zero fun q hq => ?_
  rw [mem_range] at hq
  rw [Linear.smul_comp, cl_capcup, Category.assoc, eq_2_14_c cs i μ _ (by omega),
    ite_eq_right (by omega), Limits.comp_zero, smul_zero]

/-! ## (5.11) -/

/-- The right-hand side of (5.11). -/
def dcupRHS (i : I) (μ : X) (n : ℕ) :
    (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [up i, dn i]) :=
  ∑ r ∈ range (D.h i μ - n).toNat, zsign k (D.parity i * ((D.h i μ + n + r + 1 : ℤ) : ZMod 2)) •
    (bubR cs i μ (-(n : ℤ) - r - 2) ≫ etaP cs i μ ≫
      cl D Sc μ [up i, dn i] [up i, dn i] (dotsL [] i [dn i] r))

/-- **(5.13)**. -/
theorem eq_5_13 (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < D.h i μ) :
    dcupRHS cs i μ n ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) = 0 := by
  rw [dcupRHS, Preadditive.sum_comp]
  refine sum_eq_zero fun r hr => ?_
  rw [mem_range] at hr
  rw [Linear.smul_comp, Category.assoc, Category.assoc,
    cl_comp (sChain_dL i r) (sChain_sigmaL i i),
    etaP_dots_sigma cs i μ (by omega) r (by omega), Limits.comp_zero, smul_zero]

/-- **(5.14)**. -/
theorem eq_5_14 (i : I) (μ : X) (m n : ℕ) (hm : (m : ℤ) < D.h i μ) (hn : (n : ℤ) < D.h i μ) :
    dcupRHS cs i μ n ≫ cl D Sc μ [up i, dn i] [] (epsL i m) = if m = n then 𝟙 _ else 0 := by
  have hterm : ∀ r : ℕ, (bubR cs i μ (-(n : ℤ) - r - 2) ≫ etaP cs i μ ≫
      cl D Sc μ [up i, dn i] [up i, dn i] (dotsL [] i [dn i] r)) ≫
        cl D Sc μ [up i, dn i] [] (epsL i m) =
      bubR cs i μ (-(n : ℤ) - r - 2) ≫ bubL cs i μ ((r + m : ℕ) : ℤ) := by
    intro r
    rw [bubL_nat, epsL_add, ← cl_comp (sChain_dL i r) (sChain_epsL i m)]
    simp only [Category.assoc]
  rw [dcupRHS, Preadditive.sum_comp]
  simp only [Linear.smul_comp, hterm]
  rcases lt_trichotomy m n with hlt | heq | hgt
  · rw [ite_eq_right (by omega)]
    refine sum_eq_zero fun r hr => ?_
    rw [mem_range] at hr
    rw [bubL_eq_zero_of_lt cs i μ (by push_cast; omega), Limits.comp_zero, smul_zero]
  · subst heq
    rw [ite_eq_left rfl, sum_eq_single ((D.h i μ).toNat - m - 1)]
    · rw [show -(m : ℤ) - (((D.h i μ).toNat - m - 1 : ℕ) : ℤ) - 2 = -D.h i μ - 1 by omega,
        show ((((D.h i μ).toNat - m - 1 + m : ℕ)) : ℤ) = D.h i μ - 1 by omega, bubR_eq_c,
        bubL_eq_c, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, smul_smul,
        mul_assoc, Units.inv_mul, mul_one]
      rw [show D.h i μ + m + (((D.h i μ).toNat - m - 1 : ℕ) : ℤ) + 1 = 2 * D.h i μ by omega]
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, mul_zero, zsign_zero, one_smul]
    · intro r hr hne
      rw [mem_range] at hr
      rw [bubL_eq_zero_of_lt cs i μ (by push_cast; omega), Limits.comp_zero, smul_zero]
    · intro h; exfalso; exact h (mem_range.2 (by omega))
  · rw [ite_eq_right (by omega)]
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = D.h i μ - 1 - m := ⟨(D.h i μ - 1 - m).toNat, by omega⟩
    rw [show (D.h i μ - n).toNat = a + (m - n + 1) by omega, sum_range_add]
    rw [sum_eq_zero (fun r hr => by
      rw [mem_range] at hr
      rw [bubL_eq_zero_of_lt cs i μ (by push_cast; omega), Limits.comp_zero, smul_zero]),
      zero_add]
    have K := bubble_key cs i μ (m - n) (by omega)
    have hx : ∀ x ∈ range (m - n + 1),
        zsign k (D.parity i * ((D.h i μ + n + ((a + x : ℕ) : ℤ) + 1 : ℤ) : ZMod 2)) •
          (bubR cs i μ (-(n : ℤ) - ((a + x : ℕ) : ℤ) - 2) ≫ bubL cs i μ ((a + x + m : ℕ) : ℤ)) =
        isg k (D.parity i) ((n : ℤ) + m) • (isg k (D.parity i) x •
          (bubRs cs i μ (((m - n : ℕ) : ℤ) - x) ≫ bubLs cs i μ x)) := by
      intro x hx
      rw [mem_range] at hx
      rw [smul_smul, ← isg_add, bubRs, bubLs]
      congr 1
      · exact isg_congr _ (by push_cast; omega)
      · congr 2 <;> push_cast [Nat.cast_sub (show n ≤ m by omega)] <;> omega
    rw [sum_congr rfl hx, ← smul_sum, K, smul_zero]

/-- **Brundan–Ellis, Corollary 5.2, (5.11)**: for `0 ≤ n < ⟨hᵢ,λ⟩`, the `♦`-cup with label `n` is
`∑_{r ≥ 0} (-1)^{|i|(⟨hᵢ,λ⟩+n+r+1)}` (the clockwise bubble with `-n-r-2` dots) followed by `η'`
with `r` dots on its upward strand (terms with `r ≥ ⟨hᵢ,λ⟩ - n` vanish by (5.4)). -/
theorem eq_5_11 (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < D.h i μ) :
    cl D Sc μ [] [up i, dn i] (dcupL i n) = dcupRHS cs i μ n := by
  have hh : 0 ≤ D.h i μ := by omega
  have E := cl_invP₁ Sc i μ hh
  calc cl D Sc μ [] [up i, dn i] (dcupL i n)
      = ∑ m ∈ range (D.h i μ).toNat, (if m = n then 𝟙 _ else 0) ≫
          cl D Sc μ [] [up i, dn i] (dcupL i m) := by
        rw [sum_eq_single n]
        · rw [ite_eq_left rfl, Category.id_comp]
        · intro m _ hm; rw [ite_eq_right hm, Limits.zero_comp]
        · intro h; exfalso; exact h (mem_range.2 (by omega))
    _ = dcupRHS cs i μ n ≫ cl D Sc μ [up i, dn i] [up i, dn i] [] := by
        rw [← E, Preadditive.comp_add, Preadditive.comp_neg, Preadditive.comp_sum,
          ← cl_comp (sChain_sigmaL i i) (sChain_lcrossL i i), ← Category.assoc, eq_5_13 cs i μ n hn,
          Limits.zero_comp, neg_zero, zero_add]
        refine sum_congr rfl fun m hm => ?_
        rw [mem_range] at hm
        rw [← cl_comp (sChain_epsL i m) (sChain_dcupL i m), ← Category.assoc,
          eq_5_14 cs i μ m n (by omega) hn]
    _ = dcupRHS cs i μ n := by rw [cl_nil, Category.comp_id]


/-! ## (5.12) -/

/-- The right-hand side of (5.12). -/
def dcapRHS (i : I) (μ : X) (n : ℕ) :
    (pres D Sc).obj (ob D μ [dn i, up i]) ⟶ (pres D Sc).obj (ob D μ []) :=
  ∑ r ∈ range (-D.h i μ - n).toNat, zsign k (D.parity i * ((D.h i μ + n + r + 1 : ℤ) : ZMod 2)) •
    (cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] r) ≫ epsP cs i μ ≫
      bubL cs i μ (-(n : ℤ) - r - 2))

/-- The analogue of (5.13) for (5.12). -/
theorem eq_5_13' (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < -D.h i μ) :
    cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫ dcapRHS cs i μ n = 0 := by
  rw [dcapRHS, Preadditive.comp_sum]
  refine sum_eq_zero fun r hr => ?_
  rw [mem_range] at hr
  rw [Linear.comp_smul, ← Category.assoc, cl_comp (sChain_sigmaL i i) (sChain_dR i r),
    ← Category.assoc, sigma_dots_epsP cs i μ (by omega) r (by omega), Limits.zero_comp,
    smul_zero]

/-- The analogue of (5.14) for (5.12). -/
theorem eq_5_14' (i : I) (μ : X) (m n : ℕ) (hm : (m : ℤ) < -D.h i μ) (hn : (n : ℤ) < -D.h i μ) :
    cl D Sc μ [] [dn i, up i] (etaL i m) ≫ dcapRHS cs i μ n = if m = n then 𝟙 _ else 0 := by
  have hterm : ∀ r : ℕ, cl D Sc μ [] [dn i, up i] (etaL i m) ≫
      (cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] r) ≫ epsP cs i μ ≫
        bubL cs i μ (-(n : ℤ) - r - 2)) =
      bubR cs i μ ((m + r : ℕ) : ℤ) ≫ bubL cs i μ (-(n : ℤ) - r - 2) := by
    intro r
    rw [bubR_nat, etaL_add, ← cl_comp (sChain_etaL i m) (sChain_dR i r)]
    simp only [Category.assoc]
  rw [dcapRHS, Preadditive.comp_sum]
  simp only [Linear.comp_smul, hterm]
  rcases lt_trichotomy m n with hlt | heq | hgt
  · rw [ite_eq_right (by omega)]
    refine sum_eq_zero fun r hr => ?_
    rw [mem_range] at hr
    rw [bubR_eq_zero_of_lt cs i μ (by push_cast; omega), Limits.zero_comp, smul_zero]
  · subst heq
    rw [ite_eq_left rfl, sum_eq_single ((-D.h i μ).toNat - m - 1)]
    · rw [show -(m : ℤ) - (((-D.h i μ).toNat - m - 1 : ℕ) : ℤ) - 2 = D.h i μ - 1 by omega,
        show (((m + ((-D.h i μ).toNat - m - 1) : ℕ)) : ℤ) = -D.h i μ - 1 by omega, bubR_eq_c,
        bubL_eq_c, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, smul_smul,
        mul_assoc, Units.inv_mul, mul_one]
      rw [show D.h i μ + m + (((-D.h i μ).toNat - m - 1 : ℕ) : ℤ) + 1 = 0 by omega]
      simp [zsign_zero]
    · intro r hr hne
      rw [mem_range] at hr
      rw [bubR_eq_zero_of_lt cs i μ (by push_cast; omega), Limits.zero_comp, smul_zero]
    · intro h; exfalso; exact h (mem_range.2 (by omega))
  · rw [ite_eq_right (by omega)]
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = -D.h i μ - 1 - m := ⟨(-D.h i μ - 1 - m).toNat, by omega⟩
    rw [show (-D.h i μ - n).toNat = a + (m - n + 1) by omega, sum_range_add]
    rw [sum_eq_zero (fun r hr => by
      rw [mem_range] at hr
      rw [bubR_eq_zero_of_lt cs i μ (by push_cast; omega), Limits.zero_comp, smul_zero]),
      zero_add]
    have K := bubble_key cs i μ (m - n) (by omega)
    rw [← sum_range_reflect] at K
    have hx : ∀ x ∈ range (m - n + 1),
        zsign k (D.parity i * ((D.h i μ + n + ((a + x : ℕ) : ℤ) + 1 : ℤ) : ZMod 2)) •
          (bubR cs i μ ((m + (a + x) : ℕ) : ℤ) ≫ bubL cs i μ (-(n : ℤ) - ((a + x : ℕ) : ℤ) - 2)) =
        isg k (D.parity i) (((m - n + 1 - 1 - x : ℕ) : ℤ)) •
          (bubRs cs i μ (((m - n : ℕ) : ℤ) - ((m - n + 1 - 1 - x : ℕ) : ℤ)) ≫
            bubLs cs i μ (((m - n + 1 - 1 - x : ℕ) : ℤ))) := by
      intro x hx
      rw [mem_range] at hx
      rw [bubRs, bubLs]
      have e : ((m - n + 1 - 1 - x : ℕ) : ℤ) = (m : ℤ) - n - x := by omega
      rw [e]
      congr 1
      · exact isg_congr _ (by push_cast; omega)
      · congr 2 <;> push_cast [Nat.cast_sub (show n ≤ m by omega)] <;> omega
    rw [sum_congr rfl hx, K]

/-- **Brundan–Ellis, Corollary 5.2, (5.12)**: for `0 ≤ n < -⟨hᵢ,λ⟩`, the `♦`-cap with label `n` is
`∑_{r ≥ 0} (-1)^{|i|(⟨hᵢ,λ⟩+n+r+1)}` (`ε'` with `r` dots on its upward strand) followed by the
counterclockwise bubble with `-n-r-2` dots (terms with `r ≥ -⟨hᵢ,λ⟩ - n` vanish by (5.3)). -/
theorem eq_5_12 (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < -D.h i μ) :
    cl D Sc μ [dn i, up i] [] (dcapL i n) = dcapRHS cs i μ n := by
  have hh : D.h i μ ≤ 0 := by omega
  have E := cl_invM₁ Sc i μ hh
  calc cl D Sc μ [dn i, up i] [] (dcapL i n)
      = ∑ m ∈ range (-D.h i μ).toNat, cl D Sc μ [dn i, up i] [] (dcapL i m) ≫
          (if m = n then 𝟙 _ else 0) := by
        rw [sum_eq_single n]
        · rw [ite_eq_left rfl, Category.comp_id]
        · intro m _ hm; rw [ite_eq_right hm, Limits.comp_zero]
        · intro h; exfalso; exact h (mem_range.2 (by omega))
    _ = cl D Sc μ [dn i, up i] [dn i, up i] [] ≫ dcapRHS cs i μ n := by
        rw [← E, Preadditive.add_comp, Preadditive.neg_comp, Preadditive.sum_comp,
          ← cl_comp (sChain_lcrossL i i) (sChain_sigmaL i i), Category.assoc,
          eq_5_13' cs i μ n hn, Limits.comp_zero, neg_zero, zero_add]
        refine sum_congr rfl fun m hm => ?_
        rw [mem_range] at hm
        rw [← cl_comp (sChain_dcapL i m) (sChain_etaL i m), Category.assoc,
          eq_5_14' cs i μ m n (by omega) hn]
    _ = dcapRHS cs i μ n := by rw [cl_nil, Category.id_comp]


/-! ## Corollary 5.3 -/

/-- **Brundan–Ellis, Corollary 5.3, (5.15)**: `σ ≫` (leftward crossing) on `Eᵢ Fᵢ 1_λ` is
`∑_{n<⟨hᵢ,λ⟩} (ε with n dots) ≫ (right-hand side of (5.11)) - 1`. -/
theorem eq_5_15 (i : I) (μ : X) :
    cl D Sc μ [up i, dn i] [up i, dn i] (sigmaL i i ++ lcrossL i i) =
      ∑ n ∈ range (D.h i μ).toNat, cl D Sc μ [up i, dn i] [] (epsL i n) ≫ dcupRHS cs i μ n -
        cl D Sc μ [up i, dn i] [up i, dn i] [] := by
  rw [eq_2_12_a Sc i μ]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  rw [← cl_comp (sChain_epsL i n) (sChain_dcupL i n), eq_5_11 cs i μ n (by omega)]

/-- **Brundan–Ellis, Corollary 5.3, (5.16)**: (leftward crossing) `≫ σ` on `Fᵢ Eᵢ 1_λ` is
`∑_{n<-⟨hᵢ,λ⟩} (right-hand side of (5.12)) ≫ (η with n dots) - 1`. -/
theorem eq_5_16 (i : I) (μ : X) :
    cl D Sc μ [dn i, up i] [dn i, up i] (lcrossL i i ++ sigmaL i i) =
      ∑ n ∈ range (-D.h i μ).toNat, dcapRHS cs i μ n ≫ cl D Sc μ [] [dn i, up i] (etaL i n) -
        cl D Sc μ [dn i, up i] [dn i, up i] [] := by
  rw [eq_2_12_b Sc i μ]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  rw [← cl_comp (sChain_dcapL i n) (sChain_etaL i n), eq_5_12 cs i μ n (by omega)]

/-! ## Corollary 5.4, (5.17) -/

/-- `(right-hand side of (5.11)) ≫ (ε with ⟨hᵢ,λ⟩ dots)` for `n < ⟨hᵢ,λ⟩`, computed with
`bubble_key`: it is `-(-1)^{|i|(⟨hᵢ,λ⟩+n)} c_{λ;i}` times the clockwise bubble with `-n-1` dots. -/
theorem dcupRHS_epsL (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < D.h i μ) :
    dcupRHS cs i μ n ≫ cl D Sc μ [up i, dn i] [] (epsL i (D.h i μ).toNat) =
      (-(isg k (D.parity i) (D.h i μ + n)) * (cs.c μ i : k)) • bubR cs i μ (-(n : ℤ) - 1) := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = D.h i μ - n := ⟨(D.h i μ - n).toNat, by omega⟩
  have hterm : ∀ r ∈ range t, zsign k (D.parity i * ((D.h i μ + n + r + 1 : ℤ) : ZMod 2)) •
      ((bubR cs i μ (-(n : ℤ) - r - 2) ≫ etaP cs i μ ≫
        cl D Sc μ [up i, dn i] [up i, dn i] (dotsL [] i [dn i] r)) ≫
          cl D Sc μ [up i, dn i] [] (epsL i (D.h i μ).toNat)) =
      isg k (D.parity i) (D.h i μ + n) • (isg k (D.parity i) ((r + 1 : ℕ) : ℤ) •
        (bubRs cs i μ ((t : ℤ) - ((r + 1 : ℕ) : ℤ)) ≫ bubLs cs i μ ((r + 1 : ℕ) : ℤ))) := by
    intro r _
    rw [Category.assoc, Category.assoc,
      cl_comp (sChain_dL i r) (sChain_epsL i _), ← epsL_add, ← bubL_nat, smul_smul, ← isg_add,
      bubRs, bubLs]
    congr 1
    · exact isg_congr _ (by push_cast; omega)
    · congr 2 <;> push_cast <;> omega
  rw [dcupRHS, Preadditive.sum_comp, show (D.h i μ - n).toNat = t by omega]
  simp only [Linear.smul_comp]
  rw [sum_congr rfl hterm, ← smul_sum]
  have K := bubble_key cs i μ t (by omega)
  rw [sum_range_succ', Nat.cast_zero, sub_zero, bubLs_zero, Linear.comp_smul, Category.comp_id,
    isg_zero, one_smul] at K
  rw [eq_neg_of_add_eq_zero_left K, bubRs, show (t : ℤ) - D.h i μ - 1 = -(n : ℤ) - 1 by omega,
    smul_neg, smul_smul, neg_mul, neg_smul]

/-- **Brundan–Ellis, Corollary 5.4, (5.17)**, first relation: `σ ≫ ε'` on `Eᵢ Fᵢ 1_λ` is
`∑_{n=0}^{⟨hᵢ,λ⟩} (-1)^{|i|n}` (ε with `n` dots) followed by the clockwise bubble with `-n-1`
dots (`0` if `⟨hᵢ,λ⟩ < 0`). -/
theorem eq_5_17_a (i : I) (μ : X) :
    cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫ epsP cs i μ =
      ∑ n ∈ range ((D.h i μ).toNat + 1), zsign k (D.parity i * (n : ZMod 2)) •
        (cl D Sc μ [up i, dn i] [] (epsL i n) ≫ bubR cs i μ (-(n : ℤ) - 1)) := by
  rcases lt_or_ge (D.h i μ) 0 with hh | hh
  · rw [eq_2_14_a cs i μ hh, show (D.h i μ).toNat = 0 by omega, zero_add, sum_range_one,
      Nat.cast_zero, Int.natCast_zero, neg_zero, zero_sub, bubR_eq_zero_of_lt cs i μ (by omega),
      Limits.comp_zero, smul_zero]
  · set N := (D.h i μ).toNat with hN
    have hNh : (N : ℤ) = D.h i μ := Int.toNat_of_nonneg hh
    rw [epsP_eq_of_nonneg cs hh, Linear.comp_smul, ← hN,
      cl_comp (sChain_sigmaL i i) ((sChain_lcrossL i i).append (sChain_epsL i N)),
      ← List.append_assoc, ← cl_comp ((sChain_sigmaL i i).append (sChain_lcrossL i i))
        (sChain_epsL i N), eq_5_15, Preadditive.sub_comp, cl_nil, Category.id_comp,
      Preadditive.sum_comp, sum_range_succ, show -((N : ℕ) : ℤ) - 1 = -D.h i μ - 1 by omega,
      bubR_eq_c, Linear.comp_smul, Category.comp_id]
    have hs : ∀ n ∈ range N, (cl D Sc μ [up i, dn i] [] (epsL i n) ≫ dcupRHS cs i μ n) ≫
        cl D Sc μ [up i, dn i] [] (epsL i N) = (-(isg k (D.parity i) (D.h i μ + n)) *
          (cs.c μ i : k)) • (cl D Sc μ [up i, dn i] [] (epsL i n) ≫ bubR cs i μ (-(n : ℤ) - 1)) := by
      intro n hn
      rw [mem_range] at hn
      rw [Category.assoc, dcupRHS_epsL cs i μ n (by omega), Linear.comp_smul]
    rw [sum_congr rfl hs, smul_sub, smul_sum, sub_eq_add_neg]
    congr 1
    · refine sum_congr rfl fun n hn => ?_
      rw [smul_smul]
      congr 1
      rw [isg_add, isg_natCast]
      have h1 : zsign k (D.parity i * ((D.h i μ : ℤ) : ZMod 2)) = isg k (D.parity i) (D.h i μ) := rfl
      have h2 := isg_mul_self (k := k) (D.parity i) (D.h i μ)
      rw [h1]
      have hc : (↑(cs.c μ i)⁻¹ : k) * (cs.c μ i : k) = 1 := Units.inv_mul _
      linear_combination (isg k (D.parity i) n) * ((isg k (D.parity i) (D.h i μ))^2 * hc + h2)
    · rw [← neg_smul, smul_smul, isg_natCast, hNh]
      congr 1
      simp [isg]


/-- `(η with -⟨hᵢ,λ⟩ dots) ≫ (right-hand side of (5.12))` for `n < -⟨hᵢ,λ⟩`, computed with
`bubble_key`: `-(-1)^{|i|(⟨hᵢ,λ⟩+n)} c_{λ;i}⁻¹` times the counterclockwise bubble with `-n-1`
dots. -/
theorem etaL_dcapRHS (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < -D.h i μ) :
    cl D Sc μ [] [dn i, up i] (etaL i (-D.h i μ).toNat) ≫ dcapRHS cs i μ n =
      (-(isg k (D.parity i) (D.h i μ + n)) * (↑(cs.c μ i)⁻¹ : k)) •
        bubL cs i μ (-(n : ℤ) - 1) := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = -D.h i μ - n := ⟨(-D.h i μ - n).toNat, by omega⟩
  have hterm : ∀ r ∈ range t, zsign k (D.parity i * ((D.h i μ + n + r + 1 : ℤ) : ZMod 2)) •
      (cl D Sc μ [] [dn i, up i] (etaL i (-D.h i μ).toNat) ≫
        (cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] r) ≫ epsP cs i μ ≫
          bubL cs i μ (-(n : ℤ) - r - 2))) =
      isg k (D.parity i) ((t : ℤ) - ((r + 1 : ℕ) : ℤ)) •
        (bubRs cs i μ ((r + 1 : ℕ) : ℤ) ≫ bubLs cs i μ ((t : ℤ) - ((r + 1 : ℕ) : ℤ))) := by
    intro r _
    rw [← Category.assoc, ← Category.assoc, cl_comp (sChain_etaL i _) (sChain_dR i r),
      ← etaL_add, ← bubR_nat, bubRs, bubLs]
    congr 1
    · exact isg_congr _ (by push_cast; omega)
    · congr 2 <;> push_cast <;> omega
  rw [dcapRHS, Preadditive.comp_sum, show (-D.h i μ - n).toNat = t by omega]
  simp only [Linear.comp_smul]
  rw [sum_congr rfl hterm]
  have K := bubble_key cs i μ t (by omega)
  rw [sum_range_succ, sub_self, bubRs_zero, Linear.smul_comp, Category.id_comp] at K
  have hre : ∑ r ∈ range t, isg k (D.parity i) ((t : ℤ) - ((r + 1 : ℕ) : ℤ)) •
      (bubRs cs i μ ((r + 1 : ℕ) : ℤ) ≫ bubLs cs i μ ((t : ℤ) - ((r + 1 : ℕ) : ℤ))) =
      ∑ j ∈ range t, isg k (D.parity i) (j : ℤ) •
        (bubRs cs i μ ((t : ℤ) - j) ≫ bubLs cs i μ (j : ℤ)) := by
    conv_rhs => rw [← sum_range_reflect]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    have e : (((t - 1 - j : ℕ)) : ℤ) = (t : ℤ) - ((j + 1 : ℕ) : ℤ) := by omega
    rw [e, show (t : ℤ) - ((t : ℤ) - ((j + 1 : ℕ) : ℤ)) = ((j + 1 : ℕ) : ℤ) by ring]
  rw [hre]
  rw [eq_neg_of_add_eq_zero_left K, bubLs, show (t : ℤ) + D.h i μ - 1 = -(n : ℤ) - 1 by omega,
    smul_smul, ← neg_smul]
  congr 1
  rw [isg_congr _ (n := D.h i μ + n) (by omega)]; ring


/-- **Brundan–Ellis, Corollary 5.4, (5.17)**, second relation: `η' ≫ σ` on `1_λ → Fᵢ Eᵢ 1_λ` is
`-∑_{n=0}^{-⟨hᵢ,λ⟩} (-1)^{|i|(n+1)}` (the counterclockwise bubble with `-n-1` dots) followed by
(η with `n` dots) (`0` if `⟨hᵢ,λ⟩ > 0`). -/
theorem eq_5_17_b (i : I) (μ : X) :
    etaP cs i μ ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) =
      -∑ n ∈ range ((-D.h i μ).toNat + 1), zsign k (D.parity i * ((n + 1 : ℕ) : ZMod 2)) •
        (bubL cs i μ (-(n : ℤ) - 1) ≫ cl D Sc μ [] [dn i, up i] (etaL i n)) := by
  rcases lt_or_ge 0 (D.h i μ) with hh | hh
  · rw [eq_2_13_a cs i μ hh, show (-D.h i μ).toNat = 0 by omega, zero_add, sum_range_one,
      Nat.cast_zero, neg_zero, zero_sub, bubL_eq_zero_of_lt cs i μ (by omega), Limits.zero_comp,
      smul_zero, neg_zero]
  · set M := (-D.h i μ).toNat with hM
    have hMh : (M : ℤ) = -D.h i μ := Int.toNat_of_nonneg (by omega)
    have hlσ := (sChain_lcrossL i i).append (sChain_sigmaL i i)
    have e : cl D Sc μ [] [up i, dn i] (etaL i M ++ lcrossL i i) ≫
        cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) =
        cl D Sc μ [] [dn i, up i] (etaL i M) ≫
          cl D Sc μ [dn i, up i] [dn i, up i] (lcrossL i i ++ sigmaL i i) := by
      rw [cl_comp ((sChain_etaL i M).append (sChain_lcrossL i i)) (sChain_sigmaL i i),
        cl_comp (sChain_etaL i M) hlσ, List.append_assoc]
    rw [etaP_eq_of_nonpos cs hh, ← hM, Linear.smul_comp, e, eq_5_16, Preadditive.comp_sub,
      cl_nil, Category.comp_id, Preadditive.comp_sum]
    have hs : ∀ n ∈ range M, cl D Sc μ [] [dn i, up i] (etaL i M) ≫
        (dcapRHS cs i μ n ≫ cl D Sc μ [] [dn i, up i] (etaL i n)) =
        (-(isg k (D.parity i) (D.h i μ + n)) * (↑(cs.c μ i)⁻¹ : k)) •
          (bubL cs i μ (-(n : ℤ) - 1) ≫ cl D Sc μ [] [dn i, up i] (etaL i n)) := by
      intro n hn
      rw [mem_range] at hn
      rw [← Category.assoc, hM, etaL_dcapRHS cs i μ n (by omega), Linear.smul_comp]
    rw [sum_congr rfl hs, sum_range_succ, show -((M : ℕ) : ℤ) - 1 = D.h i μ - 1 by omega,
      bubL_eq_c, Linear.smul_comp, Category.id_comp, smul_sub, smul_sum, neg_add, sub_eq_add_neg]
    have hz : zsign k (ipar D i μ) = isg k (D.parity i) (D.h i μ + 1) := by simp [ipar, isg]
    have h2 : isg k (D.parity i) (((M + 1 : ℕ) : ℤ)) = isg k (D.parity i) (D.h i μ + 1) :=
      isg_congr _ (by push_cast; omega)
    have hc : (cs.c μ i : k) * (↑(cs.c μ i)⁻¹ : k) = 1 := Units.mul_inv _
    congr 1
    · rw [← sum_neg_distrib]
      refine sum_congr rfl fun n hn => ?_
      rw [smul_smul, ← neg_smul, hz, isg_natCast]
      congr 1
      have h1 : isg k (D.parity i) (((n + 1 : ℕ) : ℤ)) =
          isg k (D.parity i) (D.h i μ + 1) * isg k (D.parity i) (D.h i μ + n) := by
        rw [← isg_add]; exact isg_congr _ (by push_cast; omega)
      rw [h1]
      linear_combination (-(isg k (D.parity i) (D.h i μ + 1) *
        isg k (D.parity i) (D.h i μ + ↑n))) * hc
    · rw [smul_smul, ← neg_smul, hz, isg_natCast, h2, neg_smul]

end OddMath.SKM
