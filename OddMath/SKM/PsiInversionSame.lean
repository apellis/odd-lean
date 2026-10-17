/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Curls
import OddMath.SKM.ChevalleyRel

/-!
# Same-colour change of inversion entries for ψ

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 9.4, proof, (1.13)–(1.14) and Corollary 5.2, (5.11)–(5.14).

`psiSameCup_inversion` and `psiSameCap_inversion` prove all five blocks of
the two raw same-colour matrices. Their inverse entries are bubble-weighted sums
of right caps or cups. The change-of-entries formulas include their zero tails;
`psiSameCupDual_zero` and `psiSameCapDual_zero` verify the totalized entries.
The scalar blocks follow by anti-triangular independence with unit anti-diagonal,
without a field or a relation-preservation hypothesis.

These are morphisms of the existing presentation `pres D Sc`. Their downstream
use is the same-colour relation check for the printed ψ. Identification with the
assigned dotted cup/cap composites and transport of the matrix equations to the
shifted super-opposite, including scalar and parity factors, remain separate;
this module does not construct the 2-superfunctor of Proposition 9.4.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w

private theorem antitriangular_independent {k : Type*} [CommRing k]
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {A B T : C} (N : ℕ) (c : kˣ)
    (L : ℕ → (A ⟶ B)) (R : ℕ → (B ⟶ A))
    (hz : ∀ r m, r + m < N - 1 → L r ≫ R m = 0)
    (hd : ∀ r, r < N → L r ≫ R (N - 1 - r) = (c : k) • 𝟙 A)
    (f : ℕ → (T ⟶ A)) (hf : ∑ r ∈ range N, f r ≫ L r = 0) :
    ∀ r, r < N → f r = 0 := by
  classical
  intro r hr
  by_contra hfr
  let S := (range N).filter (fun s => f s ≠ 0)
  have hS : S.Nonempty := ⟨r, mem_filter.mpr ⟨mem_range.mpr hr, hfr⟩⟩
  let m := S.max' hS
  have hm : m < N ∧ f m ≠ 0 := by
    simpa only [S, mem_filter, mem_range] using S.max'_mem hS
  have H := congrArg (fun g => g ≫ R (N - 1 - m)) hf
  rw [Preadditive.sum_comp, Limits.zero_comp, sum_eq_single m] at H
  · rw [Category.assoc, hd m hm.1, Linear.comp_smul, Category.comp_id] at H
    exact hm.2 (c.isUnit.smul_eq_zero.mp H)
  · intro s hs hsm
    rw [mem_range] at hs
    by_cases hlt : s < m
    · rw [Category.assoc, hz s (N - 1 - m) (by omega), Limits.comp_zero]
    · have hfs : f s = 0 := by
        by_contra hfs
        have hsS : s ∈ S := mem_filter.mpr ⟨mem_range.mpr hs, hfs⟩
        have := S.le_max' s hsS
        change s ≤ m at this
        omega
      rw [hfs, Limits.zero_comp, Limits.zero_comp]
  · intro h
    exact False.elim (h (mem_range.mpr hm.1))

private theorem antitriangular_independent_right {k : Type*} [CommRing k]
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {A B T : C} (N : ℕ) (c : kˣ)
    (L : ℕ → (A ⟶ B)) (R : ℕ → (B ⟶ A))
    (hz : ∀ r m, m + r < N - 1 → L m ≫ R r = 0)
    (hd : ∀ r, r < N → L (N - 1 - r) ≫ R r = (c : k) • 𝟙 A)
    (f : ℕ → (A ⟶ T)) (hf : ∑ r ∈ range N, R r ≫ f r = 0) :
    ∀ r, r < N → f r = 0 := by
  classical
  intro r hr
  by_contra hfr
  let S := (range N).filter (fun s => f s ≠ 0)
  have hS : S.Nonempty := ⟨r, mem_filter.mpr ⟨mem_range.mpr hr, hfr⟩⟩
  let m := S.max' hS
  have hm : m < N ∧ f m ≠ 0 := by
    simpa only [S, mem_filter, mem_range] using S.max'_mem hS
  have H := congrArg (fun g => L (N - 1 - m) ≫ g) hf
  rw [Preadditive.comp_sum, Limits.comp_zero, sum_eq_single m] at H
  · rw [← Category.assoc, hd m hm.1, Linear.smul_comp, Category.id_comp] at H
    exact hm.2 (c.isUnit.smul_eq_zero.mp H)
  · intro s hs hsm
    rw [mem_range] at hs
    by_cases hlt : s < m
    · rw [← Category.assoc, hz s (N - 1 - m) (by omega), Limits.zero_comp]
    · have hfs : f s = 0 := by
        by_contra hfs
        have hsS : s ∈ S := mem_filter.mpr ⟨mem_range.mpr hs, hfs⟩
        have := S.le_max' s hsS
        change s ≤ m at this
        omega
      rw [hfs, Limits.comp_zero, Limits.comp_zero]
  · intro h
    exact False.elim (h (mem_range.mpr hm.1))

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- The dotted left cup in the raw positive-weight inversion matrix. -/
def psiSameCup (cs : CScalars Sc) (i : I) (μ : X) (r : ℕ) :
    (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [up i, dn i]) :=
  etaP cs i μ ≫ cl D Sc μ [up i, dn i] [up i, dn i] (dotsL [] i [dn i] r)

/-- The bubble coefficient of the change from dotted left cups to diamonds. -/
def psiSameCupCoeff (cs : CScalars Sc) (i : I) (μ : X) (n r : ℕ) :
    (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ []) :=
  zsign k (D.parity i * ((D.h i μ + n + r + 1 : ℤ) : ZMod 2)) •
    bubR cs i μ (-(n : ℤ) - r - 2)

/-- The cap entry dual to the dotted left cup, before the ψ scalar factors. -/
def psiSameCupDual (cs : CScalars Sc) (i : I) (μ : X) (r : ℕ) :
    (pres D Sc).obj (ob D μ [up i, dn i]) ⟶ (pres D Sc).obj (ob D μ []) :=
  ∑ n ∈ range (D.h i μ).toNat,
    cl D Sc μ [up i, dn i] [] (epsL i n) ≫ psiSameCupCoeff cs i μ n r

variable (cs : CScalars Sc)

/-- The change-of-entries matrix is anti-triangular. -/
theorem psiSameCupCoeff_zero (i : I) (μ : X) (n r : ℕ)
    (h : D.h i μ ≤ (n : ℤ) + r) : psiSameCupCoeff cs i μ n r = 0 := by
  rw [psiSameCupCoeff, bubR_eq_zero_of_lt cs i μ (by omega), smul_zero]

/-- Totalized diamond-cup images vanish outside the range of (1.13). -/
theorem psiSameCupDual_zero (i : I) (μ : X) (r : ℕ) (h : D.h i μ ≤ r) :
    psiSameCupDual cs i μ r = 0 := by
  apply sum_eq_zero
  intro n _
  rw [psiSameCupCoeff_zero cs i μ n r (by omega), Limits.comp_zero]

/-- The full rectangular sum for (5.11), with its zero tail included. -/
theorem psiSameCup_change (i : I) (μ : X) (n : ℕ) :
    cl D Sc μ [] [up i, dn i] (dcupL i n) =
      ∑ r ∈ range (D.h i μ).toNat, psiSameCupCoeff cs i μ n r ≫ psiSameCup cs i μ r := by
  by_cases hn : (n : ℤ) < D.h i μ
  · rw [eq_5_11 cs i μ n hn, dcupRHS]
    trans ∑ r ∈ range (D.h i μ - n).toNat,
      psiSameCupCoeff cs i μ n r ≫ psiSameCup cs i μ r
    · apply sum_congr rfl
      intro r _
      simp only [psiSameCupCoeff, psiSameCup, Linear.smul_comp]
    · apply sum_subset (range_mono (by omega))
      intro r _ hr
      rw [mem_range, not_lt] at hr
      rw [psiSameCupCoeff_zero cs i μ n r (by omega), Limits.zero_comp]
  · rw [cl_dcupZero Sc i μ n (by omega)]
    symm
    apply sum_eq_zero
    intro r _
    rw [psiSameCupCoeff_zero cs i μ n r (by omega), Limits.zero_comp]

/-- The dotted cup is killed by the rightward mixed crossing in the allowed range. -/
theorem psiSameCup_sigma (i : I) (μ : X) (r : ℕ) (hr : (r : ℤ) < D.h i μ) :
    psiSameCup cs i μ r ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) = 0 := by
  rw [psiSameCup, Category.assoc, cl_comp (sChain_dL i r) (sChain_sigmaL i i)]
  exact etaP_dots_sigma cs i μ (by omega) r hr

/-- The leftward mixed crossing is killed by every dual cap entry. -/
theorem psiSameCup_lcross_dual (i : I) (μ : X) (r : ℕ) :
    cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) ≫ psiSameCupDual cs i μ r = 0 := by
  rw [psiSameCupDual, Preadditive.comp_sum]
  apply sum_eq_zero
  intro n hn
  rw [mem_range] at hn
  rw [← Category.assoc, cl_comp (sChain_lcrossL i i) (sChain_epsL i n),
    cl_invP₃ Sc i μ n (by omega), Limits.zero_comp]

/-- The nontrivial diagonal block of the raw positive-weight inverse matrix. -/
theorem psiSameCup_complete (i : I) (μ : X) (hh : 0 ≤ D.h i μ) :
    -(cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫
      cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i)) +
      ∑ r ∈ range (D.h i μ).toNat, psiSameCupDual cs i μ r ≫ psiSameCup cs i μ r = 𝟙 _ := by
  have E := cl_invP₁ Sc i μ hh
  rw [← cl_comp (sChain_sigmaL i i) (sChain_lcrossL i i), cl_nil] at E
  rw [← E]
  congr 1
  simp only [psiSameCupDual, Preadditive.sum_comp, Category.assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  rw [← Preadditive.comp_sum, ← psiSameCup_change cs i μ n,
    cl_comp (sChain_epsL i n) (sChain_dcupL i n)]

/-- Pairing a dotted left cup with a right cap is the corresponding bubble. -/
theorem psiSameCup_eps (i : I) (μ : X) (r m : ℕ) :
    psiSameCup cs i μ r ≫ cl D Sc μ [up i, dn i] [] (epsL i m) =
      bubL cs i μ ((r + m : ℕ) : ℤ) := by
  rw [psiSameCup, Category.assoc, cl_comp (sChain_dL i r) (sChain_epsL i m),
    ← epsL_add, ← bubL_nat]

/-- Dotted left cups in the inversion range are independent over morphisms into `1_μ`.
The anti-diagonal pairing is the unit `c_{μ;i}`, so no field assumption is needed. -/
theorem psiSameCup_independent (i : I) (μ : X) {T : (pres D Sc).Presented}
    (f : ℕ → (T ⟶ (pres D Sc).obj (ob D μ [])))
    (hf : ∑ r ∈ range (D.h i μ).toNat, f r ≫ psiSameCup cs i μ r = 0) :
    ∀ r, r < (D.h i μ).toNat → f r = 0 := by
  apply antitriangular_independent (D.h i μ).toNat (cs.c μ i)
    (psiSameCup cs i μ) (fun m => cl D Sc μ [up i, dn i] [] (epsL i m)) ?_ ?_ f hf
  · intro r m h
    rw [psiSameCup_eps, bubL_eq_zero_of_lt cs i μ (by omega)]
  · intro r hr
    rw [psiSameCup_eps, show ((r + ((D.h i μ).toNat - 1 - r) : ℕ) : ℤ) =
      D.h i μ - 1 by omega, bubL_eq_c]

/-- The scalar block of the raw positive-weight inverse matrix. -/
theorem psiSameCup_pair (i : I) (μ : X) (r s : ℕ)
    (hr : (r : ℤ) < D.h i μ) (hs : (s : ℤ) < D.h i μ) :
    psiSameCup cs i μ r ≫ psiSameCupDual cs i μ s = if r = s then 𝟙 _ else 0 := by
  classical
  have E := psiSameCup_complete cs i μ (by omega)
  have H : ∑ j ∈ range (D.h i μ).toNat,
      psiSameCup cs i μ r ≫ psiSameCupDual cs i μ j ≫ psiSameCup cs i μ j =
        psiSameCup cs i μ r := by
    have H := congrArg (fun g => psiSameCup cs i μ r ≫ g) E
    rw [Preadditive.comp_add, Preadditive.comp_neg, ← Category.assoc,
      psiSameCup_sigma cs i μ r hr, Limits.zero_comp, neg_zero, zero_add,
      Category.comp_id, Preadditive.comp_sum] at H
    exact H
  have Hzero : ∑ j ∈ range (D.h i μ).toNat,
      (psiSameCup cs i μ r ≫ psiSameCupDual cs i μ j - (if r = j then 𝟙 _ else 0)) ≫
        psiSameCup cs i μ j = 0 := by
    simp only [Preadditive.sub_comp, sum_sub_distrib, Category.assoc]
    rw [H]
    simp only [ite_comp, Category.id_comp, Limits.zero_comp]
    rw [sum_ite_eq_of_mem _ _ _ (mem_range.mpr (show r < (D.h i μ).toNat by omega)), sub_self]
  exact sub_eq_zero.mp (psiSameCup_independent cs i μ _ Hzero s (by omega))

/-- The dotted left cap in the raw negative-weight inversion matrix. -/
def psiSameCap (i : I) (μ : X) (r : ℕ) :
    (pres D Sc).obj (ob D μ [dn i, up i]) ⟶ (pres D Sc).obj (ob D μ []) :=
  cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] r) ≫ epsP cs i μ

/-- The bubble coefficient of the change from dotted left caps to diamonds. -/
def psiSameCapCoeff (i : I) (μ : X) (n r : ℕ) :
    (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ []) :=
  zsign k (D.parity i * ((D.h i μ + n + r + 1 : ℤ) : ZMod 2)) •
    bubL cs i μ (-(n : ℤ) - r - 2)

/-- The cup entry dual to the dotted left cap, before the ψ scalar factors. -/
def psiSameCapDual (i : I) (μ : X) (r : ℕ) :
    (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [dn i, up i]) :=
  ∑ n ∈ range (-D.h i μ).toNat,
    psiSameCapCoeff cs i μ n r ≫ cl D Sc μ [] [dn i, up i] (etaL i n)

/-- The negative-weight change matrix is anti-triangular. -/
theorem psiSameCapCoeff_zero (i : I) (μ : X) (n r : ℕ)
    (h : -D.h i μ ≤ (n : ℤ) + r) : psiSameCapCoeff cs i μ n r = 0 := by
  rw [psiSameCapCoeff, bubL_eq_zero_of_lt cs i μ (by omega), smul_zero]

/-- Totalized diamond-cap images vanish outside the range of (1.14). -/
theorem psiSameCapDual_zero (i : I) (μ : X) (r : ℕ) (h : -D.h i μ ≤ r) :
    psiSameCapDual cs i μ r = 0 := by
  apply sum_eq_zero
  intro n _
  rw [psiSameCapCoeff_zero cs i μ n r (by omega), Limits.zero_comp]

/-- The full rectangular sum for (5.12), with its zero tail included. -/
theorem psiSameCap_change (i : I) (μ : X) (n : ℕ) :
    cl D Sc μ [dn i, up i] [] (dcapL i n) =
      ∑ r ∈ range (-D.h i μ).toNat, psiSameCap cs i μ r ≫ psiSameCapCoeff cs i μ n r := by
  by_cases hn : (n : ℤ) < -D.h i μ
  · rw [eq_5_12 cs i μ n hn, dcapRHS]
    trans ∑ r ∈ range (-D.h i μ - n).toNat,
      psiSameCap cs i μ r ≫ psiSameCapCoeff cs i μ n r
    · apply sum_congr rfl
      intro r _
      simp only [psiSameCapCoeff, psiSameCap, Linear.comp_smul, Category.assoc]
    · apply sum_subset (range_mono (by omega))
      intro r _ hr
      rw [mem_range, not_lt] at hr
      rw [psiSameCapCoeff_zero cs i μ n r (by omega), Limits.comp_zero]
  · rw [cl_dcapZero Sc i μ n (by omega)]
    symm
    apply sum_eq_zero
    intro r _
    rw [psiSameCapCoeff_zero cs i μ n r (by omega), Limits.comp_zero]

/-- The rightward mixed crossing is killed by a dotted cap in the allowed range. -/
theorem psiSameCap_sigma (i : I) (μ : X) (r : ℕ) (hr : (r : ℤ) < -D.h i μ) :
    cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫ psiSameCap cs i μ r = 0 := by
  rw [psiSameCap, ← Category.assoc, cl_comp (sChain_sigmaL i i) (sChain_dR i r)]
  exact sigma_dots_epsP cs i μ (by omega) r hr

/-- Every dual cup entry is killed by the leftward mixed crossing. -/
theorem psiSameCap_dual_lcross (i : I) (μ : X) (r : ℕ) :
    psiSameCapDual cs i μ r ≫ cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) = 0 := by
  rw [psiSameCapDual, Preadditive.sum_comp]
  apply sum_eq_zero
  intro n hn
  rw [mem_range] at hn
  rw [Category.assoc, cl_comp (sChain_etaL i n) (sChain_lcrossL i i),
    cl_invM₃ Sc i μ n (by omega), Limits.comp_zero]

/-- The nontrivial diagonal block of the raw negative-weight inverse matrix. -/
theorem psiSameCap_complete (i : I) (μ : X) (hh : D.h i μ ≤ 0) :
    -(cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) ≫
      cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i)) +
      ∑ r ∈ range (-D.h i μ).toNat, psiSameCap cs i μ r ≫ psiSameCapDual cs i μ r = 𝟙 _ := by
  have E := cl_invM₁ Sc i μ hh
  rw [← cl_comp (sChain_lcrossL i i) (sChain_sigmaL i i), cl_nil] at E
  rw [← E]
  congr 1
  simp only [psiSameCapDual, Preadditive.comp_sum, ← Category.assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  rw [← Preadditive.sum_comp, ← psiSameCap_change cs i μ n,
    cl_comp (sChain_dcapL i n) (sChain_etaL i n)]

/-- Pairing a right cup with a dotted left cap is the corresponding bubble. -/
theorem psiSameCap_eta (i : I) (μ : X) (m r : ℕ) :
    cl D Sc μ [] [dn i, up i] (etaL i m) ≫ psiSameCap cs i μ r =
      bubR cs i μ ((m + r : ℕ) : ℤ) := by
  rw [psiSameCap, ← Category.assoc, cl_comp (sChain_etaL i m) (sChain_dR i r),
    ← etaL_add, ← bubR_nat]

/-- Dotted left caps in the inversion range are independent over morphisms out of `1_μ`. -/
theorem psiSameCap_independent (i : I) (μ : X) {T : (pres D Sc).Presented}
    (f : ℕ → ((pres D Sc).obj (ob D μ []) ⟶ T))
    (hf : ∑ r ∈ range (-D.h i μ).toNat, psiSameCap cs i μ r ≫ f r = 0) :
    ∀ r, r < (-D.h i μ).toNat → f r = 0 := by
  apply antitriangular_independent_right (-D.h i μ).toNat (cs.c μ i)⁻¹
    (fun m => cl D Sc μ [] [dn i, up i] (etaL i m)) (psiSameCap cs i μ) ?_ ?_ f hf
  · intro r m h
    rw [psiSameCap_eta, bubR_eq_zero_of_lt cs i μ (by omega)]
  · intro r hr
    rw [psiSameCap_eta, show ((((-D.h i μ).toNat - 1 - r) + r : ℕ) : ℤ) =
      -D.h i μ - 1 by omega, bubR_eq_c]

/-- The scalar block of the raw negative-weight inverse matrix. -/
theorem psiSameCap_pair (i : I) (μ : X) (r s : ℕ)
    (hr : (r : ℤ) < -D.h i μ) (hs : (s : ℤ) < -D.h i μ) :
    psiSameCapDual cs i μ s ≫ psiSameCap cs i μ r = if r = s then 𝟙 _ else 0 := by
  classical
  have E := psiSameCap_complete cs i μ (by omega)
  have H : ∑ j ∈ range (-D.h i μ).toNat,
      psiSameCap cs i μ j ≫ psiSameCapDual cs i μ j ≫ psiSameCap cs i μ r =
        psiSameCap cs i μ r := by
    have H := congrArg (fun g => g ≫ psiSameCap cs i μ r) E
    rw [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc,
      psiSameCap_sigma cs i μ r hr, Limits.comp_zero, neg_zero, zero_add,
      Category.id_comp, Preadditive.sum_comp] at H
    simpa only [Category.assoc] using H
  have Hzero : ∑ j ∈ range (-D.h i μ).toNat,
      psiSameCap cs i μ j ≫
        (psiSameCapDual cs i μ j ≫ psiSameCap cs i μ r - (if r = j then 𝟙 _ else 0)) = 0 := by
    simp only [Preadditive.comp_sub, sum_sub_distrib]
    rw [H]
    simp only [comp_ite, Category.comp_id, Limits.comp_zero]
    rw [sum_ite_eq_of_mem _ _ _ (mem_range.mpr (show r < (-D.h i μ).toNat by omega)), sub_self]
  exact sub_eq_zero.mp (psiSameCap_independent cs i μ _ Hzero s (by omega))

/-- Parity of the raw dotted left cup. -/
theorem psiSameCup_mem (i : I) (μ : X) (r : ℕ) :
    psiSameCup cs i μ r ∈ homPar D Sc μ [] [up i, dn i]
      (ipar D i μ + D.parity i * r) := by
  have h := comp_mem_homPar (etaP_mem cs i μ)
    (cl_mem_homPar (D := D) (Sc := Sc) (μ := μ) (sChain_dL i r) rfl)
  simpa only [parsum_dotsL, psiSameCup, mul_comm] using h

/-- Parity of the raw dotted left cap. -/
theorem psiSameCap_mem (i : I) (μ : X) (r : ℕ) :
    psiSameCap cs i μ r ∈ homPar D Sc μ [dn i, up i] []
      (D.parity i * r + ipar D i μ) := by
  have h := comp_mem_homPar
    (cl_mem_homPar (D := D) (Sc := Sc) (μ := μ) (sChain_dR i r) rfl) (epsP_mem cs i μ)
  simpa only [parsum_dotsL, psiSameCap, mul_comm] using h

/-- The dual cap has the same parity as the dotted left cup. -/
theorem psiSameCupDual_mem (i : I) (μ : X) (r : ℕ) :
    psiSameCupDual cs i μ r ∈ homPar D Sc μ [up i, dn i] []
      (ipar D i μ + D.parity i * r) := by
  refine Submodule.sum_mem _ fun n _ => ?_
  rw [psiSameCupCoeff, Linear.comp_smul]
  apply Submodule.smul_mem
  have h := comp_mem_homPar (epsL_mem i μ n) (bubR_mem cs i μ (-(n : ℤ) - r - 2))
  convert h using 2
  rw [ipar, parsum_epsL]
  push_cast
  generalize D.parity i = a
  generalize (D.h i μ : ZMod 2) = b
  generalize (n : ZMod 2) = c
  generalize (r : ZMod 2) = d
  revert a b c d
  decide

/-- The dual cup has the same parity as the dotted left cap. -/
theorem psiSameCapDual_mem (i : I) (μ : X) (r : ℕ) :
    psiSameCapDual cs i μ r ∈ homPar D Sc μ [] [dn i, up i]
      (D.parity i * r + ipar D i μ) := by
  refine Submodule.sum_mem _ fun n _ => ?_
  rw [psiSameCapCoeff, Linear.smul_comp]
  apply Submodule.smul_mem
  have h := comp_mem_homPar (bubL_mem cs i μ (-(n : ℤ) - r - 2)) (etaL_mem i μ n)
  convert h using 2
  rw [ipar, parsum_etaL]
  push_cast
  generalize D.parity i = a
  generalize (D.h i μ : ZMod 2) = b
  generalize (n : ZMod 2) = c
  generalize (r : ZMod 2) = d
  revert a b c d
  decide

/-- **Proposition 9.4, raw (1.13) matrix:** the leftward crossing and dotted
left cups have the displayed two-sided inverse. The five blocks are established
from presentation relations, not assumed as preservation data for ψ. -/
theorem psiSameCup_inversion (i : I) (μ : X) (hh : 0 ≤ D.h i μ) :
    (-(cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫
        cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i)) +
      ∑ r ∈ range (D.h i μ).toNat, psiSameCupDual cs i μ r ≫ psiSameCup cs i μ r = 𝟙 _) ∧
    (cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) ≫
        cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) = -𝟙 _) ∧
    (∀ r : ℕ, (r : ℤ) < D.h i μ →
      psiSameCup cs i μ r ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) = 0) ∧
    (∀ r : ℕ, cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) ≫
      psiSameCupDual cs i μ r = 0) ∧
    (∀ r s : ℕ, (r : ℤ) < D.h i μ → (s : ℤ) < D.h i μ →
      psiSameCup cs i μ r ≫ psiSameCupDual cs i μ s = if r = s then 𝟙 _ else 0) := by
  refine ⟨psiSameCup_complete cs i μ hh, ?_, psiSameCup_sigma cs i μ,
    psiSameCup_lcross_dual cs i μ, psiSameCup_pair cs i μ⟩
  rw [cl_comp (sChain_lcrossL i i) (sChain_sigmaL i i), cl_invP₂ Sc i μ hh, cl_nil]

/-- **Proposition 9.4, raw (1.14) matrix:** the leftward crossing and dotted
left caps have the displayed two-sided inverse, with all five blocks proved. -/
theorem psiSameCap_inversion (i : I) (μ : X) (hh : D.h i μ ≤ 0) :
    (-(cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) ≫
        cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i)) +
      ∑ r ∈ range (-D.h i μ).toNat, psiSameCap cs i μ r ≫ psiSameCapDual cs i μ r = 𝟙 _) ∧
    (cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫
        cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) = -𝟙 _) ∧
    (∀ r : ℕ, (r : ℤ) < -D.h i μ →
      cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫ psiSameCap cs i μ r = 0) ∧
    (∀ r : ℕ, psiSameCapDual cs i μ r ≫
      cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) = 0) ∧
    (∀ r s : ℕ, (r : ℤ) < -D.h i μ → (s : ℤ) < -D.h i μ →
      psiSameCapDual cs i μ s ≫ psiSameCap cs i μ r = if r = s then 𝟙 _ else 0) := by
  refine ⟨psiSameCap_complete cs i μ hh, ?_, psiSameCap_sigma cs i μ,
    psiSameCap_dual_lcross cs i μ, psiSameCap_pair cs i μ⟩
  rw [cl_comp (sChain_sigmaL i i) (sChain_lcrossL i i), cl_invM₂ Sc i μ hh, cl_nil]

end OddMath.SKM
