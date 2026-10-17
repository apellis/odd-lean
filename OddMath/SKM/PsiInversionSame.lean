/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Curls
import OddMath.SKM.ChevalleyRel
import OddMath.SKM.PsiInversion

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

`psiDottedCap_raw` and `psiDottedCup_raw` calculate the assigned dotted entries
from powers of the assigned dot and normalized target whiskering. Their scalar
factors cancel the Koszul factors in `psiSamePositive_inversion` and
`psiSameNegative_inversion`, which prove both five-block matrices in the shifted
super-opposite. The diamond entries have their source parity and integer degree,
and their totalized zero entries are proved. Boundary reindexing changes only
the proof of the left weight, not the underlying diagram.

The downstream use is the auxiliary-generator relation check for ψ. Contextual
relation descent, the strict graded 2-superfunctor, its envelope extension and
its categorical inverse remain separate obligations.
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

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

private theorem same_ud (μ : X) (i : I) : wt D μ [up i, dn i] = μ := by
  simp [wt, sh]
private theorem same_du (μ : X) (i : I) : wt D μ [dn i, up i] = μ := by
  simp [wt, sh]

/-- Reindex the left boundary of a target 2-morphism along an equality of weights. -/
def psiRebase {ν ν' μ : X} {s t : List (Letter I)}
    {hs : wt D μ s = ν} {ht : wt D μ t = ν} (h : ν = ν')
    (f : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ t ht) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) ν' μ s (hs.trans h) ⟶
      psiAt ν' μ t (ht.trans h) := by
  subst ν'
  exact f

/-- Reindexing the weight does not change the underlying diagram. -/
theorem psiRebase_unsop {ν ν' μ : X} {s t : List (Letter I)}
    {hs : wt D μ s = ν} {ht : wt D μ t = ν} (h : ν = ν')
    (f : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ t ht) :
    SOp.unsop (psiRebase h f) = SOp.unsop f := by
  subst ν'
  rfl

/-- Reindexing the left weight preserves parity. -/
theorem psiRebase_mem {ν ν' μ : X} {s t : List (Letter I)}
    {hs : wt D μ s = ν} {ht : wt D μ t = ν} (h : ν = ν')
    {f : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ t ht}
    {p : ZMod 2} (hf : f ∈ parity (R := k) _ _ p) :
    psiRebase h f ∈ parity (R := k) _ _ p := by
  subst ν'
  exact hf

/-- The mixed crossing at the common same-colour boundary. -/
def psiSameSigma (t : k) (μ : X) (i : I) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) μ μ [up i, dn i] (same_ud μ i) ⟶
      psiAt μ μ [dn i, up i] (same_du μ i) :=
  psiRebase (same_ud μ i) (psiSigma t μ i i)

/-- The inverse-crossing assignment at the common same-colour boundary. -/
def psiSameLCross (t : k) (μ : X) (i : I) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) μ μ [dn i, up i] (same_du μ i) ⟶
      psiAt μ μ [up i, dn i] (same_ud μ i) :=
  psiRebase (same_ud μ i) (psiLCross t μ i i)

/-- The assigned dot power on the upward strand to the left of `Fᵢ`. -/
def psiSameDotsLeft (t : k) (μ : X) (i : I) (r : ℕ) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) μ μ [up i, dn i] (same_ud μ i) ⟶
      psiAt μ μ [up i, dn i] (same_ud μ i) :=
  psiRebase (same_ud μ i)
    (psiWhiskerRight _ μ [up i] [up i] [dn i] rfl rfl
      (cpow (psiDot t (wt D μ [dn i]) i) r))

/-- The assigned dot power on the upward strand to the right of `Fᵢ`. -/
def psiSameDotsRight (t : k) (μ : X) (i : I) (r : ℕ) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) μ μ [dn i, up i] (same_du μ i) ⟶
      psiAt μ μ [dn i, up i] (same_du μ i) :=
  psiWhiskerLeft μ (wt D μ [up i]) μ [dn i] [up i] [up i] (same_du μ i) rfl rfl
    (cpow (psiDot t μ i) r)

/-- The image of a dotted right cap, using actual dot powers and whiskering. -/
def psiDottedCap (cs : CScalars Sc) (t : k) (μ : X) (i : I) (r : ℕ) :=
  psiSameDotsLeft (sy := sy) (hc := hc) t μ i r ≫ psiCap cs μ i

/-- The image of a dotted right cup, using actual dot powers and whiskering. -/
def psiDottedCup (cs : CScalars Sc) (t : k) (μ : X) (i : I) (r : ℕ) :=
  psiCup (sy := sy) (hc := hc) cs μ i ≫ psiSameDotsRight t μ i r

private theorem same_homPar_mem {μ : X} {s t : List (Letter I)} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ homPar D Sc μ s t p) :
    f ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ p := by
  refine Submodule.span_le.mpr ?_ hf
  rintro f ⟨L, hL, hp, rfl⟩
  rw [cl_of hL]
  apply Presentation.diag_mem_homDeg'
  rw [degree_parity_mkD]
  exact hp

private theorem same_dots_mem (μ : X) (i : I) (r : ℕ) :
    cl D Sc μ [up i] [up i] (dotsL [] i [] r) ∈
      homPar D Sc μ [up i] [up i] (r * D.parity i) :=
  cl_mem_homPar (sChain_dotsL [] i [] r) (parsum_dotsL [] i [] r)

/-- The scalar introduced by the right whiskering of the dot power. -/
theorem psiSameDotsLeft_raw (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (r : ℕ) :
    SOp.unsop (psiSameDotsLeft (Sc := Sc) (sy := sy) (hc := hc) t μ i r) =
      (psiCoeff t (r * D.parity i) * sign k (ipar D i μ * (r * D.parity i))) •
        cl D Sc μ [up i, dn i] [up i, dn i] (dotsL [] i [dn i] r) := by
  unfold psiSameDotsLeft
  rw [psiRebase_unsop, psiDot_power t ht]
  unfold psiDots
  rw [psiWhiskerRight_mk _ _ _ _ _ _ _ (Submodule.smul_mem _ _ (same_dots_mem _ i r))]
  simp only [SOp.unsop_mk', psiParity, psiWordAt, ob, wd, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Bool.false_eq_true, ↓reduceIte, add_zero, wt_nil]
  change sign k (ipar D i μ * (r * D.parity i)) •
    plcL D Sc μ [] [dn i] [up i] [up i]
      (psiCoeff t (r * D.parity i) • cl D Sc (wt D μ [dn i]) [up i] [up i] (dotsL [] i [] r)) = _
  rw [(plcL D Sc μ [] [dn i] [up i] [up i]).map_smul, plcL_cl, smul_smul, mul_comm]
  simp only [dotsL, List.map_replicate, whL, List.nil_append, List.append_nil, List.cons_append]

/-- The scalar introduced by left whiskering with the shifted downward strand. -/
theorem psiSameDotsRight_raw (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (r : ℕ) :
    SOp.unsop (psiSameDotsRight (Sc := Sc) (sy := sy) (hc := hc) t μ i r) =
      (psiCoeff t (r * D.parity i) * sign k (ipar D i μ * (r * D.parity i))) •
        cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] r) := by
  unfold psiSameDotsRight
  rw [psiDot_power t ht]
  unfold psiDots
  rw [psiWhiskerLeft_mk _ _ _ _ _ _ _ _ _ (Submodule.smul_mem _ _ (same_dots_mem μ i r))]
  simp only [SOp.unsop_mk', psiParity, psiWordAt, ob, wd, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Bool.false_eq_true, ↓reduceIte, add_zero, wt_nil]
  rw [ipar_wt_up]
  change sign k (ipar D i μ * (r * D.parity i)) •
    plcL D Sc μ [dn i] [] [up i] [up i]
      (psiCoeff t (r * D.parity i) • cl D Sc μ [up i] [up i] (dotsL [] i [] r)) = _
  have H : plcL D Sc μ [dn i] [] [up i] [up i]
      (cl D Sc μ [up i] [up i] (dotsL [] i [] r)) =
      cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] r) := by
    simpa only [wt_nil, dotsL, List.map_replicate, whL, List.nil_append, List.append_nil,
      List.cons_append] using plcL_cl D Sc μ [dn i] [] [up i] [up i] (dotsL [] i [] r)
  rw [(plcL D Sc μ [dn i] [] [up i] [up i]).map_smul, smul_smul, mul_comm]
  exact congrArg (fun f => (psiCoeff t (r * D.parity i) *
    sign k (ipar D i μ * (r * D.parity i))) • f) H

private theorem same_dots_parity (t : k) (μ : X) (i : I) (r : ℕ) :
    psiDots (Sc := Sc) (sy := sy) (hc := hc) t μ i r ∈
      parity (R := k) _ _ (r * D.parity i) := by
  change psiCoeff t (r * D.parity i) • cl D Sc μ [up i] [up i] (dotsL [] i [] r) ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (r * D.parity i + (0 + 0))
  simpa only [add_zero] using Submodule.smul_mem _ (psiCoeff t (r * D.parity i))
    (same_homPar_mem (same_dots_mem (Sc := Sc) μ i r))

theorem psiSameDotsLeft_mem (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (r : ℕ) :
    psiSameDotsLeft (Sc := Sc) (sy := sy) (hc := hc) t μ i r ∈
      parity (R := k) _ _ (r * D.parity i) := by
  unfold psiSameDotsLeft
  apply psiRebase_mem
  exact psiWhiskerRight_mem (sy := sy) (hc := hc) _ μ [up i] [up i] [dn i] rfl rfl
    (by rw [psiDot_power t ht]; exact same_dots_parity (sy := sy) (hc := hc) t _ i r)

theorem psiSameDotsRight_mem (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (r : ℕ) :
    psiSameDotsRight (Sc := Sc) (sy := sy) (hc := hc) t μ i r ∈
      parity (R := k) _ _ (r * D.parity i) := by
  unfold psiSameDotsRight
  exact psiWhiskerLeft_mem (sy := sy) (hc := hc) μ (wt D μ [up i]) μ
    [dn i] [up i] [up i] (same_du μ i) rfl rfl
    (by rw [psiDot_power t ht]; exact same_dots_parity (sy := sy) (hc := hc) t μ i r)

/-- Dotted-cap coefficient calculated from the printed assignments and whiskerings. -/
theorem psiDottedCap_raw (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (r : ℕ) :
    SOp.unsop (psiDottedCap (sy := sy) (hc := hc) cs t μ i r) =
      (psiCoeff t (r * D.parity i) * sign k (ipar D i μ * (r * D.parity i + 1))) •
        psiSameCup cs i μ r := by
  unfold psiDottedCap
  rw [SOp.comp_of_mem (f := psiSameDotsLeft (sy := sy) (hc := hc) t μ i r)
    (g := psiCap cs μ i) (psiSameDotsLeft_mem t ht μ i r) (psiCap_mem_parity cs μ i)]
  simp only [mul_zero, sign_zero, one_smul]
  rw [psiSameDotsLeft_raw t ht]
  change (sign k (ipar D i μ) • etaP cs i μ) ≫ (_ • _) = _
  rw [Linear.smul_comp, Linear.comp_smul, smul_smul]
  congr 1
  rw [mul_add, mul_one, sign_add]
  ring

/-- Dotted-cup coefficient calculated from the printed assignments and whiskerings. -/
theorem psiDottedCup_raw (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (r : ℕ) :
    SOp.unsop (psiDottedCup (sy := sy) (hc := hc) cs t μ i r) =
      (psiCoeff t (r * D.parity i) * sign k (ipar D i μ * (r * D.parity i))) •
        psiSameCap cs i μ r := by
  unfold psiDottedCup
  rw [SOp.comp_of_mem (f := psiCup (sy := sy) (hc := hc) cs μ i)
    (g := psiSameDotsRight t μ i r) (psiCup_mem_parity cs μ i) (psiSameDotsRight_mem t ht μ i r)]
  simp only [zero_mul, sign_zero, one_smul]
  rw [psiSameDotsRight_raw t ht]
  change (_ • _) ≫ epsP cs i μ = _
  rw [Linear.smul_comp]
  rfl

/-- The diamond cup entry determined by the positive-weight inverse matrix. -/
def psiDiamondCup (cs : CScalars Sc) (t : k) (μ : X) (i : I) (r : ℕ) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) μ μ [] rfl ⟶
      psiAt μ μ [up i, dn i] (same_ud μ i) :=
  SOp.mk' ((psiCoeff t (r * D.parity i) * sign k (ipar D i μ * (r * D.parity i + 1))) •
    psiSameCupDual cs i μ r)

/-- The diamond cap entry determined by the negative-weight inverse matrix. -/
def psiDiamondCap (cs : CScalars Sc) (t : k) (μ : X) (i : I) (r : ℕ) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) μ μ [dn i, up i] (same_du μ i) ⟶
      psiAt μ μ [] rfl :=
  SOp.mk' ((psiCoeff t (r * D.parity i) * sign k (ipar D i μ * (r * D.parity i))) •
    psiSameCapDual cs i μ r)

/-- The totalized diamond-cup assignment vanishes beyond the positive range. -/
theorem psiDiamondCup_zero (cs : CScalars Sc) (t : k) (μ : X) (i : I) (r : ℕ)
    (hr : D.h i μ ≤ r) : psiDiamondCup (sy := sy) (hc := hc) cs t μ i r = 0 := by
  apply SOp.hom_ext
  change (_ : k) • psiSameCupDual cs i μ r = 0
  rw [psiSameCupDual_zero cs i μ r hr, smul_zero]

/-- The totalized diamond-cap assignment vanishes beyond the negative range. -/
theorem psiDiamondCap_zero (cs : CScalars Sc) (t : k) (μ : X) (i : I) (r : ℕ)
    (hr : -D.h i μ ≤ r) : psiDiamondCap (sy := sy) (hc := hc) cs t μ i r = 0 := by
  apply SOp.hom_ext
  change (_ : k) • psiSameCapDual cs i μ r = 0
  rw [psiSameCapDual_zero cs i μ r hr, smul_zero]

private theorem same_ud_parity (μ : X) (i : I) :
    psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) μ μ [up i, dn i] (same_ud μ i)) =
      ipar D i μ := by simp [psiParity, psiWordAt, ob, wd]
private theorem same_du_parity (μ : X) (i : I) :
    psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) μ μ [dn i, up i] (same_du μ i)) =
      ipar D i μ := by simpa [psiParity, psiWordAt, ob, wd] using ipar_wt_up (D := D) i μ

/-- The dotted-cap image has parity `r|i|` in the shifted target. -/
theorem psiDottedCap_mem (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (r : ℕ) :
    psiDottedCap (sy := sy) (hc := hc) cs t μ i r ∈ parity (R := k) _ _ (r * D.parity i) := by
  simpa only [psiDottedCap, add_zero] using comp_mem
    (psiSameDotsLeft_mem (Sc := Sc) (sy := sy) (hc := hc) t ht μ i r)
    (psiCap_mem_parity (sy := sy) (hc := hc) cs μ i)

/-- The dotted-cup image has parity `r|i|` in the shifted target. -/
theorem psiDottedCup_mem (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (r : ℕ) :
    psiDottedCup (sy := sy) (hc := hc) cs t μ i r ∈ parity (R := k) _ _ (r * D.parity i) := by
  simpa only [psiDottedCup, zero_add] using comp_mem
    (psiCup_mem_parity (sy := sy) (hc := hc) cs μ i)
    (psiSameDotsRight_mem (Sc := Sc) (sy := sy) (hc := hc) t ht μ i r)

/-- The diamond-cup image has parity `r|i|` after the downward Π-shift. -/
theorem psiDiamondCup_mem (cs : CScalars Sc) (t : k) (μ : X) (i : I) (r : ℕ) :
    psiDiamondCup (sy := sy) (hc := hc) cs t μ i r ∈ parity (R := k) _ _ (r * D.parity i) := by
  change (_ : k) • psiSameCupDual cs i μ r ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
      (r * D.parity i + (psiParity (sy := sy) (hc := hc)
        (psiWordAt (Sc := Sc) μ μ [up i, dn i] (same_ud μ i)) + 0))
  rw [same_ud_parity, add_zero]
  apply Submodule.smul_mem
  simpa only [mul_comm, add_comm] using same_homPar_mem (psiSameCupDual_mem cs i μ r)

/-- The diamond-cap image has parity `r|i|` after the downward Π-shift. -/
theorem psiDiamondCap_mem (cs : CScalars Sc) (t : k) (μ : X) (i : I) (r : ℕ) :
    psiDiamondCap (sy := sy) (hc := hc) cs t μ i r ∈ parity (R := k) _ _ (r * D.parity i) := by
  change (_ : k) • psiSameCapDual cs i μ r ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
      (r * D.parity i + (0 + psiParity (sy := sy) (hc := hc)
        (psiWordAt (Sc := Sc) μ μ [dn i, up i] (same_du μ i))))
  rw [same_du_parity, zero_add]
  apply Submodule.smul_mem
  simpa only [mul_comm] using same_homPar_mem (psiSameCapDual_mem cs i μ r)

private theorem same_coeff_cancel (t : k) (ht : t ^ 2 = -1) (q b : ZMod 2) :
    sign k (q * q) * (psiCoeff t q * sign k b) * (psiCoeff t q * sign k b) = 1 := by
  have h := psiCoeff_comp ht q q
  rw [zmod2_add_self, psiCoeff_zero] at h
  calc
    _ = (sign k (q * q) * (psiCoeff t q * psiCoeff t q)) *
      (sign k b * sign k b) := by ring
    _ = 1 := by rw [h, sign_mul_self, mul_one]

private theorem sameSigma_mem (t : k) (μ : X) (i : I) :
    psiSameSigma (Sc := Sc) (sy := sy) (hc := hc) t μ i ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [psiSameSigma, zmod2_mul_self] using psiRebase_mem (same_ud μ i)
    (psiSigma_mem_parity (Sc := Sc) (sy := sy) (hc := hc) t μ i i)
/-- The normalized inverse crossing retains its source parity. -/
theorem psiSameLCross_mem_parity (t : k) (μ : X) (i : I) :
    psiSameLCross (Sc := Sc) (sy := sy) (hc := hc) t μ i ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [psiSameLCross, zmod2_mul_self] using psiRebase_mem (same_ud μ i)
    (psiLCross_mem_parity (Sc := Sc) (sy := sy) (hc := hc) t μ i i)

private theorem sameSigma_raw (t : k) (μ : X) (i : I) :
    SOp.unsop (psiSameSigma (Sc := Sc) (sy := sy) (hc := hc) t μ i) =
      (psiCoeff t (D.parity i) * sign k (D.parity i * ipar D i μ)) •
        cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) := by
  rw [psiSameSigma, psiRebase_unsop]
  simp only [psiSigma, zmod2_mul_self, SOp.unsop_mk']
private theorem sameLCross_raw (t : k) (μ : X) (i : I) :
    SOp.unsop (psiSameLCross (Sc := Sc) (sy := sy) (hc := hc) t μ i) =
      (psiCoeff t (D.parity i) * sign k (D.parity i * ipar D i μ)) •
        cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) := by
  rw [psiSameLCross, psiRebase_unsop]
  simp only [psiLCross, zmod2_mul_self, SOp.unsop_mk']

private theorem sameSigma_LCross_raw (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) :
    SOp.unsop (psiSameSigma (Sc := Sc) (sy := sy) (hc := hc) t μ i ≫ psiSameLCross t μ i) =
      cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫
        cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) := by
  rw [SOp.comp_of_mem (f := psiSameSigma (sy := sy) (hc := hc) t μ i)
    (g := psiSameLCross t μ i) (sameSigma_mem t μ i) (psiSameLCross_mem_parity t μ i),
    sameSigma_raw, sameLCross_raw]
  change _ • ((_ • _) ≫ (_ • _)) = _
  rw [Linear.smul_comp, Linear.comp_smul, smul_smul, smul_smul, same_coeff_cancel t ht, one_smul]
  rfl

private theorem sameLCross_Sigma_raw (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) :
    SOp.unsop (psiSameLCross (Sc := Sc) (sy := sy) (hc := hc) t μ i ≫ psiSameSigma t μ i) =
      cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) ≫
        cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) := by
  rw [SOp.comp_of_mem (f := psiSameLCross (sy := sy) (hc := hc) t μ i)
    (g := psiSameSigma t μ i) (psiSameLCross_mem_parity t μ i) (sameSigma_mem t μ i),
    sameSigma_raw, sameLCross_raw]
  change _ • ((_ • _) ≫ (_ • _)) = _
  rw [Linear.smul_comp, Linear.comp_smul, smul_smul, smul_smul, same_coeff_cancel t ht, one_smul]
  rfl

private theorem sameCap_Diamond_raw (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (r : ℕ) :
    SOp.unsop (psiDottedCap (sy := sy) (hc := hc) cs t μ i r ≫ psiDiamondCup cs t μ i r) =
      psiSameCupDual cs i μ r ≫ psiSameCup cs i μ r := by
  rw [SOp.comp_of_mem (f := psiDottedCap (sy := sy) (hc := hc) cs t μ i r)
    (g := psiDiamondCup cs t μ i r) (psiDottedCap_mem cs t ht μ i r) (psiDiamondCup_mem cs t μ i r),
    psiDottedCap_raw cs t ht]
  change _ • ((_ • _) ≫ (_ • _)) = _
  rw [Linear.smul_comp, Linear.comp_smul, smul_smul, smul_smul, same_coeff_cancel t ht, one_smul]
  rfl

private theorem sameDiamond_Cup_raw (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (r : ℕ) :
    SOp.unsop (psiDiamondCap (sy := sy) (hc := hc) cs t μ i r ≫ psiDottedCup cs t μ i r) =
      psiSameCap cs i μ r ≫ psiSameCapDual cs i μ r := by
  rw [SOp.comp_of_mem (f := psiDiamondCap (sy := sy) (hc := hc) cs t μ i r)
    (g := psiDottedCup cs t μ i r) (psiDiamondCap_mem cs t μ i r) (psiDottedCup_mem cs t ht μ i r),
    psiDottedCup_raw cs t ht]
  change _ • ((_ • _) ≫ (_ • _)) = _
  rw [Linear.smul_comp, Linear.comp_smul, smul_smul, smul_smul, same_coeff_cancel t ht, one_smul]
  rfl

private theorem same_scaled_zero {A B C : (pres D Sc).Presented}
    (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0) (a b c : k) :
    a • ((b • f) ≫ (c • g)) = 0 := by
  rw [Linear.smul_comp, Linear.comp_smul, h, smul_zero, smul_zero, smul_zero]

private theorem same_scaled_pair {A B : (pres D Sc).Presented}
    (f : A ⟶ B) (g : B ⟶ A) (r s : ℕ)
    (h : f ≫ g = if r = s then 𝟙 A else 0) (a b c : k)
    (habc : r = s → a * b * c = 1) :
    a • ((b • f) ≫ (c • g)) = if r = s then 𝟙 A else 0 := by
  rw [Linear.smul_comp, Linear.comp_smul, h]
  split_ifs with hrs
  · rw [smul_smul, smul_smul, habc hrs, one_smul]
  · simp only [smul_zero]

/-- The normalized same-colour crossing is the assigned mixed composite (1.11). -/
theorem psiSameSigma_eq_composite (cs : CScalars Sc) (t : k) (μ : X) (i : I) :
    psiRebase (same_ud μ i) (psiSigmaCup (sy := sy) (hc := hc) cs μ i i ≫
      psiSigmaMiddle t μ i i ≫ psiSigmaCap cs μ i i) = psiSameSigma t μ i := by
  rw [psiSigma_eq_composite]
  rfl

/-- Completeness block of the positive-weight inversion matrix in the ψ target. -/
theorem psi_invP₁ (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (hh : 0 ≤ D.h i μ) :
    -(psiSameSigma (sy := sy) (hc := hc) t μ i ≫ psiSameLCross t μ i) +
      ∑ r ∈ range (D.h i μ).toNat, psiDottedCap cs t μ i r ≫ psiDiamondCup cs t μ i r = 𝟙 _ := by
  apply SOp.hom_ext
  change (SOp.unsopₗ _ _) (_ + _) = 𝟙 _
  rw [map_add, map_neg, map_sum]
  change -SOp.unsop (psiSameSigma (sy := sy) (hc := hc) t μ i ≫ psiSameLCross t μ i) +
    ∑ r ∈ range (D.h i μ).toNat,
      SOp.unsop (psiDottedCap cs t μ i r ≫ psiDiamondCup cs t μ i r) = 𝟙 _
  simp only [sameSigma_LCross_raw t ht, sameCap_Diamond_raw cs t ht]
  exact psiSameCup_complete cs i μ hh

/-- Crossing block of the positive-weight inversion matrix. -/
theorem psi_invP₂ (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (hh : 0 ≤ D.h i μ) :
    psiSameLCross (Sc := Sc) (sy := sy) (hc := hc) t μ i ≫ psiSameSigma t μ i = -𝟙 _ := by
  apply SOp.hom_ext
  rw [sameLCross_Sigma_raw t ht]
  change cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) ≫
    cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) = -𝟙 _
  rw [cl_comp (sChain_lcrossL i i) (sChain_sigmaL i i), cl_invP₂ Sc i μ hh, cl_nil]

/-- First off-diagonal zero block of the positive-weight inversion matrix. -/
theorem psi_invP₃ (cs : CScalars Sc) (t : k) (μ : X) (i : I) (r : ℕ) :
    psiDiamondCup (sy := sy) (hc := hc) cs t μ i r ≫ psiSameSigma t μ i = 0 := by
  apply SOp.hom_ext
  rw [SOp.comp_of_mem (f := psiDiamondCup (sy := sy) (hc := hc) cs t μ i r)
    (g := psiSameSigma t μ i) (psiDiamondCup_mem cs t μ i r) (sameSigma_mem t μ i), sameSigma_raw]
  change _ • ((_ • _) ≫ (_ • _)) = 0
  exact same_scaled_zero _ _ (psiSameCup_lcross_dual cs i μ r) _ _ _

/-- Second off-diagonal zero block of the positive-weight inversion matrix. -/
theorem psi_invP₄ (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (r : ℕ) (hr : (r : ℤ) < D.h i μ) :
    psiSameLCross (sy := sy) (hc := hc) t μ i ≫ psiDottedCap cs t μ i r = 0 := by
  apply SOp.hom_ext
  rw [SOp.comp_of_mem (f := psiSameLCross (sy := sy) (hc := hc) t μ i)
    (g := psiDottedCap cs t μ i r) (psiSameLCross_mem_parity t μ i) (psiDottedCap_mem cs t ht μ i r),
    sameLCross_raw, psiDottedCap_raw cs t ht]
  change _ • ((_ • _) ≫ (_ • _)) = 0
  exact same_scaled_zero _ _ (psiSameCup_sigma cs i μ r hr) _ _ _

/-- Scalar block of the positive-weight inversion matrix, with the Koszul sign cancelled. -/
theorem psi_invP₅ (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (r s : ℕ) (hr : (r : ℤ) < D.h i μ) (hs : (s : ℤ) < D.h i μ) :
    psiDiamondCup (sy := sy) (hc := hc) cs t μ i s ≫ psiDottedCap cs t μ i r =
      if r = s then 𝟙 _ else 0 := by
  classical
  apply SOp.hom_ext
  rw [SOp.comp_of_mem (f := psiDiamondCup (sy := sy) (hc := hc) cs t μ i s)
    (g := psiDottedCap cs t μ i r) (psiDiamondCup_mem cs t μ i s) (psiDottedCap_mem cs t ht μ i r),
    psiDottedCap_raw cs t ht]
  change _ • ((_ • psiSameCup cs i μ r) ≫ (_ • psiSameCupDual cs i μ s)) = _
  have H := same_scaled_pair _ _ r s (psiSameCup_pair cs i μ r s hr hs)
    (sign k ((s * D.parity i) * (r * D.parity i)))
    (psiCoeff t (r * D.parity i) * sign k (ipar D i μ * (r * D.parity i + 1)))
    (psiCoeff t (s * D.parity i) * sign k (ipar D i μ * (s * D.parity i + 1)))
    (by rintro rfl; exact same_coeff_cancel t ht _ _)
  split_ifs at H ⊢ <;> exact H

/-- Completeness block of the negative-weight inversion matrix in the ψ target. -/
theorem psi_invM₁ (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (hh : D.h i μ ≤ 0) :
    -(psiSameLCross (sy := sy) (hc := hc) t μ i ≫ psiSameSigma t μ i) +
      ∑ r ∈ range (-D.h i μ).toNat, psiDiamondCap cs t μ i r ≫ psiDottedCup cs t μ i r = 𝟙 _ := by
  apply SOp.hom_ext
  change (SOp.unsopₗ _ _) (_ + _) = 𝟙 _
  rw [map_add, map_neg, map_sum]
  change -SOp.unsop (psiSameLCross (sy := sy) (hc := hc) t μ i ≫ psiSameSigma t μ i) +
    ∑ r ∈ range (-D.h i μ).toNat,
      SOp.unsop (psiDiamondCap cs t μ i r ≫ psiDottedCup cs t μ i r) = 𝟙 _
  simp only [sameLCross_Sigma_raw t ht, sameDiamond_Cup_raw cs t ht]
  exact psiSameCap_complete cs i μ hh

/-- Crossing block of the negative-weight inversion matrix. -/
theorem psi_invM₂ (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (hh : D.h i μ ≤ 0) :
    psiSameSigma (Sc := Sc) (sy := sy) (hc := hc) t μ i ≫ psiSameLCross t μ i = -𝟙 _ := by
  apply SOp.hom_ext
  rw [sameSigma_LCross_raw t ht]
  change cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫
    cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i) = -𝟙 _
  rw [cl_comp (sChain_sigmaL i i) (sChain_lcrossL i i), cl_invM₂ Sc i μ hh, cl_nil]

/-- First off-diagonal zero block of the negative-weight inversion matrix. -/
theorem psi_invM₃ (cs : CScalars Sc) (t : k) (μ : X) (i : I) (r : ℕ) :
    psiSameSigma (sy := sy) (hc := hc) t μ i ≫ psiDiamondCap cs t μ i r = 0 := by
  apply SOp.hom_ext
  rw [SOp.comp_of_mem (f := psiSameSigma (sy := sy) (hc := hc) t μ i)
    (g := psiDiamondCap cs t μ i r) (sameSigma_mem t μ i) (psiDiamondCap_mem cs t μ i r), sameSigma_raw]
  change _ • ((_ • _) ≫ (_ • _)) = 0
  exact same_scaled_zero _ _ (psiSameCap_dual_lcross cs i μ r) _ _ _

/-- Second off-diagonal zero block of the negative-weight inversion matrix. -/
theorem psi_invM₄ (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (r : ℕ) (hr : (r : ℤ) < -D.h i μ) :
    psiDottedCup (sy := sy) (hc := hc) cs t μ i r ≫ psiSameLCross t μ i = 0 := by
  apply SOp.hom_ext
  rw [SOp.comp_of_mem (f := psiDottedCup (sy := sy) (hc := hc) cs t μ i r)
    (g := psiSameLCross t μ i) (psiDottedCup_mem cs t ht μ i r) (psiSameLCross_mem_parity t μ i),
    sameLCross_raw, psiDottedCup_raw cs t ht]
  change _ • ((_ • _) ≫ (_ • _)) = 0
  exact same_scaled_zero _ _ (psiSameCap_sigma cs i μ r hr) _ _ _

/-- Scalar block of the negative-weight inversion matrix. -/
theorem psi_invM₅ (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (r s : ℕ) (hr : (r : ℤ) < -D.h i μ) (hs : (s : ℤ) < -D.h i μ) :
    psiDottedCup (sy := sy) (hc := hc) cs t μ i r ≫ psiDiamondCap cs t μ i s =
      if r = s then 𝟙 _ else 0 := by
  classical
  apply SOp.hom_ext
  rw [SOp.comp_of_mem (f := psiDottedCup (sy := sy) (hc := hc) cs t μ i r)
    (g := psiDiamondCap cs t μ i s) (psiDottedCup_mem cs t ht μ i r) (psiDiamondCap_mem cs t μ i s),
    psiDottedCup_raw cs t ht]
  change _ • ((_ • psiSameCapDual cs i μ s) ≫ (_ • psiSameCap cs i μ r)) = _
  have H := same_scaled_pair _ _ r s (psiSameCap_pair cs i μ r s hr hs)
    (sign k ((r * D.parity i) * (s * D.parity i)))
    (psiCoeff t (s * D.parity i) * sign k (ipar D i μ * (s * D.parity i)))
    (psiCoeff t (r * D.parity i) * sign k (ipar D i μ * (r * D.parity i)))
    (by rintro rfl; exact same_coeff_cancel t ht _ _)
  split_ifs at H ⊢ <;> exact H

private theorem same_cl_degree {μ : X} {s t : List (Letter I)} {L : List (LayerData I)} {d : ℤ}
    (h : SChain s L t) (hd : gsum D sy μ L = d) :
    cl D Sc μ s t L ∈ (pres D Sc).homDeg (gdeg D sy) _ _ d := by
  rw [cl_of h]
  apply Presentation.diag_mem_homDeg'
  rwa [degree_gdeg_mkD]

private theorem same_bubR_degree (cs : CScalars Sc) (μ : X) (i : I) (z : ℤ) (hz : z < 0) :
    bubR cs i μ z ∈ (pres D Sc).homDeg (gdeg D sy) _ _ (2 * sy.d i * (z + D.h i μ + 1)) := by
  rw [bubR, ite_eq_right (by omega)]
  split_ifs with h h'
  · apply Submodule.smul_mem
    apply same_cl_degree ((sChain_dcupL i _).append (sChain_epsL i _))
    rw [gsum_append, gsum_dcupL, gsum_epsL,
      Int.toNat_of_nonneg (show 0 ≤ -z - 1 by omega),
      Int.toNat_of_nonneg (show 0 ≤ D.h i μ by omega)]
    ring
  · apply Submodule.smul_mem
    have he : 2 * sy.d i * (z + D.h i μ + 1) = 0 := by rw [h']; ring
    rw [he]
    exact Presentation.id_mem_homDeg _ _ _
  · exact Submodule.zero_mem _

private theorem same_bubL_degree (cs : CScalars Sc) (μ : X) (i : I) (z : ℤ) (hz : z < 0) :
    bubL cs i μ z ∈ (pres D Sc).homDeg (gdeg D sy) _ _ (2 * sy.d i * (z - D.h i μ + 1)) := by
  rw [bubL, ite_eq_right (by omega)]
  split_ifs with h h'
  · apply Submodule.smul_mem
    apply same_cl_degree ((sChain_etaL i _).append (sChain_dcapL i _))
    rw [gsum_append, gsum_etaL, gsum_dcapL,
      Int.toNat_of_nonneg (show 0 ≤ -D.h i μ by omega),
      Int.toNat_of_nonneg (show 0 ≤ -z - 1 by omega)]
    ring
  · apply Submodule.smul_mem
    have he : 2 * sy.d i * (z - D.h i μ + 1) = 0 := by rw [h']; ring
    rw [he]
    exact Presentation.id_mem_homDeg _ _ _
  · exact Submodule.zero_mem _

/-- Integer degree of the positive bubble-sum inverse entry. -/
theorem psiSameCupDual_mem_degree (cs : CScalars Sc) (μ : X) (i : I) (r : ℕ) :
    psiSameCupDual cs i μ r ∈ (pres D Sc).homDeg (gdeg D sy) _ _
      (sy.d i * (D.h i μ - 1 - 2 * r)) := by
  unfold psiSameCupDual
  apply Submodule.sum_mem
  intro n _
  unfold psiSameCupCoeff
  have hcap := same_cl_degree (Sc := Sc) (sy := sy) (sChain_epsL i n) (gsum_epsL D sy μ i n)
  have hbub := Submodule.smul_mem _ (zsign k (D.parity i * ((D.h i μ + n + r + 1 : ℤ) : ZMod 2)))
    (same_bubR_degree (sy := sy) cs μ i (-(n : ℤ) - r - 2) (by omega))
  have h := Presentation.comp_mem_homDeg hcap hbub
  convert h using 1
  ring

/-- Integer degree of the negative bubble-sum inverse entry. -/
theorem psiSameCapDual_mem_degree (cs : CScalars Sc) (μ : X) (i : I) (r : ℕ) :
    psiSameCapDual cs i μ r ∈ (pres D Sc).homDeg (gdeg D sy) _ _
      (-(sy.d i * (D.h i μ + 1 + 2 * r))) := by
  unfold psiSameCapDual
  apply Submodule.sum_mem
  intro n _
  unfold psiSameCapCoeff
  have hcup := same_cl_degree (Sc := Sc) (sy := sy) (sChain_etaL i n) (gsum_etaL D sy μ i n)
  have hbub := Submodule.smul_mem _ (zsign k (D.parity i * ((D.h i μ + n + r + 1 : ℤ) : ZMod 2)))
    (same_bubL_degree (sy := sy) cs μ i (-(n : ℤ) - r - 2) (by omega))
  have h := Presentation.comp_mem_homDeg hbub hcup
  convert h using 1
  ring

/-- The diamond-cup assignment has the integer degree of the source generator. -/
theorem psiDiamondCup_mem_degree (cs : CScalars Sc) (t : k) (μ : X) (i : I) (r : ℕ) :
    psiDiamondCup (sy := sy) (hc := hc) cs t μ i r ∈
      GradedSupercategory.degree (R := k) _ _ (sy.d i * (D.h i μ - 1 - 2 * r)) := by
  change (_ : k) • psiSameCupDual cs i μ r ∈ (pres D Sc).homDeg (gdeg D sy) _ _
    (sy.d i * (D.h i μ - 1 - 2 * r) + (0 - 0))
  rw [sub_self, add_zero]
  exact Submodule.smul_mem _ _ (psiSameCupDual_mem_degree cs μ i r)

/-- The diamond-cap assignment has the integer degree of the source generator. -/
theorem psiDiamondCap_mem_degree (cs : CScalars Sc) (t : k) (μ : X) (i : I) (r : ℕ) :
    psiDiamondCap (sy := sy) (hc := hc) cs t μ i r ∈
      GradedSupercategory.degree (R := k) _ _ (-(sy.d i * (D.h i μ + 1 + 2 * r))) := by
  change (_ : k) • psiSameCapDual cs i μ r ∈ (pres D Sc).homDeg (gdeg D sy) _ _
    (-(sy.d i * (D.h i μ + 1 + 2 * r)) + (0 - 0))
  rw [sub_self, add_zero]
  exact Submodule.smul_mem _ _ (psiSameCapDual_mem_degree cs μ i r)

/-- Reindexing the left boundary preserves integer degree. -/
theorem psiRebase_mem_degree {ν ν' μ : X} {s t : List (Letter I)}
    {hs : wt D μ s = ν} {ht : wt D μ t = ν} (h : ν = ν')
    {f : psiAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s hs ⟶ psiAt ν μ t ht}
    {d : ℤ} (hf : f ∈ GradedSupercategory.degree (R := k) _ _ d) :
    psiRebase h f ∈ GradedSupercategory.degree (R := k) _ _ d := by
  subst ν'
  exact hf

/-- The normalized same-colour inverse crossing retains integer degree zero. -/
theorem psiSameLCross_mem_degree (t : k) (μ : X) (i : I) :
    psiSameLCross (Sc := Sc) (sy := sy) (hc := hc) t μ i ∈
      GradedSupercategory.degree (R := k) _ _ 0 :=
  psiRebase_mem_degree (same_ud μ i) (psiLCross_mem_degree (sy := sy) (hc := hc) t μ i i)

/-- **Proposition 9.4, (1.13):** all five positive-weight inverse blocks for
ψ in the shifted super-opposite, with no preservation premise. -/
theorem psiSamePositive_inversion (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (hh : 0 ≤ D.h i μ) :
    (-(psiSameSigma (sy := sy) (hc := hc) t μ i ≫ psiSameLCross t μ i) +
      ∑ r ∈ range (D.h i μ).toNat, psiDottedCap cs t μ i r ≫ psiDiamondCup cs t μ i r = 𝟙 _) ∧
    (psiSameLCross (Sc := Sc) (sy := sy) (hc := hc) t μ i ≫ psiSameSigma t μ i = -𝟙 _) ∧
    (∀ r, psiDiamondCup (sy := sy) (hc := hc) cs t μ i r ≫ psiSameSigma t μ i = 0) ∧
    (∀ r : ℕ, (r : ℤ) < D.h i μ →
      psiSameLCross (sy := sy) (hc := hc) t μ i ≫ psiDottedCap cs t μ i r = 0) ∧
    (∀ r s : ℕ, (r : ℤ) < D.h i μ → (s : ℤ) < D.h i μ →
      psiDiamondCup (sy := sy) (hc := hc) cs t μ i s ≫ psiDottedCap cs t μ i r =
        if r = s then 𝟙 _ else 0) :=
  ⟨psi_invP₁ cs t ht μ i hh, psi_invP₂ t ht μ i hh, psi_invP₃ cs t μ i,
    psi_invP₄ cs t ht μ i, psi_invP₅ cs t ht μ i⟩

/-- **Proposition 9.4, (1.14):** all five negative-weight inverse blocks for
ψ in the shifted super-opposite, including the empty matrix at weight zero. -/
theorem psiSameNegative_inversion (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i : I) (hh : D.h i μ ≤ 0) :
    (-(psiSameLCross (sy := sy) (hc := hc) t μ i ≫ psiSameSigma t μ i) +
      ∑ r ∈ range (-D.h i μ).toNat, psiDiamondCap cs t μ i r ≫ psiDottedCup cs t μ i r = 𝟙 _) ∧
    (psiSameSigma (Sc := Sc) (sy := sy) (hc := hc) t μ i ≫ psiSameLCross t μ i = -𝟙 _) ∧
    (∀ r, psiSameSigma (sy := sy) (hc := hc) t μ i ≫ psiDiamondCap cs t μ i r = 0) ∧
    (∀ r : ℕ, (r : ℤ) < -D.h i μ →
      psiDottedCup (sy := sy) (hc := hc) cs t μ i r ≫ psiSameLCross t μ i = 0) ∧
    (∀ r s : ℕ, (r : ℤ) < -D.h i μ → (s : ℤ) < -D.h i μ →
      psiDottedCup (sy := sy) (hc := hc) cs t μ i r ≫ psiDiamondCap cs t μ i s =
        if r = s then 𝟙 _ else 0) :=
  ⟨psi_invM₁ cs t ht μ i hh, psi_invM₂ t ht μ i hh, psi_invM₃ cs t μ i,
    psi_invM₄ cs t ht μ i, psi_invM₅ cs t ht μ i⟩

end OddMath.SKM
