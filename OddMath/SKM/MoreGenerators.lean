/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RelationsNF

/-!
# Leftward cups and caps (Brundan–Ellis, Definition 2.2)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 2.2
(TeX label `def3`), (2.10)–(2.14), and the scalars `c_{λ;i}` of (1.17).

The leftward crossing and the `♦`-cups and caps of (2.6)–(2.9) are generators of the
presentation (`OddMath.SKM.Basic`). Here:

* `CScalars Sc`: units `c_{λ;i}` with `c_{λ+αⱼ;i} = tᵢⱼ c_{λ;i}` (1.17);
* `etaP` (`η' : 1_λ → Eᵢ Fᵢ 1_λ`, (2.10)) and `epsP` (`ε' : Fᵢ Eᵢ 1_λ → 1_λ`, (2.11)), of parity
  `|i, λ| = |i|(⟨hᵢ, λ⟩ + 1)`;
* the identities (2.12)–(2.14), "immediate from these definitions": `eq_2_12_a`, `eq_2_12_b`,
  `eq_2_13_a`–`eq_2_13_c`, `eq_2_14_a`–`eq_2_14_c`.

In (2.13) (resp. (2.14)) the leftward cup (resp. cap) with no dots is `η'` (resp. `ε'`); the
paper's statements are for `0 ≤ n < ⟨hᵢ, λ⟩` (resp. `0 ≤ n < -⟨hᵢ, λ⟩`), so in particular
`⟨hᵢ, λ⟩ > 0` (resp. `< 0`) and `η'` (resp. `ε'`) is `c_{λ;i}` times the `♦`-cup with label
`⟨hᵢ, λ⟩ - 1` (resp. `c_{λ;i}⁻¹` times the `♦`-cap with label `-⟨hᵢ, λ⟩ - 1`).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]

/-- The units `c_{λ;i}` of (1.17), with `c_{λ+αⱼ;i} = tᵢⱼ c_{λ;i}`. -/
structure CScalars (Sc : Scalars D k) where
  /-- `c_{λ;i}`. -/
  c : X → I → kˣ
  shift : ∀ μ i j, c (μ + D.α j) i = Sc.t i j * c μ i

variable {Sc : Scalars D k} (cs : CScalars Sc)

/-- The parity `|i, λ| = |i|(⟨hᵢ, λ⟩ + 1)` (1.15). -/
def ipar (D : Datum I X) (i : I) (μ : X) : ZMod 2 := D.parity i * ((D.h i μ : ZMod 2) + 1)

/-- `η' : 1_λ → Eᵢ Fᵢ 1_λ` (2.10): `c_{λ;i}` times the `♦`-cup with label `⟨hᵢ, λ⟩ - 1` if
`⟨hᵢ, λ⟩ > 0`; `(-1)^{|i,λ|} c_{λ;i}` times the rightward cup with `-⟨hᵢ, λ⟩` dots on its
upward leg followed by the leftward crossing if `⟨hᵢ, λ⟩ ≤ 0`. -/
def etaP (i : I) (μ : X) : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [up i, dn i]) :=
  if 0 < D.h i μ then (cs.c μ i : k) • cl D Sc μ [] [up i, dn i] (dcupL i (D.h i μ - 1).toNat)
  else (zsign k (ipar D i μ) * (cs.c μ i : k)) •
    cl D Sc μ [] [up i, dn i] (etaL i (-D.h i μ).toNat ++ lcrossL i i)

/-- `ε' : Fᵢ Eᵢ 1_λ → 1_λ` (2.11): `c_{λ;i}⁻¹` times the `♦`-cap with label `-⟨hᵢ, λ⟩ - 1` if
`⟨hᵢ, λ⟩ < 0`; `-(-1)^{|i|⟨hᵢ,λ⟩} c_{λ;i}⁻¹` times the leftward crossing followed by the rightward
cap with `⟨hᵢ, λ⟩` dots on its upward leg if `⟨hᵢ, λ⟩ ≥ 0`. -/
def epsP (i : I) (μ : X) : (pres D Sc).obj (ob D μ [dn i, up i]) ⟶ (pres D Sc).obj (ob D μ []) :=
  if D.h i μ < 0 then (↑(cs.c μ i)⁻¹ : k) • cl D Sc μ [dn i, up i] [] (dcapL i (-D.h i μ - 1).toNat)
  else (-(zsign k (D.parity i * (D.h i μ : ZMod 2)) * (↑(cs.c μ i)⁻¹ : k))) •
    cl D Sc μ [dn i, up i] [] (lcrossL i i ++ epsL i (D.h i μ).toNat)

/-! ## (2.12) -/

theorem sChain_ss (i : I) : SChain [up i, dn i] (sigmaL i i ++ lcrossL i i) [up i, dn i] :=
  (sChain_sigmaL i i).append (sChain_lcrossL i i)

variable (Sc) in
/-- **(2.12), first identity**: `σ ≫ lcross = ∑_{n < ⟨hᵢ,λ⟩} (ε ∘ (xⁿ ⊗ 1)) ≫ ♦ₙ - 1` on
`Eᵢ Fᵢ 1_λ`, for every `λ` (the sum is empty if `⟨hᵢ, λ⟩ ≤ 0`). -/
theorem eq_2_12_a (i : I) (μ : X) :
    cl D Sc μ [up i, dn i] [up i, dn i] (sigmaL i i ++ lcrossL i i) =
      ∑ n ∈ Finset.range (D.h i μ).toNat,
        cl D Sc μ [up i, dn i] [up i, dn i] (epsL i n ++ dcupL i n) -
      cl D Sc μ [up i, dn i] [up i, dn i] [] := by
  rcases le_or_gt 0 (D.h i μ) with hh | hh
  · have := cl_invP₁ Sc i μ hh
    rw [← this]; abel
  · rw [cl_invM₂ Sc i μ hh.le, Int.toNat_of_nonpos hh.le, Finset.range_zero, Finset.sum_empty,
      zero_sub]

variable (Sc) in
/-- **(2.12), second identity**: `lcross ≫ σ = ∑_{n < -⟨hᵢ,λ⟩} ♣ₙ ≫ ((1 ⊗ xⁿ) ∘ η) - 1` on
`Fᵢ Eᵢ 1_λ`, for every `λ`. -/
theorem eq_2_12_b (i : I) (μ : X) :
    cl D Sc μ [dn i, up i] [dn i, up i] (lcrossL i i ++ sigmaL i i) =
      ∑ n ∈ Finset.range (-D.h i μ).toNat,
        cl D Sc μ [dn i, up i] [dn i, up i] (dcapL i n ++ etaL i n) -
      cl D Sc μ [dn i, up i] [dn i, up i] [] := by
  rcases le_or_gt (D.h i μ) 0 with hh | hh
  · have := cl_invM₁ Sc i μ hh
    rw [← this]; abel
  · rw [cl_invP₂ Sc i μ hh.le, Int.toNat_of_nonpos (by omega), Finset.range_zero,
      Finset.sum_empty, zero_sub]

/-! ## (2.13), (2.14) -/

theorem etaP_of_pos {i : I} {μ : X} (hh : 0 < D.h i μ) :
    etaP cs i μ = (cs.c μ i : k) • cl D Sc μ [] [up i, dn i] (dcupL i (D.h i μ - 1).toNat) :=
  ite_eq_left hh

theorem epsP_of_neg {i : I} {μ : X} (hh : D.h i μ < 0) :
    epsP cs i μ =
      (↑(cs.c μ i)⁻¹ : k) • cl D Sc μ [dn i, up i] [] (dcapL i (-D.h i μ - 1).toNat) :=
  ite_eq_left hh

/-- **(2.13), first identity**: `η' ≫ σ = 0` when `⟨hᵢ, λ⟩ > 0`. -/
theorem eq_2_13_a (i : I) (μ : X) (hh : 0 < D.h i μ) :
    etaP cs i μ ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) = 0 := by
  rw [etaP_of_pos cs hh, Linear.smul_comp, cl_comp (sChain_dcupL i _) (sChain_sigmaL i i),
    cl_invP₄ Sc i μ _ (by omega), smul_zero]

/-- **(2.13), second identity**: `lcross ≫ (ε ∘ (xⁿ ⊗ 1)) = 0` for `0 ≤ n < ⟨hᵢ, λ⟩`. -/
theorem eq_2_13_b (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < D.h i μ) :
    cl D Sc μ [dn i, up i] [] (lcrossL i i ++ epsL i n) = 0 :=
  cl_invP₃ Sc i μ n hn

/-- **(2.13), third identity**: the counterclockwise bubble `η' ≫ (ε ∘ (xⁿ ⊗ 1))` is
`δ_{n,⟨hᵢ,λ⟩-1} c_{λ;i}` for `0 ≤ n < ⟨hᵢ, λ⟩`. -/
theorem eq_2_13_c (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < D.h i μ) :
    etaP cs i μ ≫ cl D Sc μ [up i, dn i] [] (epsL i n) =
      if (n : ℤ) = D.h i μ - 1 then (cs.c μ i : k) • 𝟙 _ else 0 := by
  have hh : 0 < D.h i μ := by omega
  rw [etaP_of_pos cs hh, Linear.smul_comp, cl_comp (sChain_dcupL i _) (sChain_epsL i n),
    cl_invP₅ Sc i μ n _ hn (by omega), cl_nil]
  by_cases hnh : (n : ℤ) = D.h i μ - 1
  · rw [ite_eq_left (by omega), ite_eq_left hnh]
  · rw [ite_eq_right (by omega), ite_eq_right hnh, smul_zero]

/-- **(2.14), first identity**: `σ ≫ ε' = 0` when `⟨hᵢ, λ⟩ < 0`. -/
theorem eq_2_14_a (i : I) (μ : X) (hh : D.h i μ < 0) :
    cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫ epsP cs i μ = 0 := by
  rw [epsP_of_neg cs hh, Linear.comp_smul, cl_comp (sChain_sigmaL i i) (sChain_dcapL i _),
    cl_invM₄ Sc i μ _ (by omega), smul_zero]

/-- **(2.14), second identity**: `((1 ⊗ xⁿ) ∘ η) ≫ lcross = 0` for `0 ≤ n < -⟨hᵢ, λ⟩`. -/
theorem eq_2_14_b (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < -D.h i μ) :
    cl D Sc μ [] [up i, dn i] (etaL i n ++ lcrossL i i) = 0 :=
  cl_invM₃ Sc i μ n hn

/-- **(2.14), third identity**: the clockwise bubble `((1 ⊗ xⁿ) ∘ η) ≫ ε'` is
`δ_{n,-⟨hᵢ,λ⟩-1} c_{λ;i}⁻¹` for `0 ≤ n < -⟨hᵢ, λ⟩`. -/
theorem eq_2_14_c (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < -D.h i μ) :
    cl D Sc μ [] [dn i, up i] (etaL i n) ≫ epsP cs i μ =
      if (n : ℤ) = -D.h i μ - 1 then (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ else 0 := by
  have hh : D.h i μ < 0 := by omega
  rw [epsP_of_neg cs hh, Linear.comp_smul, cl_comp (sChain_etaL i n) (sChain_dcapL i _),
    cl_invM₅ Sc i μ n _ hn (by omega), cl_nil]
  by_cases hnh : (n : ℤ) = -D.h i μ - 1
  · rw [ite_eq_left (by omega), ite_eq_left hnh]
  · rw [ite_eq_right (by omega), ite_eq_right hnh, smul_zero]

end OddMath.SKM
