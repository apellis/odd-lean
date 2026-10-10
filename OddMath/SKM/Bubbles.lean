/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.MoreGenerators

/-!
# Dotted bubbles and the odd bubble (Brundan–Ellis, Definition 2.3)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 2.3
(TeX label `def4`), (2.15)–(2.18).

On `1_λ` (weight `λ = μ`, `h = ⟨hᵢ, λ⟩`):

* `bubL i μ n`: the bubble whose upward side is on the **left** (the leftward cup `η'` followed
  by the rightward cap `ε` with `n` dots on its upward leg) for `n ≥ 0`, and the
  negatively dotted bubbles of (2.15) for `n < 0`;
* `bubR i μ n`: the bubble whose upward side is on the **right** (the rightward cup `η` with `n`
  dots on its upward leg followed by the leftward cap `ε'`) for `n ≥ 0`, and (2.16) for `n < 0`;
* `bubLs`, `bubRs`: the shorthand (2.17), `n + * = n + h - 1` (resp. `n - h - 1`);
* `oddBubble i μ`: the odd bubble (2.18), `c_{λ;i}⁻¹ bubL(h)` if `h ≥ 0` and `c_{λ;i} bubR(-h)` if
  `h ≤ 0`; `oddBubble_consistent`: the two definitions agree at `h = 0` (the calculation after
  (2.18)), using that `i` is odd.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- The bubble with its upward side on the left and `n` dots there, (2.13) for `n ≥ 0` and (2.15)
for `n < 0`. -/
def bubL (i : I) (μ : X) (n : ℤ) : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ []) :=
  if 0 ≤ n then etaP cs i μ ≫ cl D Sc μ [up i, dn i] [] (epsL i n.toNat)
  else if D.h i μ - 1 < n then
    (-(zsign k (D.parity i * ((n + D.h i μ + 1 : ℤ) : ZMod 2))) * (cs.c μ i : k)) •
      cl D Sc μ [] [] (etaL i (-D.h i μ).toNat ++ dcapL i (-n - 1).toNat)
  else if n = D.h i μ - 1 then (cs.c μ i : k) • 𝟙 _ else 0

/-- The bubble with its upward side on the right and `n` dots there, (2.14) for `n ≥ 0` and
(2.16) for `n < 0`. -/
def bubR (i : I) (μ : X) (n : ℤ) : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ []) :=
  if 0 ≤ n then cl D Sc μ [] [dn i, up i] (etaL i n.toNat) ≫ epsP cs i μ
  else if -D.h i μ - 1 < n then
    (-(zsign k (D.parity i * ((n + D.h i μ + 1 : ℤ) : ZMod 2))) * (↑(cs.c μ i)⁻¹ : k)) •
      cl D Sc μ [] [] (dcupL i (-n - 1).toNat ++ epsL i (D.h i μ).toNat)
  else if n = -D.h i μ - 1 then (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ else 0

/-- The shorthand (2.17): `n + *` dots on the left bubble means `n + ⟨hᵢ, λ⟩ - 1` dots. -/
def bubLs (i : I) (μ : X) (n : ℤ) : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ []) :=
  bubL cs i μ (n + D.h i μ - 1)

/-- The shorthand (2.17): `n + *` dots on the right bubble means `n - ⟨hᵢ, λ⟩ - 1` dots. -/
def bubRs (i : I) (μ : X) (n : ℤ) : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ []) :=
  bubR cs i μ (n - D.h i μ - 1)

/-- The odd bubble (2.18) (meaningful for odd `i`). -/
def oddBubble (i : I) (μ : X) : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ []) :=
  if 0 ≤ D.h i μ then (↑(cs.c μ i)⁻¹ : k) • bubL cs i μ (D.h i μ)
  else (cs.c μ i : k) • bubR cs i μ (-D.h i μ)

/-- **The calculation after (2.18)**: for odd `i` and `⟨hᵢ, λ⟩ = 0`, the two expressions defining
the odd bubble agree: `c_{λ;i}⁻¹ bubL(0) = c_{λ;i} bubR(0)`. -/
theorem oddBubble_consistent (i : I) (μ : X) (hi : D.parity i = 1) (hh : D.h i μ = 0) :
    (↑(cs.c μ i)⁻¹ : k) • bubL cs i μ 0 = (cs.c μ i : k) • bubR cs i μ 0 := by
  simp only [bubL, bubR, le_refl, ite_true, Int.toNat_zero, etaP, epsP, hh, lt_irrefl, ite_false,
    neg_zero, Linear.smul_comp, Linear.comp_smul, smul_smul]
  rw [cl_comp (sChain_etaL i 0 |>.append (sChain_lcrossL i i)) (sChain_epsL i 0),
    cl_comp (sChain_etaL i 0) ((sChain_lcrossL i i).append (sChain_epsL i 0)), List.append_assoc]
  congr 1
  simp only [ipar, hh, hi, Int.cast_zero, zero_add, mul_one, mul_zero, zsign, ite_true,
    zero_ne_one, ite_false]
  ring

end OddMath.SKM
