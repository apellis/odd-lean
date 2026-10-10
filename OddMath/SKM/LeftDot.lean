/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Bubbles
import OddMath.SKM.Lemma31Rot
import OddMath.SKM.MateBlock

/-!
# Leftward dot slides (Brundan–Ellis, Proposition 4.1)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 4.1
(TeX label `leftdot`), relations (4.1) (`leftcross1`), (4.2) (`leftcross2`), (4.3) (`leftclub`).

Here, for `i = j` and `n = 1`:

* (4.1) with `⟨hᵢ, λ⟩ ≥ 0` (`lemma41_eq1_one`): on `Fᵢ Eᵢ 1_λ`, a downward dot followed by the
  leftward crossing, minus `(-1)^{|i|}` times the leftward crossing followed by a downward dot,
  is `ε' ≫ η'`;
* (4.2) with `⟨hᵢ, λ⟩ ≥ 0` (`lemma41_eq2_one`): the same for upward dots, with
  `(-1)^{|i|⟨hᵢ,λ⟩}`;
* (4.3) for all `λ` (`lemma41_eq3_one_even`, `lemma41_eq3_one_odd`): an upward dot on the
  leftward cap `ε'` equals a downward dot on its other leg if `i` is even, and `(-1)^{⟨hᵢ,λ⟩}`
  times it plus twice `ε'` followed by the odd bubble if `i` is odd.

The proofs follow the paper: (4.1), (4.2) are (3.3), (3.4) composed on both sides with the
leftward crossing, simplified with (2.12)–(2.13); (4.3) for `⟨hᵢ, λ⟩ ≥ 0` is computed from (4.1),
(4.2) and the definitions (2.11), (2.18), and for `⟨hᵢ, λ⟩ < 0` it is checked on the components
of the isomorphism (1.14).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## The 2-morphisms involved -/

section Named

variable (D Sc)

/-- The leftward crossing `Fᵢ Eᵢ 1_μ → Eᵢ Fᵢ 1_μ`. -/
abbrev lcM (i : I) (μ : X) := cl D Sc μ [dn i, up i] [up i, dn i] (lcrossL i i)
/-- The crossing `σ : Eᵢ Fᵢ 1_μ → Fᵢ Eᵢ 1_μ`. -/
abbrev sgM (i : I) (μ : X) := cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i)
/-- A downward dot on the left strand of `Fᵢ Eᵢ`. -/
abbrev dLM (i : I) (μ : X) := cl D Sc μ [dn i, up i] [dn i, up i] ((ddotL i).map (whL [] [up i]))
/-- A downward dot on the right strand of `Eᵢ Fᵢ`. -/
abbrev dRM (i : I) (μ : X) := cl D Sc μ [up i, dn i] [up i, dn i] ((ddotL i).map (whL [up i] []))
/-- An upward dot on the right strand of `Fᵢ Eᵢ`. -/
abbrev uRM (i : I) (μ : X) := cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] 1)
/-- An upward dot on the left strand of `Eᵢ Fᵢ`. -/
abbrev uLM (i : I) (μ : X) := cl D Sc μ [up i, dn i] [up i, dn i] (dotsL [] i [dn i] 1)
/-- The rightward cap with `n` dots, `ε ∘ (xⁿ ⊗ 1)`. -/
abbrev eLM (i : I) (μ : X) (n : ℕ) := cl D Sc μ [up i, dn i] [] (epsL i n)
/-- The rightward cup with `n` dots, `(1 ⊗ xⁿ) ∘ η`. -/
abbrev hLM (i : I) (μ : X) (n : ℕ) := cl D Sc μ [] [dn i, up i] (etaL i n)
/-- The `♦`-cup with label `n`. -/
abbrev dcM (i : I) (μ : X) (n : ℕ) := cl D Sc μ [] [up i, dn i] (dcupL i n)

end Named

theorem lc_sg (i : I) (μ : X) (hh : 0 ≤ D.h i μ) : lcM D Sc i μ ≫ sgM D Sc i μ = -𝟙 _ := by
  rw [cl_comp (sChain_lcrossL i i) (sChain_sigmaL i i), cl_invP₂ Sc i μ hh, cl_nil]

theorem sg_lc (i : I) (μ : X) :
    sgM D Sc i μ ≫ lcM D Sc i μ =
      ∑ n ∈ Finset.range (D.h i μ).toNat, eLM D Sc i μ n ≫ dcM D Sc i μ n - 𝟙 _ := by
  rw [cl_comp (sChain_sigmaL i i) (sChain_lcrossL i i), eq_2_12_a, cl_nil]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [cl_comp (sChain_epsL i n) (sChain_dcupL i n)]

theorem lc_eL (i : I) (μ : X) (m : ℕ) (hm : (m : ℤ) < D.h i μ) :
    lcM D Sc i μ ≫ eLM D Sc i μ m = 0 := by
  rw [cl_comp (sChain_lcrossL i i) (sChain_epsL i m)]
  exact cl_invP₃ Sc i μ m hm

theorem sChain_ddotR (i : I) : SChain [up i, dn i] ((ddotL i).map (whL [up i] [])) [up i, dn i] :=
  (sChain_ddotL i).wh [up i] [] rfl rfl

theorem sChain_ddotL' (i : I) : SChain [dn i, up i] ((ddotL i).map (whL [] [up i])) [dn i, up i] :=
  (sChain_ddotL i).wh [] [up i] rfl rfl

theorem sChain_uR (i : I) (n : ℕ) : SChain [dn i, up i] (dotsL [dn i] i [] n) [dn i, up i] :=
  sChain_dotsL [dn i] i [] n

theorem sChain_uL (i : I) (n : ℕ) : SChain [up i, dn i] (dotsL [] i [dn i] n) [up i, dn i] :=
  sChain_dotsL [] i [dn i] n

theorem ddotsL_one (i : I) : ddotsL i 1 = ddotL i := by simp [ddotsL]

/-- (3.4) for `n = 1` in morphism form. -/
theorem sg_dL (i : I) (μ : X) :
    zsign k (D.parity i) • (sgM D Sc i μ ≫ dLM D Sc i μ) - dRM D Sc i μ ≫ sgM D Sc i μ =
      eLM D Sc i μ 0 ≫ hLM D Sc i μ 0 := by
  have h := lemma31_eq4_eq Sc i μ 1
  simp only [ddotsL_one, Nat.cast_one, mul_one, zmod2_mul_self, Finset.range_one,
    Finset.sum_singleton, Nat.cast_zero, mul_zero, zsign_zero, one_smul, Nat.sub_self] at h
  rw [cl_comp (sChain_sigmaL i i) (sChain_ddotL' i), cl_comp (sChain_ddotR i) (sChain_sigmaL i i),
    h, cl_comp (sChain_epsL i 0) (sChain_etaL i 0)]
  simp [ddotsL, epsL, etaL, dotsL]

/-- (3.3) for `n = 1` in morphism form. -/
theorem sg_uR (i : I) (μ : X) :
    sgM D Sc i μ ≫ uRM D Sc i μ - zsign k (D.parity i) • (uLM D Sc i μ ≫ sgM D Sc i μ) =
      eLM D Sc i μ 0 ≫ hLM D Sc i μ 0 := by
  have h := lemma31_eq3_eq Sc i μ 1
  simp only [Nat.cast_one, mul_one, zmod2_mul_self, Finset.range_one, Finset.sum_singleton,
    Nat.cast_zero, mul_zero, zsign_zero, one_smul, Nat.sub_self] at h
  rw [cl_comp (sChain_sigmaL i i) (sChain_uR i 1),
    cl_comp (sChain_uL i 1) (sChain_sigmaL i i), h,
    cl_comp (sChain_epsL i 0) (sChain_etaL i 0)]
  simp [epsL, etaL, dotsL]

/-- An upward dot on the cap with `n` dots. -/
theorem uL_eL (i : I) (μ : X) (n : ℕ) :
    uLM D Sc i μ ≫ eLM D Sc i μ n = eLM D Sc i μ (n + 1) := by
  rw [cl_comp (sChain_uL i 1) (sChain_epsL i n)]
  congr 1

/-- A downward dot on the cap with `n` dots: `(-1)^{|i|n}` times the cap with `n + 1` dots. -/
theorem dR_eL (i : I) (μ : X) (n : ℕ) :
    dRM D Sc i μ ≫ eLM D Sc i μ n = zsign k (D.parity i * n) • eLM D Sc i μ (n + 1) := by
  rw [cl_comp (sChain_ddotR i) (sChain_epsL i n)]
  have hp : parsum D (ddotL i) = D.parity i := by
    rw [← ddotsL_one, parsum_ddotsL, Nat.cast_one, one_mul]
  -- the downward dot moves above the `n` upward dots
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := [up i, dn i]) (T := [])
    [] [([], Shape.cap i, [])] (s := [up i]) (s' := [up i]) (t := [dn i]) (t' := [dn i])
    (sChain_dotsL [] i [] n) (sChain_ddotL i)
  rw [parsum_dotsL, hp] at E
  have E' : cl D Sc μ [up i, dn i] [] ((ddotL i).map (whL [up i] []) ++ epsL i n) =
      zsign k (n * D.parity i * D.parity i) •
        cl D Sc μ [up i, dn i] [] ((dotsL [] i [dn i] n) ++
          ((ddotL i).map (whL [up i] []) ++ [([], Shape.cap i, [])])) := by
    have := congrArg (zsign k (n * D.parity i * D.parity i) • ·) E
    simp only [smul_smul, zsign_mul_self, one_smul] at this
    convert this.symm using 2 <;> simp [epsL, dotsL, whL]
  -- the downward dot on the cap is an upward dot on its other leg
  have hcap := cl_cap_slide Sc i μ (sChain_dotsL [] i [] 1)
  have hX : SChain [up i, dn i] ((ddotL i).map (whL [up i] []) ++ [([], Shape.cap i, [])]) [] :=
    (sChain_ddotR i).append (show SChain [up i, dn i] [([], Shape.cap i, [])] [] from ⟨rfl, rfl⟩)
  rw [E', ← cl_comp (sChain_uL i n) hX]
  rw [show (ddotL i).map (whL [up i] []) ++ [([], Shape.cap i, [])] =
    (mateL i (dotsL [] i [] 1)).map (whL [up i] []) ++ [([], Shape.cap i, [])] from rfl, ← hcap,
    cl_comp (sChain_uL i n) (((sChain_dotsL [] i [] 1).wh [] [dn i] rfl rfl).append
      (show SChain [up i, dn i] [([], Shape.cap i, [])] [] from ⟨rfl, rfl⟩)), mul_assoc, zmod2_mul_self, mul_comm]
  congr 1
  simp [eLM, epsL, dotsL, whL, List.replicate_succ']

theorem lc_sg_assoc (i : I) (μ : X) (hh : 0 ≤ D.h i μ) {Z : (pres D Sc).Presented}
    (f : (pres D Sc).obj (ob D μ [dn i, up i]) ⟶ Z) :
    lcM D Sc i μ ≫ sgM D Sc i μ ≫ f = -f := by
  rw [← Category.assoc, lc_sg i μ hh, Preadditive.neg_comp, Category.id_comp]

/-- The sum `∑_{n < h} lc ≫ (dot) ≫ (cap with n dots) ≫ ♦ₙ` reduces to its last term. -/
theorem sum_lc_eL_dc (i : I) (μ : X) (f : ℕ → k) :
    ∑ n ∈ Finset.range (D.h i μ).toNat,
        f n • (lcM D Sc i μ ≫ eLM D Sc i μ (n + 1) ≫ dcM D Sc i μ n) =
      if (D.h i μ).toNat = 0 then 0 else
        f ((D.h i μ).toNat - 1) •
          (lcM D Sc i μ ≫ eLM D Sc i μ (D.h i μ).toNat ≫ dcM D Sc i μ ((D.h i μ).toNat - 1)) := by
  split_ifs with hN
  · rw [hN, Finset.range_zero, Finset.sum_empty]
  · rw [Finset.sum_eq_single ((D.h i μ).toNat - 1)]
    · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN)]
    · intro n hn hne
      rw [Finset.mem_range] at hn
      rw [← Category.assoc, lc_eL i μ (n + 1) (by omega), Limits.zero_comp, smul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem zsign_toNat (i : I) (μ : X) (hh : 0 ≤ D.h i μ) (a : ZMod 2) :
    ((D.h i μ).toNat : ZMod 2) * a = (D.h i μ : ZMod 2) * a := by
  congr 1
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hh]

variable (Sc) in
/-- **Brundan–Ellis, Proposition 4.1 (4.1), `i = j`, `n = 1`, `⟨hᵢ, λ⟩ ≥ 0`.** -/
theorem lemma41_eq1_one (i : I) (μ : X) (hh : 0 ≤ D.h i μ) :
    dLM D Sc i μ ≫ lcM D Sc i μ - zsign k (D.parity i) • (lcM D Sc i μ ≫ dRM D Sc i μ) =
      epsP cs i μ ≫ etaP cs i μ := by
  have A := congrArg (fun x => lcM D Sc i μ ≫ x ≫ lcM D Sc i μ) (sg_dL (Sc := Sc) i μ)
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul,
    Category.assoc, lc_sg_assoc i μ hh, sg_lc, Preadditive.comp_sum, Preadditive.comp_sub,
    Category.comp_id] at A
  simp only [← Category.assoc (dRM D Sc i μ), dR_eL, Linear.smul_comp, Linear.comp_smul] at A
  rw [sum_lc_eL_dc] at A
  -- `A : -(z • (dL ≫ lc)) - (S - lc ≫ dR) = lc ≫ e₀ ≫ h₀ ≫ lc`
  have hz := zsign_mul_self (k := k) (D.parity i)
  have key : dLM D Sc i μ ≫ lcM D Sc i μ - zsign k (D.parity i) • (lcM D Sc i μ ≫ dRM D Sc i μ) =
      -(zsign k (D.parity i) • (lcM D Sc i μ ≫ eLM D Sc i μ 0 ≫ hLM D Sc i μ 0 ≫ lcM D Sc i μ +
        if (D.h i μ).toNat = 0 then 0 else
          zsign k (D.parity i * ((D.h i μ).toNat - 1 : ℕ)) •
            (lcM D Sc i μ ≫ eLM D Sc i μ (D.h i μ).toNat ≫
              dcM D Sc i μ ((D.h i μ).toNat - 1)))) := by
    have h1 : (zsign k (D.parity i) * zsign k (D.parity i)) • (dLM D Sc i μ ≫ lcM D Sc i μ) =
        dLM D Sc i μ ≫ lcM D Sc i μ := by rw [hz, one_smul]
    linear_combination (norm := module) (-(zsign k (D.parity i))) • A - h1
  rw [key]
  have hc : (↑(cs.c μ i)⁻¹ : k) * (cs.c μ i : k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have eps_eq : ∀ n, cl D Sc μ [dn i, up i] [] (lcrossL i i ++ epsL i n) =
      lcM D Sc i μ ≫ eLM D Sc i μ n := fun n =>
    (cl_comp (sChain_lcrossL i i) (sChain_epsL i n)).symm
  rcases eq_or_lt_of_le hh with h0 | hpos
  · -- `⟨hᵢ, λ⟩ = 0`
    have h0' : D.h i μ = 0 := h0.symm
    have eta_eq : cl D Sc μ [] [up i, dn i] (etaL i 0 ++ lcrossL i i) =
        hLM D Sc i μ 0 ≫ lcM D Sc i μ := (cl_comp (sChain_etaL i 0) (sChain_lcrossL i i)).symm
    simp only [epsP, etaP, h0', lt_irrefl, Int.toNat_zero, neg_zero, ↓reduceIte,
      add_zero, eps_eq, eta_eq, Linear.smul_comp, Linear.comp_smul, smul_smul, Category.assoc,
      ipar, Int.cast_zero, mul_zero, zsign_zero, zero_add, mul_one]
    rw [← neg_smul]
    congr 1
    linear_combination (zsign k (D.parity i)) * hc
  · -- `⟨hᵢ, λ⟩ > 0`
    have hN : (D.h i μ).toNat ≠ 0 := by omega
    have hlt : ¬ D.h i μ < 0 := by omega
    have z0 : lcM D Sc i μ ≫ eLM D Sc i μ 0 ≫ hLM D Sc i μ 0 ≫ lcM D Sc i μ = 0 := by
      rw [← Category.assoc, lc_eL i μ 0 (by exact_mod_cast hpos), Limits.zero_comp]
    simp only [hN, ↓reduceIte, z0, zero_add, epsP, hlt, etaP_of_pos cs hpos, eps_eq,
      Linear.smul_comp, Linear.comp_smul, smul_smul, Category.assoc,
      show (D.h i μ - 1).toNat = (D.h i μ).toNat - 1 by omega]
    rw [← neg_smul]
    congr 1
    have e : zsign k (D.parity i) * zsign k (D.parity i * ((D.h i μ).toNat - 1 : ℕ)) =
        zsign k (D.parity i * (D.h i μ : ZMod 2)) := by
      rw [← zsign_add]
      congr 1
      have hc' : ((D.h i μ : ℤ) : ZMod 2) = ((D.h i μ).toNat : ZMod 2) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hh]
      rw [hc', Nat.cast_sub (by omega)]
      ring
    linear_combination (-1 : k) * e + (zsign k (D.parity i * (D.h i μ : ZMod 2))) * hc

theorem cinv_mul_c (i : I) (μ : X) : (↑(cs.c μ i)⁻¹ : k) * (cs.c μ i : k) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem epsP_etaP_zero (i : I) (μ : X) (h0 : D.h i μ = 0) :
    epsP cs i μ ≫ etaP cs i μ = -(zsign k (D.parity i) •
      (lcM D Sc i μ ≫ eLM D Sc i μ 0 ≫ hLM D Sc i μ 0 ≫ lcM D Sc i μ)) := by
  have eps_eq : cl D Sc μ [dn i, up i] [] (lcrossL i i ++ epsL i 0) =
      lcM D Sc i μ ≫ eLM D Sc i μ 0 := (cl_comp (sChain_lcrossL i i) (sChain_epsL i 0)).symm
  have eta_eq : cl D Sc μ [] [up i, dn i] (etaL i 0 ++ lcrossL i i) =
      hLM D Sc i μ 0 ≫ lcM D Sc i μ := (cl_comp (sChain_etaL i 0) (sChain_lcrossL i i)).symm
  simp only [epsP, etaP, h0, lt_irrefl, Int.toNat_zero, neg_zero, ↓reduceIte,
    eps_eq, eta_eq, Linear.smul_comp, Linear.comp_smul, smul_smul, Category.assoc,
    ipar, Int.cast_zero, mul_zero, zsign_zero, zero_add, mul_one]
  rw [← neg_smul]
  congr 1
  linear_combination (-zsign k (D.parity i)) * cinv_mul_c cs i μ

theorem epsP_etaP_pos (i : I) (μ : X) (hpos : 0 < D.h i μ) :
    epsP cs i μ ≫ etaP cs i μ = -(zsign k (D.parity i * (D.h i μ : ZMod 2)) •
      (lcM D Sc i μ ≫ eLM D Sc i μ (D.h i μ).toNat ≫ dcM D Sc i μ ((D.h i μ).toNat - 1))) := by
  have hlt : ¬ D.h i μ < 0 := by omega
  have eps_eq : cl D Sc μ [dn i, up i] [] (lcrossL i i ++ epsL i (D.h i μ).toNat) =
      lcM D Sc i μ ≫ eLM D Sc i μ (D.h i μ).toNat :=
    (cl_comp (sChain_lcrossL i i) (sChain_epsL i _)).symm
  simp only [epsP, hlt, ↓reduceIte, etaP_of_pos cs hpos, eps_eq, Linear.smul_comp,
    Linear.comp_smul, smul_smul, Category.assoc,
    show (D.h i μ - 1).toNat = (D.h i μ).toNat - 1 by omega]
  rw [← neg_smul]
  congr 1
  linear_combination (-zsign k (D.parity i * (D.h i μ : ZMod 2))) * cinv_mul_c cs i μ

variable (Sc) in
/-- **Brundan–Ellis, Proposition 4.1 (4.2), `i = j`, `n = 1`, `⟨hᵢ, λ⟩ ≥ 0`.** -/
theorem lemma41_eq2_one (i : I) (μ : X) (hh : 0 ≤ D.h i μ) :
    zsign k (D.parity i) • (uRM D Sc i μ ≫ lcM D Sc i μ) - lcM D Sc i μ ≫ uLM D Sc i μ =
      zsign k (D.parity i * (D.h i μ : ZMod 2)) • (epsP cs i μ ≫ etaP cs i μ) := by
  have A := congrArg (fun x => lcM D Sc i μ ≫ x ≫ lcM D Sc i μ) (sg_uR (Sc := Sc) i μ)
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul,
    Category.assoc, lc_sg_assoc i μ hh, sg_lc, Preadditive.comp_sum, Category.comp_id] at A
  simp only [← Category.assoc (uLM D Sc i μ), uL_eL] at A
  have hs := sum_lc_eL_dc (Sc := Sc) i μ (fun _ => 1)
  simp only [one_smul] at hs
  rw [hs] at A
  have hz := zsign_mul_self (k := k) (D.parity i)
  set S := (if (D.h i μ).toNat = 0 then 0 else
    lcM D Sc i μ ≫ eLM D Sc i μ (D.h i μ).toNat ≫ dcM D Sc i μ ((D.h i μ).toNat - 1)) with hS
  have h1 : (zsign k (D.parity i) * zsign k (D.parity i)) • S = S := by rw [hz, one_smul]
  have h2 : (zsign k (D.parity i) * zsign k (D.parity i)) • (lcM D Sc i μ ≫ uLM D Sc i μ) =
      lcM D Sc i μ ≫ uLM D Sc i μ := by rw [hz, one_smul]
  have key : zsign k (D.parity i) • (uRM D Sc i μ ≫ lcM D Sc i μ) - lcM D Sc i μ ≫ uLM D Sc i μ =
      -(zsign k (D.parity i) • (lcM D Sc i μ ≫ eLM D Sc i μ 0 ≫ hLM D Sc i μ 0 ≫ lcM D Sc i μ) +
        S) := by
    linear_combination (norm := module) (-(zsign k (D.parity i))) • A - h1 + h2
  rw [key]
  rcases eq_or_lt_of_le hh with h0 | hpos
  · have hN : (D.h i μ).toNat = 0 := by omega
    simp only [hS, hN, ↓reduceIte, add_zero]
    rw [epsP_etaP_zero cs i μ h0.symm, ← h0, Int.cast_zero, mul_zero, zsign_zero, one_smul]
  · have hN : (D.h i μ).toNat ≠ 0 := by omega
    have z0 : lcM D Sc i μ ≫ eLM D Sc i μ 0 ≫ hLM D Sc i μ 0 ≫ lcM D Sc i μ = 0 := by
      rw [← Category.assoc, lc_eL i μ 0 (by exact_mod_cast hpos), Limits.zero_comp]
    simp only [hS, hN, ↓reduceIte, z0, smul_zero, zero_add]
    rw [epsP_etaP_pos cs i μ hpos, smul_neg, smul_smul, zsign_mul_self, one_smul]

/-! ## (4.3) for `n = 1` -/

theorem eps_eqN (i : I) (μ : X) (n : ℕ) :
    cl D Sc μ [dn i, up i] [] (lcrossL i i ++ epsL i n) = lcM D Sc i μ ≫ eLM D Sc i μ n :=
  (cl_comp (sChain_lcrossL i i) (sChain_epsL i n)).symm

theorem epsP_of_nonneg (i : I) (μ : X) (hh : 0 ≤ D.h i μ) :
    epsP cs i μ = (-(zsign k (D.parity i * (D.h i μ : ZMod 2)) * (↑(cs.c μ i)⁻¹ : k))) •
      (lcM D Sc i μ ≫ eLM D Sc i μ (D.h i μ).toNat) := by
  rw [epsP, ite_eq_right (show ¬ D.h i μ < 0 by omega), eps_eqN]

theorem etaP_eL (i : I) (μ : X) (hh : 0 ≤ D.h i μ) :
    etaP cs i μ ≫ eLM D Sc i μ (D.h i μ).toNat = bubL cs i μ (D.h i μ) := by
  rw [bubL, ite_eq_left hh]

/-- (4.3) for `n = 1`, `⟨hᵢ, λ⟩ ≥ 0`, both sides expressed through `ε' ≫ bubL(h)`. -/
theorem uR_epsP_nonneg (i : I) (μ : X) (hh : 0 ≤ D.h i μ) :
    uRM D Sc i μ ≫ epsP cs i μ =
      (-(zsign k (D.parity i * (D.h i μ : ZMod 2)) * (↑(cs.c μ i)⁻¹ : k))) •
        (zsign k (D.parity i) • (lcM D Sc i μ ≫ eLM D Sc i μ ((D.h i μ).toNat + 1)) +
          (zsign k (D.parity i) * zsign k (D.parity i * (D.h i μ : ZMod 2))) •
            (epsP cs i μ ≫ bubL cs i μ (D.h i μ))) := by
  have E := lemma41_eq2_one Sc cs i μ hh
  have hz := zsign_mul_self (k := k) (D.parity i)
  have E' : uRM D Sc i μ ≫ lcM D Sc i μ = zsign k (D.parity i) • (lcM D Sc i μ ≫ uLM D Sc i μ) +
      (zsign k (D.parity i) * zsign k (D.parity i * (D.h i μ : ZMod 2))) •
        (epsP cs i μ ≫ etaP cs i μ) := by
    have h1 : (zsign k (D.parity i) * zsign k (D.parity i)) • (uRM D Sc i μ ≫ lcM D Sc i μ) =
        uRM D Sc i μ ≫ lcM D Sc i μ := by rw [hz, one_smul]
    linear_combination (norm := module) zsign k (D.parity i) • E - h1
  conv_lhs => rw [epsP_of_nonneg cs i μ hh, Linear.comp_smul, ← Category.assoc, E',
    Preadditive.add_comp, Linear.smul_comp, Linear.smul_comp, Category.assoc, uL_eL, Category.assoc,
    etaP_eL cs i μ hh]

/-- (4.3) for `n = 1`, `⟨hᵢ, λ⟩ ≥ 0`: the downward dot. -/
theorem dL_epsP_nonneg (i : I) (μ : X) (hh : 0 ≤ D.h i μ) :
    dLM D Sc i μ ≫ epsP cs i μ =
      (-(zsign k (D.parity i * (D.h i μ : ZMod 2)) * (↑(cs.c μ i)⁻¹ : k))) •
        ((zsign k (D.parity i) * zsign k (D.parity i * ((D.h i μ).toNat : ZMod 2))) •
            (lcM D Sc i μ ≫ eLM D Sc i μ ((D.h i μ).toNat + 1)) +
          epsP cs i μ ≫ bubL cs i μ (D.h i μ)) := by
  have E := lemma41_eq1_one Sc cs i μ hh
  have E' : dLM D Sc i μ ≫ lcM D Sc i μ = zsign k (D.parity i) • (lcM D Sc i μ ≫ dRM D Sc i μ) +
      epsP cs i μ ≫ etaP cs i μ := by
    linear_combination (norm := module) E
  conv_lhs => rw [epsP_of_nonneg cs i μ hh, Linear.comp_smul, ← Category.assoc, E',
    Preadditive.add_comp, Linear.smul_comp, Category.assoc, Category.assoc, dR_eL, Linear.comp_smul,
    smul_smul, etaP_eL cs i μ hh]

theorem zsign_cases (p : ZMod 2) : zsign k p = 1 ∨ zsign k p = -1 := by
  unfold zsign; split_ifs <;> simp

theorem oddBubble_of_nonneg (i : I) (μ : X) (hh : 0 ≤ D.h i μ) :
    oddBubble cs i μ = (↑(cs.c μ i)⁻¹ : k) • bubL cs i μ (D.h i μ) := by
  rw [oddBubble, ite_eq_left hh]

/-- (4.3), `n = 1`, `⟨hᵢ, λ⟩ ≥ 0`, `i` even. -/
theorem lemma41_eq3_one_even_nonneg (i : I) (μ : X) (hi : D.parity i = 0) (hh : 0 ≤ D.h i μ) :
    uRM D Sc i μ ≫ epsP cs i μ = dLM D Sc i μ ≫ epsP cs i μ := by
  rw [uR_epsP_nonneg cs i μ hh, dL_epsP_nonneg cs i μ hh]
  simp only [hi, zero_mul, zsign_zero, mul_one, one_smul]

/-- (4.3), `n = 1`, `⟨hᵢ, λ⟩ ≥ 0`, `i` odd. -/
theorem lemma41_eq3_one_odd_nonneg (i : I) (μ : X) (hi : D.parity i = 1) (hh : 0 ≤ D.h i μ) :
    uRM D Sc i μ ≫ epsP cs i μ =
      zsign k (D.h i μ : ZMod 2) • (dLM D Sc i μ ≫ epsP cs i μ) +
        (2 : k) • (epsP cs i μ ≫ oddBubble cs i μ) := by
  rw [uR_epsP_nonneg cs i μ hh, dL_epsP_nonneg cs i μ hh, oddBubble_of_nonneg cs i μ hh,
    Linear.comp_smul]
  have ht : ((D.h i μ).toNat : ZMod 2) = (D.h i μ : ZMod 2) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hh]
  simp only [hi, one_mul, ht]
  have hz1 : zsign k (1 : ZMod 2) = -1 := by simp [zsign]
  rw [hz1]
  rcases zsign_cases (k := k) (D.h i μ : ZMod 2) with h | h <;> rw [h] <;> module

/-! ### `⟨hᵢ, λ⟩ < 0`: testing on the components of (1.14) -/

/-- The `♣`-cap with label `n`. -/
abbrev dkM (D : Datum I X) (Sc : Scalars D k) (i : I) (μ : X) (n : ℕ) :=
  cl D Sc μ [dn i, up i] [] (dcapL i n)

/-- For `⟨hᵢ, λ⟩ ≤ 0`, a 2-morphism out of `Fᵢ Eᵢ 1_λ` is determined by its composites with `σ`
and with the dotted rightward cups `(1 ⊗ xᵐ) ∘ η`, `m < -⟨hᵢ,λ⟩` (the components of (1.14)). -/
theorem ext_FE (i : I) (μ : X) (hh : D.h i μ ≤ 0) {Z : (pres D Sc).Presented}
    {f g : (pres D Sc).obj (ob D μ [dn i, up i]) ⟶ Z}
    (h₁ : sgM D Sc i μ ≫ f = sgM D Sc i μ ≫ g)
    (h₂ : ∀ m : ℕ, (m : ℤ) < -D.h i μ → hLM D Sc i μ m ≫ f = hLM D Sc i μ m ≫ g) : f = g := by
  have hid : 𝟙 _ = -(lcM D Sc i μ ≫ sgM D Sc i μ) +
      ∑ n ∈ Finset.range (-D.h i μ).toNat, dkM D Sc i μ n ≫ hLM D Sc i μ n := by
    have := cl_invM₁ Sc i μ hh
    rw [cl_nil] at this
    rw [← this, cl_comp (sChain_lcrossL i i) (sChain_sigmaL i i)]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [cl_comp (sChain_dcapL i n) (sChain_etaL i n)]
  rw [← Category.id_comp f, ← Category.id_comp g, hid]
  simp only [Preadditive.add_comp, Preadditive.neg_comp, Preadditive.sum_comp, Category.assoc, h₁]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  rw [h₂ n (by omega)]

theorem sg_epsP_neg (i : I) (μ : X) (hh : D.h i μ < 0) {Z : (pres D Sc).Presented}
    (f : (pres D Sc).obj (ob D μ []) ⟶ Z) : sgM D Sc i μ ≫ epsP cs i μ ≫ f = 0 := by
  rw [← Category.assoc, eq_2_14_a cs i μ hh, Limits.zero_comp]

theorem hL_uR (i : I) (μ : X) (m : ℕ) :
    hLM D Sc i μ m ≫ uRM D Sc i μ = hLM D Sc i μ (m + 1) := by
  rw [cl_comp (sChain_etaL i m) (sChain_uR i 1)]
  congr 1
  simp [etaL, dotsL, List.replicate_succ']

theorem hL_dL (i : I) (μ : X) (m : ℕ) :
    hLM D Sc i μ m ≫ dLM D Sc i μ = zsign k (D.parity i * m) • hLM D Sc i μ (m + 1) := by
  rw [cl_comp (sChain_etaL i m) (sChain_ddotL' i)]
  have hp : parsum D (ddotL i) = D.parity i := by
    rw [← ddotsL_one, parsum_ddotsL, Nat.cast_one, one_mul]
  -- the downward dot moves below the `m` upward dots
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := []) (T := [dn i, up i])
    [([], Shape.cup i, [])] [] (s := [dn i]) (s' := [dn i]) (t := [up i]) (t' := [up i])
    (sChain_ddotL i) (sChain_dotsL [] i [] m)
  rw [hp, parsum_dotsL] at E
  have E' : cl D Sc μ [] [dn i, up i] (etaL i m ++ (ddotL i).map (whL [] [up i])) =
      zsign k (D.parity i * (m * D.parity i)) •
        cl D Sc μ [] [dn i, up i] (([([], Shape.cup i, [])] ++ (ddotL i).map (whL [] [up i])) ++
          dotsL [dn i] i [] m) := by
    have := congrArg (zsign k (D.parity i * (m * D.parity i)) • ·) E
    simp only [smul_smul, zsign_mul_self, one_smul] at this
    convert this.symm using 2 <;> simp [etaL, dotsL, whL]
  have hcup := cl_cup_slide Sc i μ (sChain_dotsL [] i [] 1)
  have hX : SChain [] ([([], Shape.cup i, [])] ++ (ddotL i).map (whL [] [up i])) [dn i, up i] :=
    SChain.append (t' := [dn i, up i])
      (show SChain [] [([], Shape.cup i, [])] [dn i, up i] from ⟨rfl, rfl⟩) (sChain_ddotL' i)
  have hY : SChain [] ([([], Shape.cup i, [])] ++ (dotsL [] i [] 1).map (whL [dn i] []))
      [dn i, up i] := SChain.append (t' := [dn i, up i])
      (show SChain [] [([], Shape.cup i, [])] [dn i, up i] from ⟨rfl, rfl⟩)
      ((sChain_dotsL [] i [] 1).wh [dn i] [] rfl rfl)
  rw [E', ← cl_comp hX (sChain_uR i m),
    show [([], Shape.cup i, [])] ++ (ddotL i).map (whL [] [up i]) =
      [([], Shape.cup i, [])] ++ (mateL i (dotsL [] i [] 1)).map (whL [] [up i]) from rfl, ← hcup,
    cl_comp hY (sChain_uR i m)]
  congr 1
  rw [← mul_assoc, mul_comm (D.parity i), mul_assoc, zmod2_mul_self, mul_comm]

theorem hL_epsP_lt (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < -D.h i μ) :
    hLM D Sc i μ n ≫ epsP cs i μ =
      if (n : ℤ) = -D.h i μ - 1 then (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ else 0 :=
  eq_2_14_c cs i μ n hn

theorem hL_epsP_top (i : I) (μ : X) (hh : D.h i μ < 0) :
    hLM D Sc i μ (-D.h i μ).toNat ≫ epsP cs i μ = (↑(cs.c μ i)⁻¹ : k) • oddBubble cs i μ := by
  rw [oddBubble, ite_eq_right (show ¬ 0 ≤ D.h i μ by omega), bubR, ite_eq_left (by omega),
    smul_smul, cinv_mul_c, one_smul]

theorem sg_uR_epsP_neg (i : I) (μ : X) (hh : D.h i μ < 0) :
    sgM D Sc i μ ≫ uRM D Sc i μ ≫ epsP cs i μ = eLM D Sc i μ 0 ≫ hLM D Sc i μ 0 ≫ epsP cs i μ := by
  have E := sg_uR (Sc := Sc) i μ
  rw [sub_eq_iff_eq_add] at E
  rw [← Category.assoc, E]
  simp only [Preadditive.add_comp, Linear.smul_comp, Category.assoc, eq_2_14_a cs i μ hh,
    Limits.comp_zero, smul_zero, add_zero]

theorem sg_dL_epsP_neg (i : I) (μ : X) (hh : D.h i μ < 0) :
    sgM D Sc i μ ≫ dLM D Sc i μ ≫ epsP cs i μ =
      zsign k (D.parity i) • (eLM D Sc i μ 0 ≫ hLM D Sc i μ 0 ≫ epsP cs i μ) := by
  have E := sg_dL (Sc := Sc) i μ
  have E' : sgM D Sc i μ ≫ dLM D Sc i μ = zsign k (D.parity i) • (dRM D Sc i μ ≫ sgM D Sc i μ +
      eLM D Sc i μ 0 ≫ hLM D Sc i μ 0) := by
    have hz := zsign_mul_self (k := k) (D.parity i)
    have h1 : (zsign k (D.parity i) * zsign k (D.parity i)) • (sgM D Sc i μ ≫ dLM D Sc i μ) =
        sgM D Sc i μ ≫ dLM D Sc i μ := by rw [hz, one_smul]
    linear_combination (norm := module) zsign k (D.parity i) • E - h1
  rw [← Category.assoc, E']
  simp only [Preadditive.add_comp, Linear.smul_comp, Category.assoc, eq_2_14_a cs i μ hh,
    Limits.comp_zero, zero_add]

theorem cast_neg_one_eq (a : ℤ) (h : a = -1) : (a : ZMod 2) = 1 := by
  subst h; decide

/-- (4.3), `n = 1`, `⟨hᵢ, λ⟩ < 0`, `i` even. -/
theorem lemma41_eq3_one_even_neg (i : I) (μ : X) (hi : D.parity i = 0) (hh : D.h i μ < 0) :
    uRM D Sc i μ ≫ epsP cs i μ = dLM D Sc i μ ≫ epsP cs i μ := by
  refine ext_FE i μ hh.le ?_ fun m _ => ?_
  · rw [sg_uR_epsP_neg cs i μ hh, sg_dL_epsP_neg cs i μ hh, hi, zsign_zero, one_smul]
  · rw [← Category.assoc, ← Category.assoc, hL_uR, hL_dL, hi, zero_mul, zsign_zero, one_smul]

/-- (4.3), `n = 1`, `⟨hᵢ, λ⟩ < 0`, `i` odd. -/
theorem lemma41_eq3_one_odd_neg (i : I) (μ : X) (hi : D.parity i = 1) (hh : D.h i μ < 0) :
    uRM D Sc i μ ≫ epsP cs i μ =
      zsign k (D.h i μ : ZMod 2) • (dLM D Sc i μ ≫ epsP cs i μ) +
        (2 : k) • (epsP cs i μ ≫ oddBubble cs i μ) := by
  have hz1 : zsign k (1 : ZMod 2) = -1 := by simp [zsign]
  refine ext_FE i μ hh.le ?_ fun m hm => ?_
  · rw [Preadditive.comp_add, Linear.comp_smul, Linear.comp_smul, sg_uR_epsP_neg cs i μ hh,
      sg_dL_epsP_neg cs i μ hh, sg_epsP_neg cs i μ hh, smul_zero, add_zero, smul_smul, hi, hz1,
      hL_epsP_lt cs i μ 0 (by omega)]
    by_cases h1 : D.h i μ = -1
    · rw [cast_neg_one_eq _ h1, hz1, ite_eq_left (by omega)]
      simp
    · rw [ite_eq_right (by omega)]
      simp
  · rw [Preadditive.comp_add, Linear.comp_smul, Linear.comp_smul, ← Category.assoc,
      ← Category.assoc, ← Category.assoc, hL_uR, hL_dL, hi, one_mul, Linear.smul_comp,
      smul_smul]
    by_cases htop : (m : ℤ) + 1 = -D.h i μ
    · have hmt : m + 1 = (-D.h i μ).toNat := by omega
      rw [hmt, hL_epsP_top cs i μ hh, hL_epsP_lt cs i μ m hm, ite_eq_left (by omega),
        Linear.smul_comp, Category.id_comp]
      have hs : zsign k (D.h i μ : ZMod 2) * zsign k (m : ZMod 2) = -1 := by
        rw [← zsign_add, show ((D.h i μ : ℤ) : ZMod 2) + (m : ZMod 2) = 1 by
          rw [show (m : ZMod 2) = ((m : ℤ) : ZMod 2) by simp, ← Int.cast_add]
          exact cast_neg_one_eq _ (by omega), hz1]
      rw [hs]
      module
    · rw [hL_epsP_lt cs i μ (m + 1) (by push_cast; omega),
        hL_epsP_lt cs i μ m hm, ite_eq_right (show ¬ (m : ℤ) = -D.h i μ - 1 by omega)]
      simp only [Limits.zero_comp, smul_zero, add_zero]
      by_cases hb : ((m + 1 : ℕ) : ℤ) = -D.h i μ - 1
      · rw [ite_eq_left hb]
        have hs : zsign k (D.h i μ : ZMod 2) * zsign k (m : ZMod 2) = 1 := by
          rw [← zsign_add, show ((D.h i μ : ℤ) : ZMod 2) + (m : ZMod 2) = 0 by
            rw [show (m : ZMod 2) = ((m : ℤ) : ZMod 2) by simp, ← Int.cast_add,
              show D.h i μ + m = -2 by push_cast at hb; omega]
            decide, zsign_zero]
        rw [hs, one_smul]
      · rw [ite_eq_right hb, smul_zero]

/-- **Brundan–Ellis, Proposition 4.1 (4.3), `n = 1`, `i` even**: an upward dot on the right leg
of the leftward cap `ε'` equals a downward dot on its left leg. -/
theorem lemma41_eq3_one_even (i : I) (μ : X) (hi : D.parity i = 0) :
    uRM D Sc i μ ≫ epsP cs i μ = dLM D Sc i μ ≫ epsP cs i μ := by
  rcases le_or_gt 0 (D.h i μ) with hh | hh
  · exact lemma41_eq3_one_even_nonneg cs i μ hi hh
  · exact lemma41_eq3_one_even_neg cs i μ hi hh

/-- **Brundan–Ellis, Proposition 4.1 (4.3), `n = 1`, `i` odd**: an upward dot on the right leg of
the leftward cap `ε'` equals `(-1)^{⟨hᵢ,λ⟩}` times a downward dot on its left leg plus twice
`ε'` followed by the odd bubble (2.18). -/
theorem lemma41_eq3_one_odd (i : I) (μ : X) (hi : D.parity i = 1) :
    uRM D Sc i μ ≫ epsP cs i μ =
      zsign k (D.h i μ : ZMod 2) • (dLM D Sc i μ ≫ epsP cs i μ) +
        (2 : k) • (epsP cs i μ ≫ oddBubble cs i μ) := by
  rcases le_or_gt 0 (D.h i μ) with hh | hh
  · exact lemma41_eq3_one_odd_nonneg cs i μ hi hh
  · exact lemma41_eq3_one_odd_neg cs i μ hi hh

end OddMath.SKM
