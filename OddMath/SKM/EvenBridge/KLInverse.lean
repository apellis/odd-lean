/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Decompositions
import Categorification.Diagrams.KL3.BubbleSlidesGen
import Categorification.KLR.KL1

/-!
# The inverse of the decomposition of KL III Proposition 3.25 in components

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`* III, arXiv:0807.3250v1,
Proposition 3.25. For `n = ⟨i, λ⟩ ≥ 0` the components `α_s`, `β_s` (`alphaEF`, `betaEF`) of
the decomposition `E_i F_i 1_λ ≅ F_i E_i 1_λ ⊕ ⨁_{s < n} 1_λ` are rearranged into the
components dual to the dotted caps `dotCapEF m`:

* `dcupEF n = ∑_{g < n - m} ccw_{-n-1+g} β_{m+g}` satisfies `dcupEF m · dotCapEF m' = δ`
  (`dcupEF_dotCapEF`), `dcupEF m · crossl = 0` (`dcupEF_crossl`) and
  `∑_m dotCapEF m · dcupEF m = ∑_s α_s β_s` (`sum_dotCapEF_dcupEF`);
* `crossr · dotCapEF m = 0` for `m < n` (`crossr_dotCapEF`), from `crossr α_s = 0`.

The case `n ≤ 0` (`alphaFE`, `betaFE`) needs only the reindexing `s ↦ -n - 1 - s`
(`betaFE_reflect`, `sum_alphaFE_cupDotFE`) and `crossl α_s = 0` (`crossl_alphaFE`).

These are the images of the `♦`-cups and `♦`-caps of J. Brundan, A. P. Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, (2.6), and the identities are the inversion relations of
Definition 1.5 for an even colour.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k] (i : I) (lam : X)

variable (RD k) in
/-- The component `1_λ ⟶ E_i F_i 1_λ` dual to the dotted cap with `m` dots. -/
def dcupEF (m : ℕ) : (pres RD k).obj (ob RD lam []) ⟶ (pres RD k).obj (ob RD lam [up i, dn i]) :=
  ∑ g ∈ Finset.range ((ip RD i lam).toNat - m),
    ccwU RD k lam i (-ip RD i lam - 1 + g) ≫ betaEF RD k i lam (m + g)

/-! ## The case `⟨i, λ⟩ ≥ 0` -/

theorem crossr_alphaEF (t : ℕ) (ht : t < (ip RD i lam).toNat) :
    dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) ≫ alphaEF RD k i lam t = 0 := by
  have h0 := b0a0_EF (RD := RD) (k := k) i lam (by omega)
  have htot := congrArg (dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) ≫ ·)
    (total_EF (RD := RD) (k := k) i lam)
  rw [Preadditive.comp_add, ← Category.assoc, h0, Category.id_comp, Category.comp_id,
    Preadditive.comp_sum, add_eq_left] at htot
  have h2 := congrArg (· ≫ alphaEF RD k i lam t) htot
  simp only [Preadditive.sum_comp, zero_comp] at h2
  have h3 : ∀ s ∈ Finset.range (ip RD i lam).toNat,
      (dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) ≫
          alphaEF RD k i lam s ≫ betaEF RD k i lam s) ≫ alphaEF RD k i lam t =
        if s = t then dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) ≫ alphaEF RD k i lam t
        else 0 := by
    intro s hs
    rw [Category.assoc, Category.assoc, ba_EF i lam s t (Finset.mem_range.1 hs) ht]
    split_ifs with hst
    · subst hst; simp
    · simp
  rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 ht)] at h2
  exact h2

@[reassoc]
theorem crossr_dotCapEF (t : ℕ) (ht : t < (ip RD i lam).toNat) :
    dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) ≫
      dg RD k lam [up i, dn i] [] (dotCapEFLs i t) = 0 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    have h := crossr_alphaEF (RD := RD) (k := k) i lam t ht
    rw [alphaEF, Finset.sum_range_succ', Preadditive.comp_add, Preadditive.comp_sum,
      Finset.sum_eq_zero (fun g hg => by
        rw [Finset.mem_range] at hg
        rw [← Category.assoc, ih _ (by omega) (by omega), zero_comp]), zero_add] at h
    simpa [ccwU_deg0] using h

theorem betaEF_dotCapEF (s m : ℕ) (hs : s < (ip RD i lam).toNat) :
    betaEF RD k i lam s ≫ dg RD k lam [up i, dn i] [] (dotCapEFLs i m) =
      cwU RD k lam i (ip RD i lam - 1 + ((m : ℤ) - s)) := by
  rw [betaEF, dotCapEFLs, ← dg_dots_cap_dn, dg_comp (by schain) (by schain)]
  have e : ip RD i lam - 1 + ((m : ℤ) - s) = (((ip RD i lam).toNat - 1 - s + m : ℕ) : ℤ) := by
    omega
  rw [e, cwU_of_nonneg, cwLs, cupDotEFLs, List.replicate_add]
  simp only [List.append_assoc]

@[reassoc]
theorem dcupEF_dotCapEF (m n : ℕ) (hm : m < (ip RD i lam).toNat) (hn : n < (ip RD i lam).toNat) :
    dcupEF RD k i lam n ≫ dg RD k lam [up i, dn i] [] (dotCapEFLs i m) =
      if m = n then 𝟙 _ else 0 := by
  rw [dcupEF, Preadditive.sum_comp]
  have hterm : ∀ g ∈ Finset.range ((ip RD i lam).toNat - n),
      (ccwU RD k lam i (-ip RD i lam - 1 + g) ≫ betaEF RD k i lam (n + g)) ≫
          dg RD k lam [up i, dn i] [] (dotCapEFLs i m) =
        cwU RD k lam i (ip RD i lam - 1 + (((m : ℤ) - n) - g)) ≫
          ccwU RD k lam i (-ip RD i lam - 1 + g) := by
    intro g hg
    rw [Finset.mem_range] at hg
    rw [Category.assoc, betaEF_dotCapEF i lam _ _ (by omega), endEmpty_comm]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm,
    show (ip RD i lam).toNat - n = (ip RD i lam).toNat - n - 1 + 1 by omega,
    sum_cw_ccw lam i _ _ (by omega)]
  by_cases hmn : m = n
  · subst hmn; simp
  · rw [ite_eq_right (by omega), ite_eq_right hmn]

@[reassoc]
theorem dcupEF_crossl (n : ℕ) :
    dcupEF RD k i lam n ≫ dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) = 0 := by
  rw [dcupEF, Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun g hg => ?_
  rw [Finset.mem_range] at hg
  have h := ba0_EF (RD := RD) (k := k) i lam (n + g) (by omega)
  rw [Preadditive.comp_neg, neg_eq_zero] at h
  rw [Category.assoc, h, comp_zero]

theorem sum_dotCapEF_dcupEF :
    ∑ m ∈ Finset.range (ip RD i lam).toNat,
        dg RD k lam [up i, dn i] [] (dotCapEFLs i m) ≫ dcupEF RD k i lam m =
      ∑ s ∈ Finset.range (ip RD i lam).toNat, alphaEF RD k i lam s ≫ betaEF RD k i lam s := by
  have hr : ∀ s ∈ Finset.range (ip RD i lam).toNat,
      alphaEF RD k i lam s ≫ betaEF RD k i lam s =
        ∑ j ∈ Finset.range (s + 1),
          dg RD k lam [up i, dn i] [] (dotCapEFLs i j) ≫
            ccwU RD k lam i (-ip RD i lam - 1 + ((s - j : ℕ) : ℤ)) ≫
              betaEF RD k i lam (j + (s - j)) := by
    intro s _
    rw [alphaEF, Preadditive.sum_comp, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [Category.assoc, show s + 1 - 1 - j = s - j by omega, show s - (s - j) = j by omega,
      show j + (s - j) = s by omega]
  rw [Finset.sum_congr rfl hr,
    Finset.sum_range_diag_flip (ip RD i lam).toNat fun j g =>
      dg RD k lam [up i, dn i] [] (dotCapEFLs i j) ≫
        ccwU RD k lam i (-ip RD i lam - 1 + (g : ℤ)) ≫ betaEF RD k i lam (j + g)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dcupEF, Preadditive.comp_sum]

/-! ## The case `⟨i, λ⟩ ≤ 0` -/

@[reassoc]
theorem crossl_alphaFE (t : ℕ) (ht : t < (-ip RD i lam).toNat) :
    dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) ≫ alphaFE RD k i lam t = 0 := by
  have h0 := b0a0_FE (RD := RD) (k := k) i lam (by omega)
  have htot := congrArg (dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) ≫ ·)
    (total_FE (RD := RD) (k := k) i lam)
  rw [Preadditive.comp_add, ← Category.assoc, h0, Category.id_comp, Category.comp_id,
    Preadditive.comp_sum, add_eq_left] at htot
  have h2 := congrArg (· ≫ alphaFE RD k i lam t) htot
  simp only [Preadditive.sum_comp, zero_comp] at h2
  have h3 : ∀ s ∈ Finset.range (-ip RD i lam).toNat,
      (dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) ≫
          alphaFE RD k i lam s ≫ betaFE RD k i lam s) ≫ alphaFE RD k i lam t =
        if s = t then dg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) ≫ alphaFE RD k i lam t
        else 0 := by
    intro s hs
    rw [Category.assoc, Category.assoc, ba_FE i lam s t (Finset.mem_range.1 hs) ht]
    split_ifs with hst
    · subst hst; simp
    · simp
  rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 ht)] at h2
  exact h2

theorem betaFE_reflect (m : ℕ) (hm : m < (-ip RD i lam).toNat) :
    betaFE RD k i lam ((-ip RD i lam).toNat - 1 - m) =
      dg RD k lam [] [dn i, up i] (cupDotFELs i m) := by
  rw [betaFE, show (-ip RD i lam).toNat - 1 - ((-ip RD i lam).toNat - 1 - m) = m by omega]

theorem sum_alphaFE_cupDotFE :
    ∑ m ∈ Finset.range (-ip RD i lam).toNat,
        alphaFE RD k i lam ((-ip RD i lam).toNat - 1 - m) ≫
          dg RD k lam [] [dn i, up i] (cupDotFELs i m) =
      ∑ s ∈ Finset.range (-ip RD i lam).toNat, alphaFE RD k i lam s ≫ betaFE RD k i lam s := by
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [show (-ip RD i lam).toNat - 1 - ((-ip RD i lam).toNat - 1 - m) = m by omega, betaFE]

@[reassoc]
theorem cupDotFE_crossr (m : ℕ) (hm : m < (-ip RD i lam).toNat) :
    dg RD k lam [] [dn i, up i] (cupDotFELs i m) ≫
      dg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) = 0 := by
  have h := ba0_FE (RD := RD) (k := k) i lam ((-ip RD i lam).toNat - 1 - m) (by omega)
  rw [Preadditive.comp_neg, neg_eq_zero, betaFE_reflect i lam m hm] at h
  exact h

@[reassoc]
theorem cupDotFE_alphaFE (m n : ℕ) (hm : m < (-ip RD i lam).toNat)
    (hn : n < (-ip RD i lam).toNat) :
    dg RD k lam [] [dn i, up i] (cupDotFELs i m) ≫
        alphaFE RD k i lam ((-ip RD i lam).toNat - 1 - n) =
      if m = n then 𝟙 _ else 0 := by
  rw [← betaFE_reflect i lam m hm, ba_FE i lam _ _ (by omega) (by omega)]
  by_cases hmn : m = n
  · subst hmn; simp
  · rw [ite_eq_right (by omega), ite_eq_right hmn]

variable (RD k) in
/-- **KL III `eq_r3_hard-gen`** for `c ≠ d` with `c · d = 0`: the KL II polynomial is `Q_cd = 1`,
so the correction term vanishes and `ψ₀ψ₁ψ₀ = ψ₁ψ₀ψ₁` on `E_c E_d E_c`. -/
theorem dg_braidQ_zero (μ : X) (c d : I) (h : c ≠ d) (hcd : C.dot c d = 0) :
    dg RD k μ [up c, up d, up c] [up c, up d, up c]
        [([], .cross true c d, [up c]), ([up d], .cross true c c, []),
          ([], .cross true d c, [up c])] =
      dg RD k μ [up c, up d, up c] [up c, up d, up c]
        [([up c], .cross true d c, []), ([], .cross true c c, [up d]),
          ([up c], .cross true c d, [])] := by
  have key := KLR.Diagram.braidQ_at (KLR.klQ2 k C) (u := []) (v := []) h
    (KLR.Diagram.braidL c d c) (KLR.Diagram.braidR c d c) (KLR.Diagram.E0 c d c)
    (KLR.Diagram.E1 c d c) (KLR.Diagram.E2 c d c) rfl rfl rfl rfl rfl
  rw [KLR.klQ2, ite_eq_left hcd, KLR.qbar_one] at key
  simp only [KLR.ncEval, AddMonoidAlgebra.coeff_zero, Finsupp.sum_zero_index, sub_eq_zero] at key
  have key' := congrArg (upFunctor RD k μ).map key
  simp only [upFunctor_diag, upDiag_eq_dg] at key'
  exact key'

end Categorification.KL3.Diagram
