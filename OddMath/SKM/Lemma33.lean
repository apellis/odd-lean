/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Lemma32
import OddMath.SKM.Lemma31Rot

/-!
# The rotated braid relations (Brundan–Ellis, Lemma 3.3)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Lemma 3.3, relations
(3.8) (TeX label `lurking`) and (3.9) (`lastone`): the braid relation (1.9) rotated so that one
strand (3.8), respectively all three strands (3.9), point downward.

This file contains (3.9): on `Fₖ Fⱼ Fᵢ 1_λ` (bottom), the two composites of three downward
crossings (2.1) ending at `Fᵢ Fⱼ Fₖ`, with the strand `j` passing to the right (`lemma33_eq9_lhs`)
or to the left (`lemma33_eq9_rhs`) of the crossing of `i` and `k`, are equal unless
`i = k ≠ j`, when their difference is
`∑_{r+s=dᵢⱼ-1} (-1)^{|i|(⌊dᵢⱼ/2⌋+r+1)} tᵢⱼ x^r ⊗ 1 ⊗ x^s
 + ∑ (-1)^{|i|(⌊p/2⌋+r+1)+|j|⌊q/2⌋} sᵢⱼ^{pq} x^r ⊗ x^q ⊗ x^s` (downward dots; in each term the
dots on the right strand come first, then those on the middle strand, then those on the left
strand: they are drawn at the same height). The proof: the left-hand side is the mate of the
braid relation (1.9) for `(k, j, i)` (`cl_mateN_comp3`, `cl_mateN_whiskerL`, `cl_mateN_whiskerR`),
and the mates of the dots are computed with (2.2).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

/-! ## The braid relation (1.9) for `i = k ≠ j` in normal form -/

variable (Sc) in
theorem cl_braidEq (i j : I) (ν : X) (hij : i ≠ j) :
    cl D Sc ν [up i, up j, up i] [up i, up j, up i]
        (crossL [] i j [up i] ++ crossL [up j] i i [] ++ crossL [] j i [up i]) =
      cl D Sc ν [up i, up j, up i] [up i, up j, up i]
          (crossL [up i] j i [] ++ crossL [] i i [up j] ++ crossL [up i] i j []) +
        ∑ s ∈ Finset.range (D.dn i j),
          (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
            cl D Sc ν [up i, up j, up i] [up i, up j, up i]
              (dotsL [up i, up j] i [] s ++ dotsL [] i [up j, up i] (D.dn i j - 1 - s)) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
          (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
            cl D Sc ν [up i, up j, up i] [up i, up j, up i]
              (dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q ++
                dotsL [] i [up j, up i] (p - 1 - s)) := by
  have := lin_relation Sc (.braidEq i j ν hij)
  skm_rel_simp this
  rw [← sub_eq_zero, ← this]
  abel

/-! ## Mates of composites of three layers -/

variable (Sc) in
theorem cl_mateN_comp3 (μ : X) {w₀ w₁ w₂ w₃ : List I} {L₁ L₂ L₃ : List (LayerData I)}
    (h₁ : SChain (ups w₀) L₁ (ups w₁)) (h₂ : SChain (ups w₁) L₂ (ups w₂))
    (h₃ : SChain (ups w₂) L₃ (ups w₃)) :
    cl D Sc μ (dns w₃) (dns w₀) (mateN w₀ w₃ (L₁ ++ L₂ ++ L₃)) =
      zsign k (parsum D L₁ * parsum D L₂ + parsum D L₁ * parsum D L₃ +
          parsum D L₂ * parsum D L₃) •
        (cl D Sc μ (dns w₃) (dns w₂) (mateN w₂ w₃ L₃) ≫
          cl D Sc μ (dns w₂) (dns w₁) (mateN w₁ w₂ L₂) ≫
            cl D Sc μ (dns w₁) (dns w₀) (mateN w₀ w₁ L₁)) := by
  have c1 := cl_mateN_comp Sc μ h₂ h₁
  have c2 := cl_mateN_comp Sc μ h₃ (h₁.append h₂)
  rw [cl_comp (sChain_mateN h₂) (sChain_mateN h₁), c1, Linear.comp_smul,
    cl_comp (sChain_mateN h₃) (sChain_mateN (h₁.append h₂)), c2, smul_smul, ← zsign_add,
    smul_smul, ← zsign_add, parsum_append]
  have : parsum D L₁ * parsum D L₂ + parsum D L₁ * parsum D L₃ + parsum D L₂ * parsum D L₃ +
      parsum D L₂ * parsum D L₁ + parsum D L₃ * (parsum D L₁ + parsum D L₂) = 0 := by
    generalize parsum D L₁ = a; generalize parsum D L₂ = b; generalize parsum D L₃ = c
    revert a b c; decide
  rw [this, zsign_zero, one_smul]

/-! ## Lemma 3.3 (3.9) -/

/-- The left-hand side of (3.9): the strand `j` passes to the right of the crossing of `i` and
`k`. -/
def lemma33_eq9_lhs (i j k' : I) : List (LayerData I) :=
  (dcrossL j i).map (whL [dn k'] []) ++ (dcrossL k' i).map (whL [] [dn j]) ++
    (dcrossL k' j).map (whL [dn i] [])

/-- The second term of (3.9): the strand `j` passes to the left of the crossing of `i` and `k`. -/
def lemma33_eq9_rhs (i j k' : I) : List (LayerData I) :=
  (dcrossL k' j).map (whL [] [dn i]) ++ (dcrossL k' i).map (whL [dn j] []) ++
    (dcrossL j i).map (whL [] [dn k'])

theorem hτ_ups (a b : I) : SChain (ups [a, b]) (crossL [] a b []) (ups [b, a]) := by
  simp [crossL, Shape.dom, Shape.cod]

variable (Sc) in
/-- The mate of the left-hand side of (1.9) for `(k, j, i)` is `±` the left-hand side of (3.9). -/
theorem cl_mate_braid_lhs (μ : X) (i j k' : I) :
    cl D Sc μ (dns [i, j, k']) (dns [k', j, i])
        (mateN [k', j, i] [i, j, k']
          (crossL [] k' j [up i] ++ crossL [up j] k' i [] ++ crossL [] j i [up k'])) =
      zsign k (D.parity k' * D.parity j * (D.parity k' * D.parity i) +
          D.parity k' * D.parity j * (D.parity j * D.parity i) +
          D.parity k' * D.parity i * (D.parity j * D.parity i)) •
        cl D Sc μ (dns [i, j, k']) (dns [k', j, i]) (lemma33_eq9_lhs i j k') := by
  have h₁ : SChain (ups [k', j, i]) (crossL [] k' j [up i]) (ups [j, k', i]) := by
    simp [crossL, Shape.dom, Shape.cod]
  have h₂ : SChain (ups [j, k', i]) (crossL [up j] k' i []) (ups [j, i, k']) := by
    simp [crossL, Shape.dom, Shape.cod]
  have h₃ : SChain (ups [j, i, k']) (crossL [] j i [up k']) (ups [i, j, k']) := by
    simp [crossL, Shape.dom, Shape.cod]
  rw [cl_mateN_comp3 Sc μ h₁ h₂ h₃]
  have e₁ : cl D Sc μ (dns [j, k', i]) (dns [k', j, i]) (mateN [k', j, i] [j, k', i]
      (crossL [] k' j [up i])) =
      cl D Sc μ (dns [j, k', i]) (dns [k', j, i]) ((dcrossL k' j).map (whL [dn i] [])) := by
    have := cl_mateN_whiskerR Sc μ (w := [k', j]) (w' := [j, k']) [i] (hτ_ups k' j)
    rw [← dcrossL_eq_mateN] at this
    exact this
  have e₂ : cl D Sc μ (dns [j, i, k']) (dns [j, k', i]) (mateN [j, k', i] [j, i, k']
      (crossL [up j] k' i [])) =
      cl D Sc μ (dns [j, i, k']) (dns [j, k', i]) ((dcrossL k' i).map (whL [] [dn j])) := by
    have := cl_mateN_whiskerL Sc μ [j] (w := [k', i]) (w' := [i, k']) (hτ_ups k' i)
    rw [← dcrossL_eq_mateN] at this
    exact this
  have e₃ : cl D Sc μ (dns [i, j, k']) (dns [j, i, k']) (mateN [j, i, k'] [i, j, k']
      (crossL [] j i [up k'])) =
      cl D Sc μ (dns [i, j, k']) (dns [j, i, k']) ((dcrossL j i).map (whL [dn k'] [])) := by
    have := cl_mateN_whiskerR Sc μ (w := [j, i]) (w' := [i, j]) [k'] (hτ_ups j i)
    rw [← dcrossL_eq_mateN] at this
    exact this
  rw [e₁, e₂, e₃]
  have c₁ : SChain (dns [i, j, k']) ((dcrossL j i).map (whL [dn k'] [])) (dns [j, i, k']) :=
    (sChain_dcrossL j i).wh [dn k'] [] rfl rfl
  have c₂ : SChain (dns [j, i, k']) ((dcrossL k' i).map (whL [] [dn j])) (dns [j, k', i]) :=
    (sChain_dcrossL k' i).wh [] [dn j] rfl rfl
  have c₃ : SChain (dns [j, k', i]) ((dcrossL k' j).map (whL [dn i] [])) (dns [k', j, i]) :=
    (sChain_dcrossL k' j).wh [dn i] [] rfl rfl
  rw [cl_comp c₂ c₃, cl_comp c₁ (c₂.append c₃), lemma33_eq9_lhs, List.append_assoc]
  simp only [crossL, parsum_cons, parsum_nil, Shape.parity, add_zero]

variable (Sc) in
/-- The mate of the right-hand side of (1.9) for `(k, j, i)` is `±` the second term of (3.9). -/
theorem cl_mate_braid_rhs (μ : X) (i j k' : I) :
    cl D Sc μ (dns [i, j, k']) (dns [k', j, i])
        (mateN [k', j, i] [i, j, k']
          (crossL [up k'] j i [] ++ crossL [] k' i [up j] ++ crossL [up i] k' j [])) =
      zsign k (D.parity k' * D.parity j * (D.parity k' * D.parity i) +
          D.parity k' * D.parity j * (D.parity j * D.parity i) +
          D.parity k' * D.parity i * (D.parity j * D.parity i)) •
        cl D Sc μ (dns [i, j, k']) (dns [k', j, i]) (lemma33_eq9_rhs i j k') := by
  have h₁ : SChain (ups [k', j, i]) (crossL [up k'] j i []) (ups [k', i, j]) := by
    simp [crossL, Shape.dom, Shape.cod]
  have h₂ : SChain (ups [k', i, j]) (crossL [] k' i [up j]) (ups [i, k', j]) := by
    simp [crossL, Shape.dom, Shape.cod]
  have h₃ : SChain (ups [i, k', j]) (crossL [up i] k' j []) (ups [i, j, k']) := by
    simp [crossL, Shape.dom, Shape.cod]
  rw [cl_mateN_comp3 Sc μ h₁ h₂ h₃]
  have e₁ : cl D Sc μ (dns [k', i, j]) (dns [k', j, i]) (mateN [k', j, i] [k', i, j]
      (crossL [up k'] j i [])) =
      cl D Sc μ (dns [k', i, j]) (dns [k', j, i]) ((dcrossL j i).map (whL [] [dn k'])) := by
    have := cl_mateN_whiskerL Sc μ [k'] (w := [j, i]) (w' := [i, j]) (hτ_ups j i)
    rw [← dcrossL_eq_mateN] at this
    exact this
  have e₂ : cl D Sc μ (dns [i, k', j]) (dns [k', i, j]) (mateN [k', i, j] [i, k', j]
      (crossL [] k' i [up j])) =
      cl D Sc μ (dns [i, k', j]) (dns [k', i, j]) ((dcrossL k' i).map (whL [dn j] [])) := by
    have := cl_mateN_whiskerR Sc μ (w := [k', i]) (w' := [i, k']) [j] (hτ_ups k' i)
    rw [← dcrossL_eq_mateN] at this
    exact this
  have e₃ : cl D Sc μ (dns [i, j, k']) (dns [i, k', j]) (mateN [i, k', j] [i, j, k']
      (crossL [up i] k' j [])) =
      cl D Sc μ (dns [i, j, k']) (dns [i, k', j]) ((dcrossL k' j).map (whL [] [dn i])) := by
    have := cl_mateN_whiskerL Sc μ [i] (w := [k', j]) (w' := [j, k']) (hτ_ups k' j)
    rw [← dcrossL_eq_mateN] at this
    exact this
  rw [e₁, e₂, e₃]
  have c₁ : SChain (dns [i, j, k']) ((dcrossL k' j).map (whL [] [dn i])) (dns [i, k', j]) :=
    (sChain_dcrossL k' j).wh [] [dn i] rfl rfl
  have c₂ : SChain (dns [i, k', j]) ((dcrossL k' i).map (whL [dn j] [])) (dns [k', i, j]) :=
    (sChain_dcrossL k' i).wh [dn j] [] rfl rfl
  have c₃ : SChain (dns [k', i, j]) ((dcrossL j i).map (whL [] [dn k'])) (dns [k', j, i]) :=
    (sChain_dcrossL j i).wh [] [dn k'] rfl rfl
  rw [cl_comp c₂ c₃, cl_comp c₁ (c₂.append c₃), lemma33_eq9_rhs, List.append_assoc]
  simp only [crossL, parsum_cons, parsum_nil, Shape.parity, add_zero]
  congr 2
  generalize D.parity i = a; generalize D.parity j = b; generalize D.parity k' = c
  revert a b c; decide

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.3 (3.9), unless `i = k ≠ j`.** -/
theorem lemma33_eq9 (i j k' : I) (ν : X) (h : ¬(i = k' ∧ i ≠ j)) :
    cl D Sc ν [dn k', dn j, dn i] [dn i, dn j, dn k'] (lemma33_eq9_lhs i j k') =
      cl D Sc ν [dn k', dn j, dn i] [dn i, dn j, dn k'] (lemma33_eq9_rhs i j k') := by
  have hb : cl D Sc (wt D ν (dns [i, j, k'])) (ups [k', j, i]) (ups [i, j, k'])
      (crossL [] k' j [up i] ++ crossL [up j] k' i [] ++ crossL [] j i [up k']) =
      cl D Sc (wt D ν (dns [i, j, k'])) (ups [k', j, i]) (ups [i, j, k'])
      (crossL [up k'] j i [] ++ crossL [] k' i [up j] ++ crossL [up i] k' j []) :=
    cl_braid Sc k' j i _ (fun ⟨h1, h2⟩ => h ⟨h1.symm, h1 ▸ h2⟩)
  have := congrArg (mateMap D Sc ν [k', j, i] [i, j, k']) hb
  rw [mateMap_cl, mateMap_cl, cl_mate_braid_lhs, cl_mate_braid_rhs] at this
  have := congrArg (zsign k (D.parity k' * D.parity j * (D.parity k' * D.parity i) +
          D.parity k' * D.parity j * (D.parity j * D.parity i) +
          D.parity k' * D.parity i * (D.parity j * D.parity i)) • ·) this
  simp only [smul_smul, zsign_mul_self, one_smul] at this
  exact this

/-- Downward dots on three strands `Fᵢ Fⱼ Fᵢ`: `s` on the right strand, then `q` on the middle
strand, then `r` on the left strand. -/
def dots3 (i j : I) (r q s : ℕ) : List (LayerData I) :=
  (ddotsL i s).map (whL [dn i, dn j] []) ++ (ddotsL j q).map (whL [dn i] [dn i]) ++
    (ddotsL i r).map (whL [] [dn j, dn i])

theorem sChain_dots3 (i j : I) (r q s : ℕ) :
    SChain [dn i, dn j, dn i] (dots3 i j r q s) [dn i, dn j, dn i] :=
  (((sChain_ddotsL i s).wh [dn i, dn j] [] rfl rfl).append
    ((sChain_ddotsL j q).wh [dn i] [dn i] rfl rfl)).append
    ((sChain_ddotsL i r).wh [] [dn j, dn i] rfl rfl)

theorem zsign_aux3 (σ A B C : ZMod 2) (x : k) (h : σ + (A + B) = C) :
    zsign k σ * (zsign k A * x * zsign k B) = zsign k C * x := by
  rw [← h, zsign_add, zsign_add]; ring

/-- The sign identity behind the coefficients of (3.9). -/
theorem lemma33_sign (a b R S FR FS F : ZMod 2) (hfl : F + S + R * S + FS + FR + R = 0)
    (hd : a * (R + S + 1) = 0) :
    a * b * (a * a) + a * b * (b * a) + a * a * (b * a) + a * (b + S) + R * a * (S * a) +
      a * FR + a * FS = a * (F + S + 1) := by
  revert a b R S FR FS F; decide

variable (Sc) in
/-- The mate of the correction terms of (1.9) with `t`. -/
theorem cl_mate_braid_tterm (μ : X) (i j : I) (r s : ℕ) :
    cl D Sc μ (dns [i, j, i]) (dns [i, j, i])
        (mateN [i, j, i] [i, j, i] (dotsL [up i, up j] i [] s ++ dotsL [] i [up j, up i] r)) =
      zsign k ((r : ZMod 2) * D.parity i * ((s : ZMod 2) * D.parity i) +
          D.parity i * ((r / 2 : ℕ) : ZMod 2) + D.parity i * ((s / 2 : ℕ) : ZMod 2)) •
        cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) (dots3 i j s 0 r) := by
  have hS : SChain (ups [i, j, i]) (dotsL [up i, up j] i [] s) (ups [i, j, i]) :=
    sChain_dotsL [up i, up j] i [] s
  have hR : SChain (ups [i, j, i]) (dotsL [] i [up j, up i] r) (ups [i, j, i]) :=
    sChain_dotsL [] i [up j, up i] r
  have hc := cl_mateN_comp Sc μ hR hS
  rw [parsum_dotsL, parsum_dotsL] at hc
  have hc' := congrArg (zsign k ((r : ZMod 2) * D.parity i * ((s : ZMod 2) * D.parity i)) • ·) hc
  simp only [smul_smul, zsign_mul_self, one_smul] at hc'
  have eR : cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) (mateN [i, j, i] [i, j, i]
      (dotsL [] i [up j, up i] r)) = zsign k (D.parity i * ((r / 2 : ℕ) : ZMod 2)) •
      cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) ((ddotsL i r).map (whL [dn i, dn j] [])) :=
    cl_mateN_dots_head Sc μ i [j, i] r
  have eS : cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) (mateN [i, j, i] [i, j, i]
      (dotsL [up i, up j] i [] s)) = zsign k (D.parity i * ((s / 2 : ℕ) : ZMod 2)) •
      cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) ((ddotsL i s).map (whL [] [dn j, dn i])) :=
    cl_mateN_dots_last Sc μ [i, j] i s
  have hc2 : cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) ((ddotsL i r).map (whL [dn i, dn j] [])) ≫
      cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) ((ddotsL i s).map (whL [] [dn j, dn i])) =
      cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) (dots3 i j s 0 r) := by
    have c1 : SChain (dns [i, j, i]) ((ddotsL i r).map (whL [dn i, dn j] [])) (dns [i, j, i]) :=
      (sChain_ddotsL i r).wh _ _ rfl rfl
    have c3 : SChain (dns [i, j, i]) ((ddotsL i s).map (whL [] [dn j, dn i])) (dns [i, j, i]) :=
      (sChain_ddotsL i s).wh _ _ rfl rfl
    rw [cl_comp c1 c3]
    simp [dots3, ddotsL]
  rw [← hc', ← cl_comp (sChain_mateN hR) (sChain_mateN hS), eR, eS, Linear.smul_comp,
    Linear.comp_smul, smul_smul, smul_smul, hc2, ← zsign_add, ← zsign_add, add_assoc]

variable (Sc) in
/-- The mate of the correction terms of (1.9) with `s`. -/
theorem cl_mate_braid_sterm (μ : X) (i j : I) (r q s : ℕ) :
    cl D Sc μ (dns [i, j, i]) (dns [i, j, i])
        (mateN [i, j, i] [i, j, i] (dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q ++
          dotsL [] i [up j, up i] r)) =
      zsign k ((s : ZMod 2) * D.parity i * ((q : ZMod 2) * D.parity j) +
          (s : ZMod 2) * D.parity i * ((r : ZMod 2) * D.parity i) +
          (q : ZMod 2) * D.parity j * ((r : ZMod 2) * D.parity i) +
          (D.parity i * ((r / 2 : ℕ) : ZMod 2) + D.parity j * ((q / 2 : ℕ) : ZMod 2) +
            D.parity i * ((s / 2 : ℕ) : ZMod 2))) •
        cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) (dots3 i j s q r) := by
  have hS : SChain (ups [i, j, i]) (dotsL [up i, up j] i [] s) (ups [i, j, i]) :=
    sChain_dotsL [up i, up j] i [] s
  have hQ : SChain (ups [i, j, i]) (dotsL [up i] j [up i] q) (ups [i, j, i]) :=
    sChain_dotsL [up i] j [up i] q
  have hR : SChain (ups [i, j, i]) (dotsL [] i [up j, up i] r) (ups [i, j, i]) :=
    sChain_dotsL [] i [up j, up i] r
  rw [cl_mateN_comp3 Sc μ hS hQ hR, parsum_dotsL, parsum_dotsL, parsum_dotsL]
  have eR : cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) (mateN [i, j, i] [i, j, i]
      (dotsL [] i [up j, up i] r)) = zsign k (D.parity i * ((r / 2 : ℕ) : ZMod 2)) •
      cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) ((ddotsL i r).map (whL [dn i, dn j] [])) :=
    cl_mateN_dots_head Sc μ i [j, i] r
  have eS : cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) (mateN [i, j, i] [i, j, i]
      (dotsL [up i, up j] i [] s)) = zsign k (D.parity i * ((s / 2 : ℕ) : ZMod 2)) •
      cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) ((ddotsL i s).map (whL [] [dn j, dn i])) :=
    cl_mateN_dots_last Sc μ [i, j] i s
  have eQ : cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) (mateN [i, j, i] [i, j, i]
      (dotsL [up i] j [up i] q)) = zsign k (D.parity j * ((q / 2 : ℕ) : ZMod 2)) •
      cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) ((ddotsL j q).map (whL [dn i] [dn i])) := by
    have h1 := cl_mateN_whiskerL Sc μ [i] (w := [j, i]) (w' := [j, i]) (sChain_dotsL [] j [up i] q)
    have h0 : cl D Sc (wt D μ [dn i]) (dns [j, i]) (dns [j, i])
        (mateN [j, i] [j, i] (dotsL [] j [up i] q)) =
        zsign k (D.parity j * ((q / 2 : ℕ) : ZMod 2)) •
          cl D Sc (wt D μ [dn i]) (dns [j, i]) (dns [j, i]) ((ddotsL j q).map (whL [dn i] [])) :=
      cl_mateN_dots_head Sc _ j [i] q
    have h2 := cl_place (D := D) (Sc := Sc) μ [] [dn i] h0
    have e : ((ddotsL j q).map (whL [dn i] [])).map (whL [] [dn i]) =
        (ddotsL j q).map (whL [dn i] [dn i]) := by simp
    rw [e] at h2
    rw [show dotsL [up i] j [up i] q = (dotsL [] j [up i] q).map (whL (ups [i]) []) by
      simp [dotsL, whL]]
    exact h1.trans h2
  have hc2 : cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) ((ddotsL i r).map (whL [dn i, dn j] [])) ≫
      cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) ((ddotsL j q).map (whL [dn i] [dn i])) ≫
      cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) ((ddotsL i s).map (whL [] [dn j, dn i])) =
      cl D Sc μ (dns [i, j, i]) (dns [i, j, i]) (dots3 i j s q r) := by
    have c1 : SChain (dns [i, j, i]) ((ddotsL i r).map (whL [dn i, dn j] [])) (dns [i, j, i]) :=
      (sChain_ddotsL i r).wh _ _ rfl rfl
    have c2 : SChain (dns [i, j, i]) ((ddotsL j q).map (whL [dn i] [dn i])) (dns [i, j, i]) :=
      (sChain_ddotsL j q).wh _ _ rfl rfl
    have c3 : SChain (dns [i, j, i]) ((ddotsL i s).map (whL [] [dn j, dn i])) (dns [i, j, i]) :=
      (sChain_ddotsL i s).wh _ _ rfl rfl
    rw [cl_comp c2 c3, cl_comp c1 (c2.append c3)]
    simp [dots3, List.append_assoc]
  rw [eR, eS, eQ]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
  rw [hc2]
  congr 1
  simp only [zsign_add]
  ring

variable (Sc) in
theorem lemma33_eq9_eq_aux (i j : I) (ν : X) (hij : i ≠ j) :
    cl D Sc ν (dns [i, j, i]) (dns [i, j, i]) (lemma33_eq9_lhs i j i) -
        cl D Sc ν (dns [i, j, i]) (dns [i, j, i]) (lemma33_eq9_rhs i j i) =
      ∑ r ∈ Finset.range (D.dn i j),
          (zsign k (D.parity i * (((D.dn i j / 2 : ℕ) : ZMod 2) + r + 1)) * (Sc.t i j : k)) •
            cl D Sc ν (dns [i, j, i]) (dns [i, j, i]) (dots3 i j r 0 (D.dn i j - 1 - r)) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ r ∈ Finset.range p,
          (zsign k (D.parity i * (((p / 2 : ℕ) : ZMod 2) + r + 1) +
              D.parity j * ((q / 2 : ℕ) : ZMod 2)) * Sc.s i j p q) •
            cl D Sc ν (dns [i, j, i]) (dns [i, j, i]) (dots3 i j r q (p - 1 - r)) := by
  have hb : cl D Sc (wt D ν (dns [i, j, i])) (ups [i, j, i]) (ups [i, j, i])
      (crossL [] i j [up i] ++ crossL [up j] i i [] ++ crossL [] j i [up i]) =
      cl D Sc (wt D ν (dns [i, j, i])) (ups [i, j, i]) (ups [i, j, i])
          (crossL [up i] j i [] ++ crossL [] i i [up j] ++ crossL [up i] i j []) +
        ∑ s ∈ Finset.range (D.dn i j),
          (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
            cl D Sc (wt D ν (dns [i, j, i])) (ups [i, j, i]) (ups [i, j, i])
              (dotsL [up i, up j] i [] s ++ dotsL [] i [up j, up i] (D.dn i j - 1 - s)) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
          (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
            cl D Sc (wt D ν (dns [i, j, i])) (ups [i, j, i]) (ups [i, j, i])
              (dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q ++
                dotsL [] i [up j, up i] (p - 1 - s)) :=
    cl_braidEq Sc i j _ hij
  have h := congrArg (mateMap D Sc ν [i, j, i] [i, j, i]) hb
  simp only [map_add, map_smul, map_sum, mateMap_cl] at h
  rw [cl_mate_braid_lhs, cl_mate_braid_rhs] at h
  simp only [cl_mate_braid_tterm, cl_mate_braid_sterm, smul_smul] at h
  set σ : ZMod 2 := D.parity i * D.parity j * (D.parity i * D.parity i) +
    D.parity i * D.parity j * (D.parity j * D.parity i) +
    D.parity i * D.parity i * (D.parity j * D.parity i) with hσ
  have h' := congrArg (zsign k σ • ·) h
  simp only [smul_add, Finset.smul_sum, smul_smul, zsign_mul_self, one_smul] at h'
  rw [h', add_assoc, add_sub_cancel_left]
  have hpd := parity_mul_dn D i j
  congr 1
  · refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    obtain ⟨m, hm⟩ : ∃ m, D.dn i j = m + r + 1 := ⟨D.dn i j - 1 - r, by omega⟩
    rw [show D.dn i j - 1 - r = m by omega]
    congr 1
    refine zsign_aux3 _ _ _ _ _ ?_
    have hd : D.parity i * ((m : ZMod 2) + r + 1) = 0 := by
      rw [hm] at hpd; push_cast at hpd; exact hpd
    have := lemma33_sign (D.parity i) (D.parity j) m r _ _ _ (zmod2_floor_identity m r) hd
    rw [hm, hσ]
    linear_combination this
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    by_cases hs : Sc.s i j p q = 0
    · simp [hs]
    obtain ⟨hp, hq⟩ := Sc.parity_of_ne_zero hs
    obtain ⟨m, hm⟩ : ∃ m, p = m + r + 1 := ⟨p - 1 - r, by omega⟩
    rw [show p - 1 - r = m by omega]
    congr 1
    refine zsign_aux3 _ _ _ _ _ ?_
    have hd : D.parity i * ((m : ZMod 2) + r + 1) = 0 := by
      rw [hm] at hp; push_cast at hp; rw [mul_comm]; exact hp
    have := lemma33_sign (D.parity i) (D.parity j) m r _ _ _ (zmod2_floor_identity m r) hd
    rw [hm, hσ]
    linear_combination this + ((r : ZMod 2) * D.parity i + (m : ZMod 2) * D.parity i) * hq

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.3 (3.9), `i = k ≠ j`.** The term with `t` and `r + s = dᵢⱼ - 1` has
`s` dots on the right strand followed by `r` dots on the left strand; the term with `sᵢⱼ^{pq}`
has `s` dots on the right strand, then `q` dots on the middle strand, then `r` dots on the left
strand (`dots3`). -/
theorem lemma33_eq9_eq (i j : I) (ν : X) (hij : i ≠ j) :
    cl D Sc ν [dn i, dn j, dn i] [dn i, dn j, dn i] (lemma33_eq9_lhs i j i) -
        cl D Sc ν [dn i, dn j, dn i] [dn i, dn j, dn i] (lemma33_eq9_rhs i j i) =
      ∑ r ∈ Finset.range (D.dn i j),
          (zsign k (D.parity i * (((D.dn i j / 2 : ℕ) : ZMod 2) + r + 1)) * (Sc.t i j : k)) •
            cl D Sc ν [dn i, dn j, dn i] [dn i, dn j, dn i] (dots3 i j r 0 (D.dn i j - 1 - r)) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ r ∈ Finset.range p,
          (zsign k (D.parity i * (((p / 2 : ℕ) : ZMod 2) + r + 1) +
              D.parity j * ((q / 2 : ℕ) : ZMod 2)) * Sc.s i j p q) •
            cl D Sc ν [dn i, dn j, dn i] [dn i, dn j, dn i] (dots3 i j r q (p - 1 - r)) :=
  lemma33_eq9_eq_aux Sc i j ν hij

end OddMath.SKM
