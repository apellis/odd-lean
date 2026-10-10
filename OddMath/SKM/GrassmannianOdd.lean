/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Grassmannian
import OddMath.SKM.LeftDot

/-!
# Infinite Grassmannian relations, part 2: odd `i` (Brundan–Ellis, Proposition 5.1)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 5.1
(TeX label `IG`), the part of the proof for odd `i`: (5.9), (5.10), (5.7), (5.6).

* `oddBubble_mem`, `comp_mem_closedPar`: parities; (1.24) `oddBubble_sq`.
* (5.9): `eq_5_9` (from Proposition 4.1 (4.3) at `n = 1` and (2.3)); for all `N ∈ ℤ`:
  `eq_5_9_all` (the paper gets the range `N ≤ 0` from the Chevalley involution; here it is the
  mirrored induction from (5.8) and (5.10), `eq_5_9_step`).
* (5.10): `eq_5_10_pos` (from (4.4) at `n = 1`), `eq_5_10_step` (the paper's induction from (5.8)
  and (5.9)), `eq_5_10` for all `N ∈ ℤ`.
* (5.7): `eq_5_7_a`, `eq_5_7_b`.
* The key identity `bubble_key`: `∑_{r+s=t} (-1)^{|i|r} bubRs(s) ≫ bubLs(r) = 0` for `t > 0` and
  every `i` (used in the proofs of Corollaries 5.2 and 5.4: "(5.5)–(5.7) and (1.24)"); (5.6):
  `eq_5_6`.

Sums over consecutive pairs (`sum_Icc_pairs`) organize the parity splitting of the paper's
inductions.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- The odd bubble (2.18) has parity `|i|`. -/
theorem oddBubble_mem (i : I) (μ : X) : oddBubble cs i μ ∈ closedPar D Sc μ (D.parity i) := by
  rw [oddBubble]
  split_ifs
  · have := bubL_mem cs i μ (D.h i μ)
    rw [show D.h i μ + D.h i μ + 1 = 2 * D.h i μ + 1 by ring] at this
    refine Submodule.smul_mem _ _ ?_
    convert this using 2
    push_cast; rw [show (2 : ZMod 2) = 0 from rfl]; ring
  · have := bubR_mem cs i μ (-D.h i μ)
    rw [show -D.h i μ + D.h i μ + 1 = 1 by ring] at this
    refine Submodule.smul_mem _ _ ?_
    convert this using 2
    simp

/-- **Brundan–Ellis, (5.9)**: for odd `i`, `N = n + 1 > 0` and `N + ⟨hᵢ, λ⟩ + 1` odd, the bubble
with `N` dots on its right (upward) side is the bubble with `N - 1` dots followed by the odd
bubble. -/
theorem eq_5_9 (i : I) (μ : X) (hi : D.parity i = 1) (n : ℕ)
    (hpar : ((((n : ℤ) + 1) + D.h i μ + 1 : ℤ) : ZMod 2) = 1) :
    bubR cs i μ ((n : ℤ) + 1) = bubR cs i μ n ≫ oddBubble cs i μ := by
  have h2 : IsUnit (2 : k) := Sc.two_isUnit ⟨i, hi⟩
  have hR : bubR cs i μ ((n : ℤ) + 1) = hLM D Sc i μ n ≫ uRM D Sc i μ ≫ epsP cs i μ := by
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, bubR_nat, ← Category.assoc,
      hL_uR]
  have key := hR
  rw [lemma41_eq3_one_odd cs i μ hi, Preadditive.comp_add, Linear.comp_smul, Linear.comp_smul,
    ← Category.assoc, hL_dL, Linear.smul_comp, ← Category.assoc, ← bubR_nat,
    show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, smul_smul] at key
  have hs : zsign k ((D.h i μ : ℤ) : ZMod 2) * zsign k (D.parity i * (n : ZMod 2)) = -1 := by
    rw [hi, one_mul, ← zsign_add]
    have : ((D.h i μ : ℤ) : ZMod 2) + (n : ZMod 2) = 1 := by
      have h' := hpar
      push_cast at h'
      generalize ((D.h i μ : ℤ) : ZMod 2) = y at h' ⊢
      generalize (n : ZMod 2) = x at h' ⊢
      revert x y; decide
    rw [this]; simp [zsign]
  rw [hs, neg_one_smul] at key
  have : (2 : k) • bubR cs i μ ((n : ℤ) + 1) = (2 : k) • (bubR cs i μ n ≫ oddBubble cs i μ) := by
    rw [bubR_nat, Category.assoc, two_smul]
    nth_rewrite 1 [key]
    simp only [Category.assoc, hLM]
    abel
  exact (h2.smul_left_cancel).mp this


/-! ## Products of homogeneous closed 2-morphisms -/

theorem comp_mem_closedPar {μ : X} {p q : ZMod 2} {f g : (pres D Sc).obj (ob D μ []) ⟶
    (pres D Sc).obj (ob D μ [])} (hf : f ∈ closedPar D Sc μ p) (hg : g ∈ closedPar D Sc μ q) :
    f ≫ g ∈ closedPar D Sc μ (p + q) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨M, hM, rfl, rfl⟩ := hg
      rw [cl_comp hL hM]
      exact cl_mem_closedPar (hL.append hM) (parsum_append L M)
    | zero => simp
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ _ hx
  | zero => simp
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ _ hx

/-! ## Sums over consecutive pairs -/

theorem sum_Icc_pairs {M : Type*} [AddCommMonoid M] (f : ℤ → M) (A : ℤ) (L : ℕ) :
    ∑ x ∈ Icc A (A + 2 * L - 1), f x = ∑ j ∈ range L, (f (A + 2 * j) + f (A + 2 * j + 1)) := by
  induction L with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, add_zero, range_zero, sum_empty]
    rw [Icc_eq_empty (by omega), sum_empty]
  | succ L ih =>
    rw [sum_range_succ, ← ih]
    have e : Icc A (A + 2 * ((L + 1 : ℕ) : ℤ) - 1) =
        insert (A + 2 * L + 1) (insert (A + 2 * L) (Icc A (A + 2 * L - 1))) := by
      ext x; simp only [mem_insert, mem_Icc]; push_cast; omega
    rw [e, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
      sum_insert (by simp only [mem_Icc]; omega)]
    abel

/-! ## (5.10) for `n ≤ 0`, by induction from (5.8) and (5.9) -/

theorem bubL_base_odd (i : I) (μ : X) (hi : D.parity i = 1) (hh : D.h i μ ≤ 0) :
    bubL cs i μ (D.h i μ) = oddBubble cs i μ ≫ bubL cs i μ (D.h i μ - 1) := by
  rw [bubL_eq_c, Linear.comp_smul, Category.comp_id]
  rcases hh.lt_or_eq with hn | h0
  · rw [oddBubble, ite_eq_right (show ¬ 0 ≤ D.h i μ by omega),
      show -D.h i μ = (((-D.h i μ).toNat : ℕ) : ℤ) by omega, bubR_nat, epsP_of_neg cs hn,
      Linear.comp_smul, cl_comp (sChain_etaL i _) (sChain_dcapL i _), smul_smul, smul_smul,
      bubL, ite_eq_right (show ¬ 0 ≤ D.h i μ by omega),
      ite_eq_left (show D.h i μ - 1 < D.h i μ by omega)]
    congr 1
    · rw [hi, show D.h i μ + D.h i μ + 1 = 2 * D.h i μ + 1 by ring]
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add, one_mul]
      simp only [zsign, ite_true, neg_neg, one_mul]
      rw [mul_assoc, Units.mul_inv, mul_one]
  · rw [oddBubble, ite_eq_left (show 0 ≤ D.h i μ by omega), smul_smul, Units.mul_inv, one_smul]


theorem zcast_one_iff (x : ℤ) : ((x : ZMod 2) = 1) ↔ (2 : ℤ) ∣ x - 1 := by
  rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast
  constructor <;> intro h <;> omega

theorem zcast_zero_iff (x : ℤ) : ((x : ZMod 2) = 0) ↔ (2 : ℤ) ∣ x := by
  rw [← Int.cast_zero, ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast
  constructor <;> intro h <;> omega

/-- For odd `i`: if `s + ⟨hᵢ,λ⟩ + 1` is odd and `bubL r` is even, then
`bubL r ≫ bubR s = oddBubble ≫ bubL r ≫ bubR (s - 1)` (by (5.9), or both sides vanish). -/
theorem bubL_bubR_shift (i : I) (μ : X) (hi : D.parity i = 1) (hh : D.h i μ < 0) (r s : ℤ)
    (hr : (2 : ℤ) ∣ r + D.h i μ + 1) (hs : (2 : ℤ) ∣ s + D.h i μ) :
    bubL cs i μ r ≫ bubR cs i μ s = oddBubble cs i μ ≫ bubL cs i μ r ≫ bubR cs i μ (s - 1) := by
  rcases lt_or_ge s (-D.h i μ) with h1 | h1
  · have h2 : s < -D.h i μ - 1 := by omega
    rw [bubR_eq_zero_of_lt cs i μ h2,
      bubR_eq_zero_of_lt cs i μ (show s - 1 < -D.h i μ - 1 by omega)]
    simp
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, s = (n : ℤ) + 1 := ⟨(s - 1).toNat, by omega⟩
    subst hn
    rw [eq_5_9 cs i μ hi n ((zcast_one_iff _).2 (by omega)), add_sub_cancel_right,
      ← Category.assoc]
    have hm := comp_mem_closedPar (bubL_mem cs i μ r) (bubR_mem cs i μ (n : ℤ))
    rw [comm_of_mem hm (oddBubble_mem cs i μ)]
    convert one_smul k _
    rw [hi, one_mul, one_mul, (zcast_zero_iff _).2 hr, (zcast_zero_iff _).2 (by omega)]
    simp [zsign_zero]

/-- The induction step for (5.10) with `⟨hᵢ,λ⟩ < n ≤ 0` (Brundan–Ellis, proof of Proposition 5.1):
from (5.8) and (5.9). -/
theorem eq_5_10_step (i : I) (μ : X) (hi : D.parity i = 1) (N : ℤ) (hN0 : N ≤ 0)
    (hhN : D.h i μ < N) (hpar : (2 : ℤ) ∣ N + D.h i μ)
    (IH : ∀ r : ℤ, r < N → (2 : ℤ) ∣ r + D.h i μ →
      bubL cs i μ r = oddBubble cs i μ ≫ bubL cs i μ (r - 1)) :
    bubL cs i μ N = oddBubble cs i μ ≫ bubL cs i μ (N - 1) := by
  have hh : D.h i μ ≤ 0 := by omega
  obtain ⟨T, hT⟩ : ∃ T : ℕ, (T : ℤ) = N - D.h i μ := ⟨(N - D.h i μ).toNat, by omega⟩
  have E := ig_hneg cs i μ hh T
  rw [show -(((-D.h i μ).toNat : ℕ) : ℤ) - 1 = D.h i μ - 1 by omega] at E
  obtain ⟨F, hF⟩ : ∃ F : ℤ → ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])),
      ∀ r, F r = bubL cs i μ r ≫ bubR cs i μ ((T : ℤ) - 1 - r) := ⟨_, fun _ => rfl⟩
  simp only [← hF] at E
  set L : ℕ := (N - 2 * D.h i μ).toNat + 1 with hL
  have E2 : ∑ r ∈ Icc (D.h i μ - 1) (D.h i μ - 1 + 2 * L - 1), isg k (D.parity i) r • F r = 0 := by
    rw [← E]
    symm
    apply sum_subset
    · intro r hr; rw [mem_Icc] at hr ⊢; omega
    · intro r hr hr'
      rw [mem_Icc] at hr hr'
      have : (T : ℤ) - 1 - r < -D.h i μ - 1 := by omega
      rw [hF, bubR_eq_zero_of_lt cs i μ this, Limits.comp_zero, smul_zero]
  rw [sum_Icc_pairs] at E2
  have hisg : ∀ j : ℕ, isg k (D.parity i) (D.h i μ - 1 + 2 * j) • F (D.h i μ - 1 + 2 * j) +
      isg k (D.parity i) (D.h i μ - 1 + 2 * j + 1) • F (D.h i μ - 1 + 2 * j + 1) =
      isg k (D.parity i) (D.h i μ) • (F (D.h i μ + 2 * j) - (oddBubble cs i μ ≫ bubL cs i μ (D.h i μ + 2 * j - 1) ≫
        bubR cs i μ ((T : ℤ) - 1 - (D.h i μ + 2 * j)))) := by
    intro j
    have e1 : isg k (D.parity i) (D.h i μ - 1 + 2 * j) = -isg k (D.parity i) (D.h i μ) := by
      rw [isg_congr _ (n := D.h i μ + (-1)) ⟨j, by ring⟩, isg_add]
      simp [isg, hi, zsign]
    have e2 : isg k (D.parity i) (D.h i μ - 1 + 2 * j + 1) = isg k (D.parity i) (D.h i μ) :=
      isg_congr _ ⟨j, by ring⟩
    have e3 : F (D.h i μ - 1 + 2 * j) = oddBubble cs i μ ≫ bubL cs i μ (D.h i μ + 2 * j - 1) ≫
        bubR cs i μ ((T : ℤ) - 1 - (D.h i μ + 2 * j)) := by
      rw [hF, bubL_bubR_shift cs i μ hi (by omega) _ _ ⟨D.h i μ + j, by ring⟩ ⟨(N - D.h i μ - 2 * j) / 2 + 0, by omega⟩]
      congr 3 <;> ring
    rw [e1, e2, e3, show D.h i μ - 1 + 2 * (j : ℤ) + 1 = D.h i μ + 2 * j by ring, smul_sub, neg_smul]
    abel
  simp only [hisg, ← smul_sum] at E2
  have E3 := congrArg (isg k (D.parity i) (D.h i μ) • ·) E2
  simp only [smul_smul, isg_mul_self, one_smul, smul_zero] at E3
  obtain ⟨j0, hj0⟩ : ∃ j0 : ℕ, D.h i μ + 2 * (j0 : ℤ) = N := ⟨((N - D.h i μ) / 2).toNat, by omega⟩
  rw [sum_eq_single j0] at E3
  · rw [hj0, hF, show (T : ℤ) - 1 - N = -D.h i μ - 1 by omega, bubR_eq_c] at E3
    simp only [Linear.comp_smul, Category.comp_id] at E3
    rw [← smul_sub] at E3
    have hc : IsUnit ((↑(cs.c μ i)⁻¹ : k)) := Units.isUnit _
    exact sub_eq_zero.mp ((hc.smul_eq_zero).mp E3)
  · intro j _ hj
    rw [hF]
    rcases lt_or_gt_of_ne (show D.h i μ + 2 * (j : ℤ) ≠ N by omega) with hlt | hgt
    · rw [IH _ hlt ⟨D.h i μ + j, by ring⟩, Category.assoc, sub_self]
    · rw [bubR_eq_zero_of_lt cs i μ (show (T : ℤ) - 1 - (D.h i μ + 2 * j) < -D.h i μ - 1 by omega)]
      simp
  · intro hj; exfalso; exact hj (mem_range.2 (by omega))


/-- **Brundan–Ellis, (5.10) for `N > 0`**: for odd `i`, `N = n + 1` and `N + ⟨hᵢ, λ⟩ + 1` odd, the
bubble with `N` dots on its left (upward) side is the odd bubble followed by the bubble with
`N - 1` dots; from Proposition 4.1 (4.4) at `n = 1` (`lemma41_eq4_one_odd`) and (2.3). -/
theorem eq_5_10_pos (i : I) (μ : X) (hi : D.parity i = 1) (n : ℕ)
    (hpar : (2 : ℤ) ∣ (n : ℤ) + D.h i μ + 1) :
    bubL cs i μ ((n : ℤ) + 1) = oddBubble cs i μ ≫ bubL cs i μ n := by
  have h2 : IsUnit (2 : k) := Sc.two_isUnit ⟨i, hi⟩
  have key : bubL cs i μ ((n : ℤ) + 1) = etaP cs i μ ≫ uLM D Sc i μ ≫ eLM D Sc i μ n := by
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, bubL_nat, uL_eL]
  rw [← Category.assoc, lemma41_eq4_one_odd cs i μ hi, Preadditive.add_comp, Linear.smul_comp,
    Linear.smul_comp, Category.assoc, dR_eL, Linear.comp_smul, smul_smul, Category.assoc,
    ← bubL_nat, ← bubL_nat, show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring] at key
  have hs : zsign k ((D.h i μ : ℤ) : ZMod 2) * zsign k (D.parity i * (n : ZMod 2)) = -1 := by
    rw [hi, one_mul, ← zsign_add]
    have : ((D.h i μ : ℤ) : ZMod 2) + (n : ZMod 2) = 1 := by
      have h' := (zcast_one_iff ((n : ℤ) + D.h i μ)).2 (by omega)
      push_cast at h'
      rw [add_comm]; exact h'
    rw [this]; simp [zsign]
  rw [hs, neg_one_smul] at key
  have : (2 : k) • bubL cs i μ ((n : ℤ) + 1) = (2 : k) • (oddBubble cs i μ ≫ bubL cs i μ n) := by
    rw [two_smul]
    nth_rewrite 1 [key]
    abel
  exact (h2.smul_left_cancel).mp this

/-- **Brundan–Ellis, (5.10)** for all `N ∈ ℤ` with `N + ⟨hᵢ, λ⟩ + 1` odd (odd `i`). -/
theorem eq_5_10 (i : I) (μ : X) (hi : D.parity i = 1) (N : ℤ) (hpar : (2 : ℤ) ∣ N + D.h i μ) :
    bubL cs i μ N = oddBubble cs i μ ≫ bubL cs i μ (N - 1) := by
  suffices H : ∀ m : ℕ, ∀ N : ℤ, (N - D.h i μ + 2).toNat = m → (2 : ℤ) ∣ N + D.h i μ →
      bubL cs i μ N = oddBubble cs i μ ≫ bubL cs i μ (N - 1) from H _ N rfl hpar
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro N hm hpar
  rcases lt_or_ge 0 N with hN | hN
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = (n : ℤ) + 1 := ⟨(N - 1).toNat, by omega⟩
    rw [eq_5_10_pos cs i μ hi n (by omega), add_sub_cancel_right]
  rcases lt_trichotomy N (D.h i μ) with hlt | heq | hgt
  · rw [bubL_eq_zero_of_lt cs i μ (show N < D.h i μ - 1 by omega),
      bubL_eq_zero_of_lt cs i μ (show N - 1 < D.h i μ - 1 by omega)]
    simp
  · subst heq; exact bubL_base_odd cs i μ hi hN
  · refine eq_5_10_step cs i μ hi N hN hgt hpar fun r hr hpr => ?_
    exact IH (r - D.h i μ + 2).toNat (by omega) r rfl hpr


/-! ## (5.9) for all `N`, by the mirrored induction from (5.8) and (5.10) -/

theorem bubR_base_odd (i : I) (μ : X) (hi : D.parity i = 1) (hh : 0 ≤ D.h i μ) :
    bubR cs i μ (-D.h i μ) = bubR cs i μ (-D.h i μ - 1) ≫ oddBubble cs i μ := by
  rw [bubR_eq_c, Linear.smul_comp, Category.id_comp]
  rcases hh.lt_or_eq with hp | h0
  · have e1 : bubR cs i μ (-D.h i μ) =
        (-(isg k (D.parity i) (D.h i μ - ((D.h i μ - 1).toNat : ℕ))) * (↑(cs.c μ i)⁻¹ : k)) •
          cl D Sc μ [] [] (dcupL i (D.h i μ - 1).toNat ++ epsL i (D.h i μ).toNat) := by
      have := bubR_neg_of_lt cs i μ ((D.h i μ - 1).toNat) (by omega)
      rwa [show -(((D.h i μ - 1).toNat : ℕ) : ℤ) - 1 = -D.h i μ by omega] at this
    have e2 : bubL cs i μ (D.h i μ) = (cs.c μ i : k) •
        cl D Sc μ [] [] (dcupL i (D.h i μ - 1).toNat ++ epsL i (D.h i μ).toNat) := by
      conv_lhs => rw [show D.h i μ = (((D.h i μ).toNat : ℕ) : ℤ) by omega]
      rw [bubL_nat, etaP_of_pos cs hp, Linear.smul_comp,
        cl_comp (sChain_dcupL i _) (sChain_epsL i _)]
    rw [e1, oddBubble, ite_eq_left hh, e2, smul_smul, smul_smul]
    congr 1
    rw [show D.h i μ - (((D.h i μ - 1).toNat : ℕ) : ℤ) = 1 by omega, isg_one, hi]
    simp only [zsign, ite_true, neg_neg, one_mul]
    rw [mul_assoc, Units.inv_mul, mul_one]
  · have hc := oddBubble_consistent cs i μ hi h0.symm
    rw [oddBubble, ite_eq_left hh, ← h0, neg_zero, hc, smul_smul, Units.inv_mul, one_smul]

/-- The induction step for (5.9) with `-⟨hᵢ,λ⟩ < N ≤ 0`, mirroring `eq_5_10_step`. -/
theorem eq_5_9_step (i : I) (μ : X) (hi : D.parity i = 1) (N : ℤ)
    (hhN : -D.h i μ < N) (hpar : (2 : ℤ) ∣ N + D.h i μ)
    (IH : ∀ s : ℤ, s < N → (2 : ℤ) ∣ s + D.h i μ →
      bubR cs i μ s = bubR cs i μ (s - 1) ≫ oddBubble cs i μ) :
    bubR cs i μ N = bubR cs i μ (N - 1) ≫ oddBubble cs i μ := by
  rcases lt_or_ge 0 N with hN | hN
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = (n : ℤ) + 1 := ⟨(N - 1).toNat, by omega⟩
    rw [eq_5_9 cs i μ hi n ((zcast_one_iff _).2 (by omega)), add_sub_cancel_right]
  have hh : 0 ≤ D.h i μ := by omega
  obtain ⟨T, hT⟩ : ∃ T : ℕ, (T : ℤ) = N + D.h i μ := ⟨(N + D.h i μ).toNat, by omega⟩
  have E := ig_hpos cs i μ hh T
  rw [show -(((D.h i μ).toNat : ℕ) : ℤ) - 1 = -D.h i μ - 1 by omega] at E
  obtain ⟨F, hF⟩ : ∃ F : ℤ → ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])),
      ∀ s, F s = bubL cs i μ ((T : ℤ) - 1 - s) ≫ bubR cs i μ s := ⟨_, fun _ => rfl⟩
  simp only [← hF] at E
  set L : ℕ := (T : ℕ) + (D.h i μ).toNat + 1 with hL
  have E2 : ∑ s ∈ Icc (-D.h i μ - 1) (-D.h i μ - 1 + 2 * L - 1),
      isg k (D.parity i) s • F s = 0 := by
    rw [← E]
    symm
    apply sum_subset
    · intro s hs; rw [mem_Icc] at hs ⊢; omega
    · intro s hs hs'
      rw [mem_Icc] at hs hs'
      have : (T : ℤ) - 1 - s < D.h i μ - 1 := by omega
      rw [hF, bubL_eq_zero_of_lt cs i μ this, Limits.zero_comp, smul_zero]
  rw [sum_Icc_pairs] at E2
  have hisg : ∀ j : ℕ, isg k (D.parity i) (-D.h i μ - 1 + 2 * j) • F (-D.h i μ - 1 + 2 * j) +
      isg k (D.parity i) (-D.h i μ - 1 + 2 * j + 1) • F (-D.h i μ - 1 + 2 * j + 1) =
      isg k (D.parity i) (-D.h i μ) • (F (-D.h i μ + 2 * j) -
        bubL cs i μ ((T : ℤ) - 1 - (-D.h i μ + 2 * j)) ≫ bubR cs i μ (-D.h i μ + 2 * j - 1) ≫
          oddBubble cs i μ) := by
    intro j
    have e1 : isg k (D.parity i) (-D.h i μ - 1 + 2 * j) = -isg k (D.parity i) (-D.h i μ) := by
      rw [isg_congr _ (n := -D.h i μ + (-1)) ⟨j, by ring⟩, isg_add]
      simp [isg, hi, zsign]
    have e2 : isg k (D.parity i) (-D.h i μ - 1 + 2 * j + 1) = isg k (D.parity i) (-D.h i μ) :=
      isg_congr _ ⟨j, by ring⟩
    have e3 : F (-D.h i μ - 1 + 2 * j) = bubL cs i μ ((T : ℤ) - 1 - (-D.h i μ + 2 * j)) ≫
        bubR cs i μ (-D.h i μ + 2 * j - 1) ≫ oddBubble cs i μ := by
      rw [hF, eq_5_10 cs i μ hi _ (by omega)]
      have hm := comp_mem_closedPar (bubL_mem cs i μ ((T : ℤ) - 1 - (-D.h i μ - 1 + 2 * j) - 1))
        (bubR_mem cs i μ (-D.h i μ - 1 + 2 * j))
      rw [Category.assoc, comm_of_mem (oddBubble_mem cs i μ) hm]
      rw [show (T : ℤ) - 1 - (-D.h i μ - 1 + 2 * j) - 1 = (T : ℤ) - 1 - (-D.h i μ + 2 * j) by ring,
        show -D.h i μ + 2 * (j : ℤ) - 1 = -D.h i μ - 1 + 2 * j by ring, Category.assoc]
      convert one_smul k _
      rw [hi, one_mul, one_mul, (zcast_zero_iff ((T : ℤ) - 1 - (-D.h i μ + 2 * j) + D.h i μ + 1)).2
        ⟨(T + 2 * D.h i μ) / 2 - j, by omega⟩, (zcast_zero_iff _).2 ⟨j, by ring⟩]
      simp [zsign_zero]
    rw [e1, e2, e3, show -D.h i μ - 1 + 2 * (j : ℤ) + 1 = -D.h i μ + 2 * j by ring, smul_sub,
      neg_smul]
    abel
  simp only [hisg, ← smul_sum] at E2
  have E3 := congrArg (isg k (D.parity i) (-D.h i μ) • ·) E2
  simp only [smul_smul, isg_mul_self, one_smul, smul_zero] at E3
  obtain ⟨j0, hj0⟩ : ∃ j0 : ℕ, -D.h i μ + 2 * (j0 : ℤ) = N :=
    ⟨((N + D.h i μ) / 2).toNat, by omega⟩
  rw [sum_eq_single j0] at E3
  · rw [hj0, hF, show (T : ℤ) - 1 - N = D.h i μ - 1 by omega, bubL_eq_c] at E3
    simp only [Linear.smul_comp, Category.id_comp] at E3
    rw [← smul_sub] at E3
    have hc : IsUnit ((cs.c μ i : k)) := Units.isUnit _
    exact sub_eq_zero.mp ((hc.smul_eq_zero).mp E3)
  · intro j _ hj
    rw [hF]
    rcases lt_or_gt_of_ne (show -D.h i μ + 2 * (j : ℤ) ≠ N by omega) with hlt | hgt
    · rw [IH _ hlt ⟨j, by ring⟩, sub_self]
    · rw [bubL_eq_zero_of_lt cs i μ
        (show (T : ℤ) - 1 - (-D.h i μ + 2 * j) < D.h i μ - 1 by omega)]
      simp
  · intro hj; exfalso; exact hj (mem_range.2 (by omega))

/-- **Brundan–Ellis, (5.9)** for all `N ∈ ℤ` with `N + ⟨hᵢ, λ⟩ + 1` odd (odd `i`); the paper obtains
the negative range from the Chevalley involution. -/
theorem eq_5_9_all (i : I) (μ : X) (hi : D.parity i = 1) (N : ℤ) (hpar : (2 : ℤ) ∣ N + D.h i μ) :
    bubR cs i μ N = bubR cs i μ (N - 1) ≫ oddBubble cs i μ := by
  suffices H : ∀ m : ℕ, ∀ N : ℤ, (N + D.h i μ + 2).toNat = m → (2 : ℤ) ∣ N + D.h i μ →
      bubR cs i μ N = bubR cs i μ (N - 1) ≫ oddBubble cs i μ from H _ N rfl hpar
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro N hm hpar
  rcases lt_trichotomy N (-D.h i μ) with hlt | heq | hgt
  · rw [bubR_eq_zero_of_lt cs i μ (show N < -D.h i μ - 1 by omega),
      bubR_eq_zero_of_lt cs i μ (show N - 1 < -D.h i μ - 1 by omega)]
    simp
  · subst heq
    rcases le_or_gt 0 (D.h i μ) with hh | hh
    · exact bubR_base_odd cs i μ hi hh
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, -D.h i μ = (n : ℤ) + 1 := ⟨(-D.h i μ - 1).toNat, by omega⟩
      rw [hn, eq_5_9 cs i μ hi n ((zcast_one_iff _).2 (by omega)), add_sub_cancel_right]
  · refine eq_5_9_step cs i μ hi N hgt hpar fun s hs hps => ?_
    exact IH (s + D.h i μ + 2).toNat (by omega) s rfl hps


/-! ## (1.24), (5.7) -/

/-- **Brundan–Ellis, (1.24)**: the odd bubble squares to zero (`i` odd). -/
theorem oddBubble_sq (i : I) (μ : X) (hi : D.parity i = 1) :
    oddBubble cs i μ ≫ oddBubble cs i μ = 0 := by
  have h2 : IsUnit (2 : k) := Sc.two_isUnit ⟨i, hi⟩
  have E := comm_of_mem (oddBubble_mem cs i μ) (oddBubble_mem cs i μ)
  rw [hi, show (1 : ZMod 2) * 1 = 1 from rfl, show zsign k 1 = -1 by simp [zsign],
    neg_one_smul, eq_neg_iff_add_eq_zero, ← two_smul k] at E
  exact (h2.smul_eq_zero).mp E

/-- **Brundan–Ellis, Proposition 5.1, (5.7)**, first relation (`i` odd, all `n ∈ ℤ`):
`2n + 1 + *` dots on the counterclockwise bubble equal the odd bubble followed by `2n + *` dots. -/
theorem eq_5_7_a (i : I) (μ : X) (hi : D.parity i = 1) (n : ℤ) :
    bubLs cs i μ (2 * n + 1) = oddBubble cs i μ ≫ bubLs cs i μ (2 * n) := by
  rw [bubLs, bubLs, eq_5_10 cs i μ hi _ ⟨n + D.h i μ, by ring⟩]
  congr 2; ring

/-- **Brundan–Ellis, Proposition 5.1, (5.7)**, second relation (`i` odd, all `n ∈ ℤ`). -/
theorem eq_5_7_b (i : I) (μ : X) (hi : D.parity i = 1) (n : ℤ) :
    bubRs cs i μ (2 * n + 1) = oddBubble cs i μ ≫ bubRs cs i μ (2 * n) := by
  rw [bubRs, bubRs, eq_5_9_all cs i μ hi _ ⟨n, by ring⟩,
    comm_of_mem (bubR_mem cs i μ _) (oddBubble_mem cs i μ)]
  rw [hi, one_mul, (zcast_zero_iff _).2 ⟨n, by ring⟩, zero_mul, zsign_zero, one_smul]
  congr 2; ring

/-- For odd `i`, a counterclockwise bubble with an odd number `x + 1 - ⟨hᵢ,λ⟩`... of `+ *` dots
followed by a clockwise bubble with an odd number of `+ *` dots vanishes (two odd bubbles
appear, (1.24)). -/
theorem bubL_bubR_odd_odd (i : I) (μ : X) (hi : D.parity i = 1) (x y : ℤ)
    (hx : (2 : ℤ) ∣ x + D.h i μ) (hy : (2 : ℤ) ∣ y + D.h i μ) :
    bubL cs i μ x ≫ bubR cs i μ y = 0 := by
  rw [eq_5_10 cs i μ hi x hx, eq_5_9_all cs i μ hi y hy]
  simp only [Category.assoc]
  have hm := comp_mem_closedPar (bubL_mem cs i μ (x - 1)) (bubR_mem cs i μ (y - 1))
  rw [← Category.assoc (bubL cs i μ (x - 1)), comm_of_mem hm (oddBubble_mem cs i μ),
    hi, one_mul, one_mul, (zcast_zero_iff (x - 1 + D.h i μ + 1)).2 (by omega),
    (zcast_zero_iff (y - 1 + D.h i μ + 1)).2 (by omega), add_zero, zero_mul, zsign_zero,
    one_smul, ← Category.assoc, oddBubble_sq cs i μ hi, Limits.zero_comp]


/-! ## The key identity: `∑_{r+s=t} (-1)^{|i|r} bubRs(s) ≫ bubLs(r) = 0` -/

/-- A clockwise bubble below a counterclockwise one equals the two in the opposite order (the
super interchange sign is trivial, or both products vanish by (1.24)). -/
theorem bubRs_bubLs (i : I) (μ : X) (r s : ℤ) :
    bubRs cs i μ s ≫ bubLs cs i μ r =
      bubL cs i μ (r + D.h i μ - 1) ≫ bubR cs i μ (s - D.h i μ - 1) := by
  rw [bubRs, bubLs, comm_of_mem (bubR_mem cs i μ _) (bubL_mem cs i μ _),
    show s - D.h i μ - 1 + D.h i μ + 1 = s by ring, show r + D.h i μ - 1 + D.h i μ + 1 =
      r + 2 * D.h i μ by ring]
  rcases zmod2_cases (D.parity i) with ha | ha
  · rw [ha]; simp [zsign_zero]
  · by_cases hrs : (2 : ℤ) ∣ r - 1 ∧ (2 : ℤ) ∣ s - 1
    · rw [bubL_bubR_odd_odd cs i μ ha _ _ (by omega) (by omega), smul_zero]
    · convert one_smul k _
      rw [ha, one_mul, one_mul]
      rcases not_and_or.mp hrs with h1 | h1
      · rw [(zcast_zero_iff (r + 2 * D.h i μ)).2 (by omega), mul_zero, zsign_zero]
      · rw [(zcast_zero_iff s).2 (by omega), zero_mul, zsign_zero]

theorem sum_hpos (i : I) (μ : X) (hh : 0 ≤ D.h i μ) (t : ℕ) (ht : 0 < t) :
    ∑ r ∈ range (t + 1), isg k (D.parity i) ((t : ℤ) - r - D.h i μ - 1) •
      (bubL cs i μ ((r : ℤ) + D.h i μ - 1) ≫ bubR cs i μ ((t : ℤ) - r - D.h i μ - 1)) = 0 := by
  obtain ⟨T, rfl⟩ : ∃ T, t = T + 1 := ⟨t - 1, by omega⟩
  have := ig_hpos cs i μ hh T
  have e : ∀ r ∈ range (T + 1 + 1), isg k (D.parity i) (((T + 1 : ℕ) : ℤ) - r - D.h i μ - 1) •
      (bubL cs i μ ((r : ℤ) + D.h i μ - 1) ≫ bubR cs i μ (((T + 1 : ℕ) : ℤ) - r - D.h i μ - 1)) =
      (fun s => isg k (D.parity i) s • (bubL cs i μ ((T:ℤ) - 1 - s) ≫ bubR cs i μ s))
        ((fun r : ℕ => (T : ℤ) - r - D.h i μ) r) := by
    intro r _
    simp only [show (T : ℤ) - 1 - ((T : ℤ) - r - D.h i μ) = (r : ℤ) + D.h i μ - 1 by ring,
      show ((T + 1 : ℕ) : ℤ) - r - D.h i μ - 1 = (T : ℤ) - r - D.h i μ by push_cast; ring]
  rw [sum_congr rfl e, ← sum_image
    (f := fun s => isg k (D.parity i) s • (bubL cs i μ ((T:ℤ) - 1 - s) ≫ bubR cs i μ s))
    (g := fun r : ℕ => (T : ℤ) - r - D.h i μ) (fun a _ b _ h => by beta_reduce at h; omega),
    ← this]
  apply sum_subset
  · intro s hs
    simp only [mem_image, mem_range] at hs
    obtain ⟨r, hr, rfl⟩ := hs
    rw [mem_Icc]; constructor <;> omega
  · intro s hs hns
    rw [mem_Icc] at hs
    simp only [mem_image, mem_range, not_exists, not_and] at hns
    rcases lt_or_ge s (-D.h i μ - 1) with h1 | h1
    · rw [bubR_eq_zero_of_lt cs i μ h1, Limits.comp_zero, smul_zero]
    · have : (T : ℤ) - 1 - s < D.h i μ - 1 := by
        by_contra hc
        exact hns ((T : ℤ) - s - D.h i μ).toNat (by omega) (by omega)
      rw [bubL_eq_zero_of_lt cs i μ this, Limits.zero_comp, smul_zero]

theorem sum_hneg (i : I) (μ : X) (hh : D.h i μ ≤ 0) (t : ℕ) (ht : 0 < t) :
    ∑ r ∈ range (t + 1), isg k (D.parity i) ((r : ℤ) + D.h i μ - 1) •
      (bubL cs i μ ((r : ℤ) + D.h i μ - 1) ≫ bubR cs i μ ((t : ℤ) - r - D.h i μ - 1)) = 0 := by
  obtain ⟨T, rfl⟩ : ∃ T, t = T + 1 := ⟨t - 1, by omega⟩
  have := ig_hneg cs i μ hh T
  have e : ∀ r ∈ range (T + 1 + 1), isg k (D.parity i) ((r : ℤ) + D.h i μ - 1) •
      (bubL cs i μ ((r : ℤ) + D.h i μ - 1) ≫ bubR cs i μ (((T + 1 : ℕ) : ℤ) - r - D.h i μ - 1)) =
      (fun x => isg k (D.parity i) x • (bubL cs i μ x ≫ bubR cs i μ ((T:ℤ) - 1 - x)))
        ((fun r : ℕ => (r : ℤ) + D.h i μ - 1) r) := by
    intro r _
    simp only [show (T : ℤ) - 1 - ((r : ℤ) + D.h i μ - 1) = ((T + 1 : ℕ) : ℤ) - r - D.h i μ - 1 by
      push_cast; ring]
  rw [sum_congr rfl e, ← sum_image
    (f := fun x => isg k (D.parity i) x • (bubL cs i μ x ≫ bubR cs i μ ((T:ℤ) - 1 - x)))
    (g := fun r : ℕ => (r : ℤ) + D.h i μ - 1) (fun a _ b _ h => by beta_reduce at h; omega),
    ← this]
  apply sum_subset
  · intro s hs
    simp only [mem_image, mem_range] at hs
    obtain ⟨r, hr, rfl⟩ := hs
    rw [mem_Icc]; constructor <;> omega
  · intro x hx hnx
    rw [mem_Icc] at hx
    simp only [mem_image, mem_range, not_exists, not_and] at hnx
    rcases lt_or_ge x (D.h i μ - 1) with h1 | h1
    · rw [bubL_eq_zero_of_lt cs i μ h1, Limits.zero_comp, smul_zero]
    · have : (T : ℤ) - 1 - x < -D.h i μ - 1 := by
        by_contra hc
        exact hnx (x - D.h i μ + 1).toNat (by omega) (by omega)
      rw [bubR_eq_zero_of_lt cs i μ this, Limits.comp_zero, smul_zero]

/-- **The key identity** behind (5.5)–(5.7) (Brundan–Ellis, proofs of Corollaries 5.2 and 5.4):
for `t > 0` and every `i`, `∑_{r+s=t, r,s ≥ 0} (-1)^{|i|r}` (clockwise bubble with `s + *` dots,
below) `≫` (counterclockwise bubble with `r + *` dots, above) `= 0`. -/
theorem bubble_key (i : I) (μ : X) (t : ℕ) (ht : 0 < t) :
    ∑ r ∈ range (t + 1), isg k (D.parity i) r •
      (bubRs cs i μ ((t : ℤ) - r) ≫ bubLs cs i μ r) = 0 := by
  simp only [bubRs_bubLs]
  rcases le_total 0 (D.h i μ) with hh | hh
  · have E := sum_hpos cs i μ hh t ht
    have hc : ∀ r : ℕ, isg k (D.parity i) r = isg k (D.parity i) ((t : ℤ) - D.h i μ - 1) *
        isg k (D.parity i) ((t : ℤ) - r - D.h i μ - 1) := fun r => by
      rw [← isg_add]; exact isg_congr _ (by omega)
    simp only [hc, ← smul_smul, ← smul_sum, E, smul_zero]
  · have E := sum_hneg cs i μ hh t ht
    have hc : ∀ r : ℕ, isg k (D.parity i) r = isg k (D.parity i) (D.h i μ - 1) *
        isg k (D.parity i) ((r : ℤ) + D.h i μ - 1) := fun r => by
      rw [← isg_add]; exact isg_congr _ (by omega)
    simp only [hc, ← smul_smul, ← smul_sum, E, smul_zero]

theorem sum_range_two_mul_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (t : ℕ) :
    ∑ r ∈ range (2 * t + 1), f r = ∑ r ∈ range (t + 1), f (2 * r) + ∑ r ∈ range t, f (2 * r + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun r => f (2 * r)) (t + 1), sum_range_succ (fun r => f (2 * r + 1)) t]
    rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring]
    abel

/-- **Brundan–Ellis, Proposition 5.1, (5.6)**: for odd `i` and `t > 0`,
`∑_{r+s=t, r,s ≥ 0}` (clockwise bubble with `2s + *` dots, below) `≫` (counterclockwise bubble
with `2r + *` dots, above) `= 0`. -/
theorem eq_5_6 (i : I) (μ : X) (hi : D.parity i = 1) (t : ℕ) (ht : 0 < t) :
    ∑ r ∈ range (t + 1), bubRs cs i μ (2 * ((t : ℤ) - r)) ≫ bubLs cs i μ (2 * r) = 0 := by
  have E := bubble_key cs i μ (2 * t) (by omega)
  rw [sum_range_two_mul_succ] at E
  have hodd : ∀ r ∈ range t, isg k (D.parity i) ((2 * r + 1 : ℕ) : ℤ) •
      (bubRs cs i μ (((2 * t : ℕ) : ℤ) - ((2 * r + 1 : ℕ) : ℤ)) ≫ bubLs cs i μ ((2 * r + 1 : ℕ) : ℤ))
        = 0 := by
    intro r hr
    rw [mem_range] at hr
    rw [bubRs_bubLs, bubL_bubR_odd_odd cs i μ hi _ _ (by push_cast; omega) (by push_cast; omega),
      smul_zero]
  rw [sum_eq_zero hodd, add_zero] at E
  rw [← E]
  refine sum_congr rfl fun r hr => ?_
  rw [isg_congr _ (n := 0) ⟨r, by push_cast; ring⟩, isg_zero, one_smul]
  congr 2; push_cast; ring

end OddMath.SKM
