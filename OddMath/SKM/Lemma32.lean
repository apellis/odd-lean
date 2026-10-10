/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.MateN

/-!
# The rotated quadratic relation (Brundan–Ellis, Lemma 3.2)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Lemma 3.2, relation
(3.7) (TeX label `noisy`): on `Fᵢ Fⱼ 1_λ`, `(-1)^{|i||j|}` times the composite of the downward
crossings `Fᵢ Fⱼ → Fⱼ Fᵢ → Fᵢ Fⱼ` (2.1) is `0` if `i = j`, `tᵢⱼ` if `dᵢⱼ = 0`, and otherwise
`(-1)^{|i|⌊dᵢⱼ/2⌋} tᵢⱼ x^{dᵢⱼ} ⊗ 1 + (-1)^{|j|⌊dⱼᵢ/2⌋} tⱼᵢ 1 ⊗ x^{dⱼᵢ}
 + ∑ (-1)^{|i|⌊p/2⌋+|j|⌊q/2⌋} sᵢⱼ^{pq} x^p ⊗ x^q`, with downward dots (2.2) and, in the last sum,
the dots on the right strand applied first (they are at the same height in the paper's picture).

The paper proves (3.7) by rotating (1.7). Here: the downward crossing is the mate of the upward
crossing (`dcrossL_eq_mateN`), mates compose contravariantly up to the sign `(-1)^{|A||B|}`
(`cl_mateN_comp`), so the left-hand side is the mate of the left-hand side of (1.7) for `(j, i)`;
the mate of dots on one strand is downward dots on the other side, with the sign of (2.2).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

/-! ## Mates as a linear map -/

variable (D Sc) in
/-- The mate `A ↦ mate(A)` as a `k`-linear map on 2-morphisms `E_w → E_{w'}`. -/
def mateMap (μ : X) (w w' : List I) :
    ((pres D Sc).obj (ob D (wt D μ (dns w')) (ups w)) ⟶
        (pres D Sc).obj (ob D (wt D μ (dns w')) (ups w'))) →ₗ[k]
      ((pres D Sc).obj (ob D μ (dns w')) ⟶ (pres D Sc).obj (ob D μ (dns w))) :=
  ctxL D Sc μ (dns w') (dns w) ((cupN w).map (whL [] (dns w'))) (dns w) (dns w')
    ((capN w').map (whL (dns w) [])) (ups w) (ups w')

theorem mateMap_cl (μ : X) (w w' : List I) (A : List (LayerData I)) :
    mateMap D Sc μ w w' (cl D Sc (wt D μ (dns w')) (ups w) (ups w') A) =
      cl D Sc μ (dns w') (dns w) (mateN w w' A) := by
  exact ctxL_cl (D := D) (Sc := Sc) μ (u := dns w) (v := dns w') (s := ups w) (t := ups w')
    ((sChain_cupN w).wh [] (dns w') (by simp) rfl) ((sChain_capN w').wh (dns w) [] (by simp) (by simp)) A

variable (Sc) in
/-- The mate of the identity is the identity (the zigzag relation). -/
theorem cl_mateN_nil (μ : X) (w : List I) :
    cl D Sc μ (dns w) (dns w) (mateN w w []) = cl D Sc μ (dns w) (dns w) [] := by
  simpa [mateN, mateB] using zigF_N Sc w μ

/-! ## Mates of dots -/

/-- Placement of an equation between the strands `u` and `v`. -/
theorem cl_place (μ : X) (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)}
    {c : k} (E : cl D Sc (wt D μ v) s t A = c • cl D Sc (wt D μ v) s t B) :
    cl D Sc μ (u ++ s ++ v) (u ++ t ++ v) (A.map (whL u v)) =
      c • cl D Sc μ (u ++ s ++ v) (u ++ t ++ v) (B.map (whL u v)) := by
  rw [← plcL_cl, E, map_smul, plcL_cl]

variable (Sc) in
/-- The mate of `n` upward dots is `(-1)^{|i|⌊n/2⌋}` times `n` downward dots ((2.2)). -/
theorem cl_mateL_dots (ν : X) (i : I) (n : ℕ) :
    cl D Sc ν [dn i] [dn i] (mateL i (dotsL [] i [] n)) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) • cl D Sc ν [dn i] [dn i] (ddotsL i n) := by
  rw [cl_ddotsL, cl_ddot_pow, smul_smul, zsign_mul_self, one_smul]

variable (Sc) in
/-- The mate of dots on the first strand of `j :: v` is downward dots on the last strand. -/
theorem cl_mateN_dots_head (μ : X) (j : I) (v : List I) (n : ℕ) :
    cl D Sc μ (dns (j :: v)) (dns (j :: v)) (mateN (j :: v) (j :: v) (dotsL [] j (ups v) n)) =
      zsign k (D.parity j * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc μ (dns (j :: v)) (dns (j :: v)) ((ddotsL j n).map (whL (dns v) [])) := by
  have h1 := cl_mateN_whiskerR Sc μ (w := [j]) (w' := [j]) v (sChain_dotsL [] j [] n)
  have h2 := cl_place (D := D) (Sc := Sc) μ (dns v) [] (cl_mateL_dots Sc (wt D μ []) j n)
  rw [show [j] ++ v = j :: v from rfl, mateN_one] at h1
  rw [List.append_nil, ← dns_cons] at h2
  rw [show dotsL [] j (ups v) n = (dotsL [] j [] n).map (whL [] (ups v)) by simp [dotsL, whL]]
  exact h1.trans h2

variable (Sc) in
/-- The mate of dots on the last strand of `u ++ [i]` is downward dots on the first strand. -/
theorem cl_mateN_dots_last (μ : X) (u : List I) (i : I) (n : ℕ) :
    cl D Sc μ (dns (u ++ [i])) (dns (u ++ [i]))
        (mateN (u ++ [i]) (u ++ [i]) (dotsL (ups u) i [] n)) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc μ (dns (u ++ [i])) (dns (u ++ [i])) ((ddotsL i n).map (whL [] (dns u))) := by
  have h1 := cl_mateN_whiskerL Sc μ u (w := [i]) (w' := [i]) (sChain_dotsL [] i [] n)
  have h2 := cl_place (D := D) (Sc := Sc) μ [] (dns u) (cl_mateL_dots Sc (wt D μ (dns u)) i n)
  rw [mateN_one] at h1
  rw [List.nil_append, show [dn i] ++ dns u = dns [i] ++ dns u from rfl, ← dns_append] at h2
  rw [show dotsL (ups u) i [] n = (dotsL [] i [] n).map (whL (ups u) []) by simp [dotsL, whL]]
  exact h1.trans h2

/-! ## Lemma 3.2 -/

theorem zsign_mul_mul_self (p : ZMod 2) : zsign k p * zsign k (p * p) = 1 := by
  rw [zmod2_mul_self, zsign_mul_self]

/-- The scalars `sⱼᵢ^{pq}` vanish unless `p|j|` is even. -/
theorem Scalars.s_mul_zsign (i j : I) (p q : ℕ) (x : ZMod 2) :
    Sc.s j i p q * zsign k ((p : ZMod 2) * D.parity j * x) = Sc.s j i p q := by
  by_cases hs : Sc.s j i p q = 0
  · rw [hs, zero_mul]
  · rw [(Sc.parity_of_ne_zero hs).1, zero_mul, zsign_zero, mul_one]

variable (Sc) in
/-- The left-hand side of (3.7) is the mate of the left-hand side of (1.7) for `(j, i)`. -/
theorem lemma32_mate (i j : I) (ν : X) :
    zsign k (D.parity i * D.parity j) •
        cl D Sc ν (dns [j, i]) (dns [j, i]) (dcrossL i j ++ dcrossL j i) =
      mateMap D Sc ν [j, i] [j, i]
        (cl D Sc (wt D ν (dns [j, i])) (ups [j, i]) (ups [j, i])
          (crossL [] j i [] ++ crossL [] i j [])) := by
  have hτ : ∀ a b : I, SChain (ups [a, b]) (crossL [] a b []) (ups [b, a]) := fun a b => by
    simp [crossL, Shape.dom, Shape.cod]
  rw [mateMap_cl, dcrossL_eq_mateN, dcrossL_eq_mateN,
    cl_mateN_comp Sc ν (w₀ := [j, i]) (w₁ := [i, j]) (w₂ := [j, i]) (hτ i j) (hτ j i), smul_smul]
  simp only [crossL, parsum_cons, parsum_nil, Shape.parity, add_zero]
  rw [mul_comm (D.parity j) (D.parity i), zsign_mul_mul_self, one_smul]

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.2 (3.7), `i = j`.** -/
theorem lemma32_eq (i : I) (ν : X) :
    cl D Sc ν [dn i, dn i] [dn i, dn i] (dcrossL i i ++ dcrossL i i) = 0 := by
  have hq : cl D Sc (wt D ν (dns [i, i])) (ups [i, i]) (ups [i, i])
      (crossL [] i i [] ++ crossL [] i i []) = 0 := cl_quadEq Sc i _
  have h := lemma32_mate Sc i i ν
  rw [hq, map_zero] at h
  have h' := congrArg (zsign k (D.parity i * D.parity i) • ·) h
  simp only [smul_smul, zsign_mul_self, one_smul, smul_zero] at h'
  exact h'

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.2 (3.7), `dᵢⱼ = 0`.** -/
theorem lemma32_zero (i j : I) (ν : X) (hij : i ≠ j) (hd : D.d i j = 0) :
    zsign k (D.parity i * D.parity j) •
        cl D Sc ν [dn i, dn j] [dn i, dn j] (dcrossL i j ++ dcrossL j i) =
      (Sc.t i j : k) • cl D Sc ν [dn i, dn j] [dn i, dn j] [] := by
  have hq : cl D Sc (wt D ν (dns [j, i])) (ups [j, i]) (ups [j, i])
      (crossL [] j i [] ++ crossL [] i j []) =
      (Sc.t j i : k) • cl D Sc (wt D ν (dns [j, i])) (ups [j, i]) (ups [j, i]) [] :=
    cl_quadZero Sc j i _ (Ne.symm hij) ((D.d_eq_zero_iff i j).1 hd)
  have h := lemma32_mate Sc i j ν
  rw [hq, map_smul, mateMap_cl, cl_mateN_nil, ← Sc.t_symm_of_d_eq_zero i j hd] at h
  exact h

variable (Sc) in
theorem lemma32_ne_aux (i j : I) (ν : X) (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    zsign k (D.parity i * D.parity j) •
        cl D Sc ν (dns [j, i]) (dns [j, i]) (dcrossL i j ++ dcrossL j i) =
      (zsign k (D.parity i * ((D.dn i j / 2 : ℕ) : ZMod 2)) * Sc.t i j) •
          cl D Sc ν (dns [j, i]) (dns [j, i]) ((ddotsL i (D.dn i j)).map (whL [] [dn j])) +
        (zsign k (D.parity j * ((D.dn j i / 2 : ℕ) : ZMod 2)) * Sc.t j i) •
          cl D Sc ν (dns [j, i]) (dns [j, i]) ((ddotsL j (D.dn j i)).map (whL [dn i] [])) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
          (zsign k (D.parity i * ((p / 2 : ℕ) : ZMod 2) + D.parity j * ((q / 2 : ℕ) : ZMod 2)) *
              Sc.s i j p q) •
            cl D Sc ν (dns [j, i]) (dns [j, i])
              ((ddotsL j q).map (whL [dn i] []) ++ (ddotsL i p).map (whL [] [dn j])) := by
  have hd' : D.d j i ≠ 0 := fun h => hd ((D.d_eq_zero_iff j i).1 h)
  have hq : cl D Sc (wt D ν (dns [j, i])) (ups [j, i]) (ups [j, i])
      (crossL [] j i [] ++ crossL [] i j []) =
      (Sc.t j i : k) • cl D Sc (wt D ν (dns [j, i])) (ups [j, i]) (ups [j, i])
          (dotsL [] j [up i] (D.dn j i)) +
        (Sc.t i j : k) • cl D Sc (wt D ν (dns [j, i])) (ups [j, i]) (ups [j, i])
          (dotsL [up j] i [] (D.dn i j)) +
        ∑ p ∈ Finset.Ioo 0 (D.dn j i), ∑ q ∈ Finset.Ioo 0 (D.dn i j),
          Sc.s j i p q • cl D Sc (wt D ν (dns [j, i])) (ups [j, i]) (ups [j, i])
            (dotsL [up j] i [] q ++ dotsL [] j [up i] p) :=
    cl_quadNe Sc j i _ (Ne.symm hij) hd'
  have h := lemma32_mate Sc i j ν
  rw [hq] at h
  simp only [map_add, map_smul, map_sum, mateMap_cl] at h
  refine h.trans ?_
  have hL : cl D Sc ν (dns [j, i]) (dns [j, i]) (mateN [j, i] [j, i] (dotsL [] j [up i] (D.dn j i))) =
      zsign k (D.parity j * ((D.dn j i / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν (dns [j, i]) (dns [j, i]) ((ddotsL j (D.dn j i)).map (whL [dn i] [])) :=
    cl_mateN_dots_head Sc ν j [i] (D.dn j i)
  have hR : ∀ n, cl D Sc ν (dns [j, i]) (dns [j, i]) (mateN [j, i] [j, i] (dotsL [up j] i [] n)) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν (dns [j, i]) (dns [j, i]) ((ddotsL i n).map (whL [] [dn j])) := fun n =>
    cl_mateN_dots_last Sc ν [j] i n
  have hL' : ∀ n, cl D Sc ν (dns [j, i]) (dns [j, i]) (mateN [j, i] [j, i] (dotsL [] j [up i] n)) =
      zsign k (D.parity j * ((n / 2 : ℕ) : ZMod 2)) •
        cl D Sc ν (dns [j, i]) (dns [j, i]) ((ddotsL j n).map (whL [dn i] [])) := fun n =>
    cl_mateN_dots_head Sc ν j [i] n
  have hS : ∀ p q : ℕ, cl D Sc ν (dns [j, i]) (dns [j, i])
      (mateN [j, i] [j, i] (dotsL [up j] i [] q ++ dotsL [] j [up i] p)) =
      (zsign k ((p : ZMod 2) * D.parity j * ((q : ZMod 2) * D.parity i)) *
        (zsign k (D.parity j * ((p / 2 : ℕ) : ZMod 2)) *
          zsign k (D.parity i * ((q / 2 : ℕ) : ZMod 2)))) •
        cl D Sc ν (dns [j, i]) (dns [j, i])
          ((ddotsL j p).map (whL [dn i] []) ++ (ddotsL i q).map (whL [] [dn j])) := by
    intro p q
    have hA : SChain (ups [j, i]) (dotsL [] j [up i] p) (ups [j, i]) := sChain_dotsL [] j [up i] p
    have hB : SChain (ups [j, i]) (dotsL [up j] i [] q) (ups [j, i]) := sChain_dotsL [up j] i [] q
    have hc := cl_mateN_comp Sc ν hA hB
    rw [parsum_dotsL, parsum_dotsL] at hc
    have hc' := congrArg (zsign k ((p : ZMod 2) * D.parity j * ((q : ZMod 2) * D.parity i)) • ·) hc
    simp only [smul_smul, zsign_mul_self, one_smul] at hc'
    have hc2 : cl D Sc ν (dns [j, i]) (dns [j, i]) ((ddotsL j p).map (whL [dn i] [])) ≫
        cl D Sc ν (dns [j, i]) (dns [j, i]) ((ddotsL i q).map (whL [] [dn j])) =
        cl D Sc ν (dns [j, i]) (dns [j, i])
          ((ddotsL j p).map (whL [dn i] []) ++ (ddotsL i q).map (whL [] [dn j])) :=
      cl_comp ((sChain_ddotsL j p).wh [dn i] [] rfl rfl) ((sChain_ddotsL i q).wh [] [dn j] rfl rfl)
    rw [← hc', ← cl_comp (sChain_mateN hA) (sChain_mateN hB), hL' p, hR q, Linear.smul_comp,
      Linear.comp_smul, smul_smul, smul_smul, hc2]
    congr 1
    ring
  rw [hL, hR]
  simp only [hS, smul_smul]
  rw [Finset.sum_comm]
  congr 1
  · rw [add_comm]
    congr 1 <;> congr 1 <;> ring
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    congr 1
    rw [Sc.s_symm i j p q, zsign_add]
    have := Sc.s_mul_zsign i j q p ((p : ZMod 2) * D.parity i)
    linear_combination (zsign k (D.parity j * ((q / 2 : ℕ) : ZMod 2)) *
      zsign k (D.parity i * ((p / 2 : ℕ) : ZMod 2))) * this

variable (Sc) in
/-- **Brundan–Ellis, Lemma 3.2 (3.7), `i ≠ j`, `dᵢⱼ ≠ 0`.** The downward dots of the last sum
are `q` dots on the right strand followed by `p` dots on the left strand (the paper draws them
at the same height). -/
theorem lemma32_ne (i j : I) (ν : X) (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    zsign k (D.parity i * D.parity j) •
        cl D Sc ν [dn i, dn j] [dn i, dn j] (dcrossL i j ++ dcrossL j i) =
      (zsign k (D.parity i * ((D.dn i j / 2 : ℕ) : ZMod 2)) * Sc.t i j) •
          cl D Sc ν [dn i, dn j] [dn i, dn j] ((ddotsL i (D.dn i j)).map (whL [] [dn j])) +
        (zsign k (D.parity j * ((D.dn j i / 2 : ℕ) : ZMod 2)) * Sc.t j i) •
          cl D Sc ν [dn i, dn j] [dn i, dn j] ((ddotsL j (D.dn j i)).map (whL [dn i] [])) +
        ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
          (zsign k (D.parity i * ((p / 2 : ℕ) : ZMod 2) + D.parity j * ((q / 2 : ℕ) : ZMod 2)) *
              Sc.s i j p q) •
            cl D Sc ν [dn i, dn j] [dn i, dn j]
              ((ddotsL j q).map (whL [dn i] []) ++ (ddotsL i p).map (whL [] [dn j])) :=
  lemma32_ne_aux Sc i j ν hij hd

end OddMath.SKM
