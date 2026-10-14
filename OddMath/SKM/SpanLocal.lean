/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanLower
import OddMath.SKM.AlternativeBraid
import OddMath.SKM.PitchforkCup
import OddMath.SKM.Lemma33

/-!
# Local relations of `𝔘(𝔤)` modulo lower terms

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11: the relations of `𝔘(𝔤)` allow arbitrary
isotopies of diagrams modulo diagrams with fewer crossings. This file records the local relations
in that form: each relation between diagrams with `c` crossings holds modulo `LeL c'` with `c' < c`
(`OddMath.SKM.SpanLower`). The signs of the super interchange law and of the odd dot slides are
units `±1`, so they appear as factors `zsign`.

## Main results

* Dot slides, modulo diagrams without crossings: through the upward crossing (`dsUp0`, `dsUp1`;
  (1.8), Lemma 3.1 (3.1), (3.2)), through `σ` (`dsSigma0`, `dsSigma1`; (3.3), (3.4)) and through
  the downward crossing (`dsDn0`, `dsDn1`; (3.5), (3.6)) and through the leftward crossing
  (`dsLcross0`, `dsLcross1`; Proposition 4.1 (4.1), (4.2) for `i = j`; for `i ≠ j` these are
  exact, `lemma41_eq1_ne`, `lemma41_eq2_ne`).
* Reidemeister II: `r2Up` ((1.7)), `r2Dn` (the mate of (1.7)), `r2Sigma`, `r2Lcross` ((1.12)–(1.14),
  (2.12)): a double crossing lies in the span of diagrams without crossings.
* Reidemeister III: `r3Up` ((1.9)), `r3Dn` ((3.9)), `r3Mixed` ((3.8)), `r3Alt` (Proposition 7.6):
  the two sides agree modulo diagrams without crossings.
* Bubbles, `η'`, `ε'` are crossingless: `bubL_mem_leL`, `bubR_mem_leL`, `oddBubble_mem_leL`.
* Curls (Corollary 5.4, (5.18)–(5.21)): `curl_5_18` … `curl_5_21`, a curl lies in the span of
  diagrams without crossings.
* Pitchforks (Proposition 7.2, (7.5)): `pitchfork_cap`, `pitchfork_cup` as identities of extended
  diagrams with the same number of crossings ((2.4), (2.5) are identities of normal-form
  diagrams, `eq_2_4_a` …).

The leftward-cap dot slides (4.3), (4.4) are exact identities between crossingless diagrams; for
odd `i` they carry an odd-bubble term of the same (zero) crossing count, which a later step of the
spanning argument absorbs into the bubbles.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## Crossing counts of the named layer lists -/

@[simp] theorem ccnt_ddotsL (i : I) (n : ℕ) : ccnt (ddotsL i n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ccnt (ddotL i ++ (List.replicate n (ddotL i)).flatten) = 0
    rw [ccnt_append, show ccnt (ddotL i) = 0 by simp [ddotL, mateL, Shape.isCross], zero_add]
    exact ih

@[simp] theorem ccnt_cupN (w : List I) : ccnt (cupN w) = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [cupN, ih, Shape.isCross]

@[simp] theorem ccnt_capN (w : List I) : ccnt (capN w) = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [capN, ih, Shape.isCross]

@[simp] theorem ccnt_mateN (w w' : List I) (A : List (LayerData I)) :
    ccnt (mateN w w' A) = ccnt A := by
  simp [mateN, mateB]

theorem leL_comp0 {ν : X} {s t r : List (Letter I)}
    {f : (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)}
    {g : (pres D Sc).obj (ob D ν t) ⟶ (pres D Sc).obj (ob D ν r)}
    (hf : f ∈ LeL D Sc cs ν s t 0) (hg : g ∈ LeL D Sc cs ν t r 0) :
    f ≫ g ∈ LeL D Sc cs ν s r 0 :=
  leL_comp_le cs hf hg (by omega)

theorem id_mem_leL (ν : X) (s : List (Letter I)) (c : ℕ) : 𝟙 _ ∈ LeL D Sc cs ν s s c := by
  rw [← cl_nil]; exact cl_mem_leL cs (by simp)

/-! ## Dot slides through upward crossings ((1.8), Lemma 3.1 (3.1), (3.2)) -/

/-- `n` dots on the left incoming strand of `τ` slide to the right outgoing strand, modulo
diagrams without crossings. -/
theorem dsUp0 (ν : X) (i j : I) (n : ℕ) :
    cl D Sc ν [up i, up j] [up j, up i] (dotsL [] i [up j] n ++ crossL [] i j []) -
      zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [up i, up j] [up j, up i] (crossL [] i j [] ++ dotsL [up j] i [] n) ∈
      LeL D Sc cs ν [up i, up j] [up j, up i] 0 := by
  by_cases h : i = j
  · subst h
    rw [lemma31_eq1_eq]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (cl_mem_leL cs (by simp))
  · rw [lemma31_eq1_ne Sc i j ν h n, sub_self]; exact Submodule.zero_mem _

/-- `n` dots on the right outgoing strand of `τ` slide to the left incoming strand, modulo
diagrams without crossings. -/
theorem dsUp1 (ν : X) (i j : I) (n : ℕ) :
    cl D Sc ν [up i, up j] [up j, up i] (crossL [] i j [] ++ dotsL [] j [up i] n) -
      zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [up i, up j] [up j, up i] (dotsL [up i] j [] n ++ crossL [] i j []) ∈
      LeL D Sc cs ν [up i, up j] [up j, up i] 0 := by
  by_cases h : i = j
  · subst h
    rw [lemma31_eq2_eq]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (cl_mem_leL cs (by simp))
  · rw [lemma31_eq2_ne Sc i j ν h n, sub_self]; exact Submodule.zero_mem _

/-! ## Dot slides through `σ` and the downward crossing (Lemma 3.1 (3.3)–(3.6)) -/

/-- (3.3): upward dots slide through `σ : Eᵢ Fⱼ → Fⱼ Eᵢ`, modulo diagrams without crossings. -/
theorem dsSigma0 (ν : X) (i j : I) (n : ℕ) :
    cl D Sc ν [up i, dn j] [dn j, up i] (sigmaL j i ++ dotsL [dn j] i [] n) -
      zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [up i, dn j] [dn j, up i] (dotsL [] i [dn j] n ++ sigmaL j i) ∈
      LeL D Sc cs ν [up i, dn j] [dn j, up i] 0 := by
  by_cases h : i = j
  · subst h
    rw [lemma31_eq3_eq]
    exact Submodule.sum_mem _ fun s _ =>
      Submodule.smul_mem _ _ (cl_mem_leL cs (by simp [Shape.isCross]))
  · rw [lemma31_eq3_ne Sc i j ν h n, sub_self]; exact Submodule.zero_mem _

/-- (3.4): downward dots slide through `σ : Eᵢ Fⱼ → Fⱼ Eᵢ`, modulo diagrams without crossings. -/
theorem dsSigma1 (ν : X) (i j : I) (n : ℕ) :
    zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [up i, dn j] [dn j, up i] (sigmaL j i ++ (ddotsL j n).map (whL [] [up i])) -
      cl D Sc ν [up i, dn j] [dn j, up i] ((ddotsL j n).map (whL [up i] []) ++ sigmaL j i) ∈
      LeL D Sc cs ν [up i, dn j] [dn j, up i] 0 := by
  by_cases h : i = j
  · subst h
    rw [lemma31_eq4_eq]
    exact Submodule.sum_mem _ fun s _ =>
      Submodule.smul_mem _ _ (cl_mem_leL cs (by simp [Shape.isCross]))
  · rw [lemma31_eq4_ne Sc i j ν h n, sub_self]; exact Submodule.zero_mem _

/-- (3.5): downward dots on `Fⱼ` slide through the downward crossing `Fⱼ Fᵢ → Fᵢ Fⱼ`, modulo
diagrams without crossings. -/
theorem dsDn0 (ν : X) (i j : I) (n : ℕ) :
    zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [dn j, dn i] [dn i, dn j] (dcrossL j i ++ (ddotsL j n).map (whL [dn i] [])) -
      cl D Sc ν [dn j, dn i] [dn i, dn j] ((ddotsL j n).map (whL [] [dn i]) ++ dcrossL j i) ∈
      LeL D Sc cs ν [dn j, dn i] [dn i, dn j] 0 := by
  by_cases h : i = j
  · subst h
    rw [lemma31_eq5_eq]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (cl_mem_leL cs (by simp))
  · rw [lemma31_eq5_ne Sc i j ν h n, sub_self]; exact Submodule.zero_mem _

/-- (3.6): downward dots on `Fᵢ` slide through the downward crossing `Fⱼ Fᵢ → Fᵢ Fⱼ`, modulo
diagrams without crossings. -/
theorem dsDn1 (ν : X) (i j : I) (n : ℕ) :
    zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [dn j, dn i] [dn i, dn j] ((ddotsL i n).map (whL [dn j] []) ++ dcrossL j i) -
      cl D Sc ν [dn j, dn i] [dn i, dn j] (dcrossL j i ++ (ddotsL i n).map (whL [] [dn j])) ∈
      LeL D Sc cs ν [dn j, dn i] [dn i, dn j] 0 := by
  by_cases h : i = j
  · subst h
    rw [lemma31_eq6_eq]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (cl_mem_leL cs (by simp))
  · rw [lemma31_eq6_ne Sc i j ν h n, sub_self]; exact Submodule.zero_mem _

/-! ## Dot slides through the leftward crossing (Proposition 4.1 (4.1), (4.2)) -/

theorem cpow_mem_leL {ν : X} {s : List (Letter I)}
    {x : (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν s)} (hx : x ∈ LeL D Sc cs ν s s 0)
    (n : ℕ) : cpow x n ∈ LeL D Sc cs ν s s 0 := by
  induction n with
  | zero => exact id_mem_leL cs ν s 0
  | succ n ih => rw [cpow_succ]; exact leL_comp0 cs ih hx

theorem ccnt_ddotL (i : I) : ccnt (ddotL i) = 0 := by simp [ddotL, mateL, Shape.isCross]

/-- (4.1), `i = j`: downward dots slide through the leftward crossing, modulo diagrams without
crossings. -/
theorem dsLcross0 (μ : X) (i : I) (n : ℕ) :
    cpow (dLM D Sc i μ) n ≫ lcM D Sc i μ -
        zsign k (D.parity i * n) • (lcM D Sc i μ ≫ cpow (dRM D Sc i μ) n) ∈
      LeL D Sc cs μ [dn i, up i] [up i, dn i] 0 := by
  rw [lemma41_eq1 Sc cs]
  refine Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ ?_
  refine leL_comp0 cs (cpow_mem_leL cs (cl_mem_leL cs (by simp [ccnt_ddotL])) _) (leL_comp0 cs
    (epsP_mem_leL cs μ i 0) (leL_comp0 cs (etaP_mem_leL cs μ i 0)
      (cpow_mem_leL cs (cl_mem_leL cs (by simp [ccnt_ddotL])) _)))

/-- (4.2), `i = j`: upward dots slide through the leftward crossing, modulo diagrams without
crossings. -/
theorem dsLcross1 (μ : X) (i : I) (n : ℕ) :
    zsign k (D.parity i * n) • (cpow (uRM D Sc i μ) n ≫ lcM D Sc i μ) -
        lcM D Sc i μ ≫ cpow (uLM D Sc i μ) n ∈
      LeL D Sc cs μ [dn i, up i] [up i, dn i] 0 := by
  rw [lemma41_eq2 Sc cs]
  refine Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ ?_
  refine leL_comp0 cs (cpow_mem_leL cs (cl_mem_leL cs (by simp)) _) (leL_comp0 cs
    (epsP_mem_leL cs μ i 0) (leL_comp0 cs (etaP_mem_leL cs μ i 0)
      (cpow_mem_leL cs (cl_mem_leL cs (by simp)) _)))

/-! ## Reidemeister II -/

/-- (1.7): a double upward crossing lies in the span of diagrams without crossings. -/
theorem r2Up (ν : X) (i j : I) :
    cl D Sc ν [up i, up j] [up i, up j] (crossL [] i j [] ++ crossL [] j i []) ∈
      LeL D Sc cs ν [up i, up j] [up i, up j] 0 := by
  by_cases h : i = j
  · subst h; rw [cl_quadEq]; exact Submodule.zero_mem _
  · by_cases hd : D.d i j = 0
    · rw [cl_quadZero Sc i j ν h hd]; exact Submodule.smul_mem _ _ (cl_mem_leL cs (by simp))
    · rw [cl_quadNe Sc i j ν h hd]
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · exact Submodule.smul_mem _ _ (cl_mem_leL cs (by simp))
      · exact Submodule.smul_mem _ _ (cl_mem_leL cs (by simp))
      · exact Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ =>
          Submodule.smul_mem _ _ (cl_mem_leL cs (by simp))

/-- The mate (`mateMap`) of a 2-morphism with `c` crossings has `c` crossings. -/
theorem mateMap_leL (μ : X) (w w' : List I) {c : ℕ}
    {f : (pres D Sc).obj (ob D (wt D μ (dns w')) (ups w)) ⟶
      (pres D Sc).obj (ob D (wt D μ (dns w')) (ups w'))}
    (hf : f ∈ LeL D Sc cs (wt D μ (dns w')) (ups w) (ups w') c) :
    mateMap D Sc μ w w' f ∈ LeL D Sc cs μ (dns w') (dns w) c := by
  have h := ctxL_leL cs (μ := μ) (s₀ := dns w') (t₀ := dns w) (u := dns w) (v := dns w')
    (pre := (cupN w).map (whL [] (dns w'))) (post := (capN w').map (whL (dns w) [])) hf
  rw [ccnt_map_whL, ccnt_map_whL, ccnt_cupN, ccnt_capN, zero_add, add_zero] at h
  exact h

/-- The mate of (1.7): a double downward crossing lies in the span of diagrams without
crossings. -/
theorem r2Dn (ν : X) (i j : I) :
    cl D Sc ν [dn i, dn j] [dn i, dn j] (dcrossL i j ++ dcrossL j i) ∈
      LeL D Sc cs ν [dn i, dn j] [dn i, dn j] 0 := by
  have hA : SChain (ups [i, j]) (crossL [] i j []) (ups [j, i]) := ⟨rfl, rfl⟩
  have hB : SChain (ups [j, i]) (crossL [] j i []) (ups [i, j]) := ⟨rfl, rfl⟩
  have E := cl_mateN_comp Sc ν hA hB
  rw [← dcrossL_eq_mateN, ← dcrossL_eq_mateN, ← mateMap_cl] at E
  change cl D Sc ν [dn i, dn j] [dn i, dn j] _ = _ at E
  rw [E]
  exact Submodule.smul_mem _ _ (mateMap_leL cs ν [j, i] [j, i] (r2Up cs _ j i))

/-- (1.12)–(1.14), (2.12): `σ` followed by the leftward crossing lies in the span of diagrams
without crossings. -/
theorem r2Sigma (ν : X) (i j : I) :
    cl D Sc ν [up j, dn i] [up j, dn i] (sigmaL i j ++ lcrossL i j) ∈
      LeL D Sc cs ν [up j, dn i] [up j, dn i] 0 := by
  by_cases h : i = j
  · subst h
    rw [eq_2_12_a]
    exact Submodule.sub_mem _ (Submodule.sum_mem _ fun n _ => cl_mem_leL cs (by simp))
      (cl_mem_leL cs (by simp))
  · rw [cl_invNe₁ Sc i j ν h]; exact cl_mem_leL cs (by simp)

/-- (1.12)–(1.14), (2.12): the leftward crossing followed by `σ` lies in the span of diagrams
without crossings. -/
theorem r2Lcross (ν : X) (i j : I) :
    cl D Sc ν [dn i, up j] [dn i, up j] (lcrossL i j ++ sigmaL i j) ∈
      LeL D Sc cs ν [dn i, up j] [dn i, up j] 0 := by
  by_cases h : i = j
  · subst h
    rw [eq_2_12_b]
    exact Submodule.sub_mem _ (Submodule.sum_mem _ fun n _ => cl_mem_leL cs (by simp))
      (cl_mem_leL cs (by simp))
  · rw [cl_invNe₂ Sc i j ν h]; exact cl_mem_leL cs (by simp)

/-! ## Reidemeister III -/

/-- (1.9): the braid relation holds modulo diagrams without crossings. -/
theorem r3Up (ν : X) (i j k' : I) :
    cl D Sc ν [up i, up j, up k'] [up k', up j, up i]
        (crossL [] i j [up k'] ++ crossL [up j] i k' [] ++ crossL [] j k' [up i]) -
      cl D Sc ν [up i, up j, up k'] [up k', up j, up i]
        (crossL [up i] j k' [] ++ crossL [] i k' [up j] ++ crossL [up k'] i j []) ∈
      LeL D Sc cs ν [up i, up j, up k'] [up k', up j, up i] 0 := by
  by_cases h : i = k' ∧ i ≠ j
  · obtain ⟨rfl, hij⟩ := h
    rw [cl_braidEq Sc i j ν hij, add_assoc, add_sub_cancel_left]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (cl_mem_leL cs (by simp))
    · exact Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ =>
        Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (cl_mem_leL cs (by simp))
  · rw [cl_braid Sc i j k' ν h, sub_self]; exact Submodule.zero_mem _

/-- (3.9): the braid relation for three downward strands holds modulo diagrams without
crossings. -/
theorem r3Dn (ν : X) (i j k' : I) :
    cl D Sc ν [dn k', dn j, dn i] [dn i, dn j, dn k'] (lemma33_eq9_lhs i j k') -
      cl D Sc ν [dn k', dn j, dn i] [dn i, dn j, dn k'] (lemma33_eq9_rhs i j k') ∈
      LeL D Sc cs ν [dn k', dn j, dn i] [dn i, dn j, dn k'] 0 := by
  by_cases h : i = k' ∧ i ≠ j
  · obtain ⟨rfl, hij⟩ := h
    rw [lemma33_eq9_eq Sc i j ν hij]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.sum_mem _ fun s _ =>
        Submodule.smul_mem _ _ (cl_mem_leL cs (by simp [dots3]))
    · exact Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ =>
        Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (cl_mem_leL cs (by simp [dots3]))
  · rw [lemma33_eq9 Sc i j k' ν h, sub_self]; exact Submodule.zero_mem _

/-- (3.8): the braid relation with one downward strand holds modulo diagrams without
crossings. -/
theorem r3Mixed (ν : X) (i j k' : I) :
    cl D Sc ν [up j, up k', dn i] [dn i, up k', up j] (lemma33_eq8_lhs i j k') -
      cl D Sc ν [up j, up k', dn i] [dn i, up k', up j] (lemma33_eq8_rhs i j k') ∈
      LeL D Sc cs ν [up j, up k', dn i] [dn i, up k', up j] 0 := by
  by_cases h : i = k' ∧ i ≠ j
  · obtain ⟨rfl, hij⟩ := h
    rw [lemma33_eq8_eq Sc i j ν hij]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.sum_mem _ fun s _ =>
        Submodule.smul_mem _ _ (cl_mem_leL cs (by simp [term8, Shape.isCross]))
    · exact Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ =>
        Submodule.sum_mem _ fun s _ =>
          Submodule.smul_mem _ _ (cl_mem_leL cs (by simp [term8, Shape.isCross]))
  · rw [lemma33_eq8 Sc i j k' ν h, sub_self]; exact Submodule.zero_mem _

/-! ## Bubbles are crossingless -/

/-- The bubble `bubL` (Definition 2.3) is a linear combination of crossingless diagrams. -/
theorem bubL_mem_leL (μ : X) (i : I) (n : ℤ) : bubL cs i μ n ∈ LeL D Sc cs μ [] [] 0 := by
  unfold bubL
  split_ifs
  · exact leL_comp0 cs (etaP_mem_leL cs μ i 0) (cl_mem_leL cs (by simp))
  · exact Submodule.smul_mem _ _ (cl_mem_leL cs (by simp))
  · exact Submodule.smul_mem _ _ (id_mem_leL cs μ [] 0)
  · exact Submodule.zero_mem _

/-- The bubble `bubR` (Definition 2.3) is a linear combination of crossingless diagrams. -/
theorem bubR_mem_leL (μ : X) (i : I) (n : ℤ) : bubR cs i μ n ∈ LeL D Sc cs μ [] [] 0 := by
  unfold bubR
  split_ifs
  · exact leL_comp0 cs (cl_mem_leL cs (by simp)) (epsP_mem_leL cs μ i 0)
  · exact Submodule.smul_mem _ _ (cl_mem_leL cs (by simp))
  · exact Submodule.smul_mem _ _ (id_mem_leL cs μ [] 0)
  · exact Submodule.zero_mem _

/-- The odd bubble (2.18) is a linear combination of crossingless diagrams. -/
theorem oddBubble_mem_leL (μ : X) (i : I) : oddBubble cs i μ ∈ LeL D Sc cs μ [] [] 0 := by
  unfold oddBubble
  split_ifs
  · exact Submodule.smul_mem _ _ (bubL_mem_leL cs μ i _)
  · exact Submodule.smul_mem _ _ (bubR_mem_leL cs μ i _)

theorem lbub_mem_leL (μ : X) (i : I) {b : (pres D Sc).obj (ob D (wt D μ [up i]) []) ⟶
    (pres D Sc).obj (ob D (wt D μ [up i]) [])} (hb : b ∈ LeL D Sc cs (wt D μ [up i]) [] [] 0) :
    lbub i μ b ∈ LeL D Sc cs μ [up i] [up i] 0 :=
  plcL_leL cs (u := []) (v := [up i]) (s := []) (t := []) hb

theorem rbub_mem_leL (μ : X) (i : I) {b : (pres D Sc).obj (ob D (wt D μ []) []) ⟶
    (pres D Sc).obj (ob D (wt D μ []) [])} (hb : b ∈ LeL D Sc cs (wt D μ []) [] [] 0) :
    rbub i μ b ∈ LeL D Sc cs μ [up i] [up i] 0 :=
  plcL_leL cs (u := [up i]) (v := []) (s := []) (t := []) hb

/-! ## Proposition 7.6 modulo lower terms -/

/-- [BE2] Proposition 7.6: the alternative braid relation holds modulo diagrams without
crossings. -/
theorem r3Alt (μ : X) (i j a : I) :
    cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altL i j a) -
      cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altR i j a) ∈
      LeL D Sc cs μ [up j, dn i, up a] [up a, dn i, up j] 0 := by
  classical
  rw [AltBraid.prop_7_6 cs, add_sub_cancel_left]
  unfold AltBraid.altCorrection
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    refine Submodule.add_mem _ ?_ ?_
    · refine Submodule.sum_mem _ fun r _ => Submodule.sum_mem _ fun s _ =>
        Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
      refine leL_comp0 cs (cl_mem_leL cs (by simp)) (leL_comp0 cs
        (lbub_mem_leL cs μ i (bubR_mem_leL cs _ i _)) (leL_comp0 cs
          (plcL_etaP_mem_leL cs μ [] [up i] i 0) (leL_comp0 cs
            (cl_mem_leL cs (by simp)) (cl_mem_leL cs (by simp)))))
    · refine Submodule.sum_mem _ fun r _ => Submodule.sum_mem _ fun s _ =>
        Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
      refine leL_comp0 cs (cl_mem_leL cs (by simp)) (leL_comp0 cs
        (plcL_epsP_mem_leL cs μ [up i] [] i 0) (leL_comp0 cs
          (rbub_mem_leL cs μ i (bubL_mem_leL cs _ i _)) (leL_comp0 cs
            (cl_mem_leL cs (by simp)) (cl_mem_leL cs (by simp)))))
  · exact Submodule.zero_mem _

/-! ## Curls (Corollary 5.4) -/

theorem sChain_curl_5_18 (i : I) (n : ℕ) :
    SChain [up i] ([([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] n ++
      [([dn i], Shape.cross i i, [])]) [dn i, up i, up i] :=
  SChain.append (t' := [dn i, up i, up i])
    (SChain.append (t' := [dn i, up i, up i]) ⟨rfl, rfl⟩ (sChain_dotsL [dn i] i [up i] n))
    ⟨rfl, rfl⟩

/-- (5.18): the left curl with `n` dots on the loop before the crossing lies in the span of
diagrams without crossings. -/
theorem curl_5_18 (μ : X) (i : I) (n : ℕ) :
    xev cs μ [up i] [up i] (([([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] n ++
      [([dn i], Shape.cross i i, [])]).map ofL ++ [([], .lcap i, [up i])]) ∈
      LeL D Sc cs μ [up i] [up i] 0 := by
  rw [show xev cs μ [up i] [up i] _ = _ from
    xev_snoc cs μ ([], .lcap i, [up i]) (XChain.of_sChain (sChain_curl_5_18 i n)), xev_map_ofL]
  change cl D Sc μ [up i] [dn i, up i, up i] _ ≫
    plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i (wt D μ [up i])) ∈ _
  rw [eq_5_18]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _
    (leL_comp0 cs (lbub_mem_leL cs μ i (bubR_mem_leL cs _ i _)) (cl_mem_leL cs (by simp)))

theorem sChain_curl_5_19 (i : I) (n : ℕ) :
    SChain [up i] (curlLList i ++ dotsL [dn i] i [up i] n) [dn i, up i, up i] :=
  SChain.append (t' := [dn i, up i, up i]) ⟨rfl, rfl, rfl⟩ (sChain_dotsL [dn i] i [up i] n)

/-- (5.19): the left curl with `n` dots on the loop after the crossing lies in the span of
diagrams without crossings. -/
theorem curl_5_19 (μ : X) (i : I) (n : ℕ) :
    xev cs μ [up i] [up i] ((curlLList i ++ dotsL [dn i] i [up i] n).map ofL ++
      [([], .lcap i, [up i])]) ∈ LeL D Sc cs μ [up i] [up i] 0 := by
  rw [show xev cs μ [up i] [up i] _ = _ from
    xev_snoc cs μ ([], .lcap i, [up i]) (XChain.of_sChain (sChain_curl_5_19 i n)), xev_map_ofL]
  change cl D Sc μ [up i] [dn i, up i, up i] _ ≫
    plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i (wt D μ [up i])) ∈ _
  rw [eq_5_19]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _
    (leL_comp0 cs (cl_mem_leL cs (by simp)) (lbub_mem_leL cs μ i (bubR_mem_leL cs _ i _)))

/-- (5.20): the right curl with `n` dots on the loop after the crossing lies in the span of
diagrams without crossings. -/
theorem curl_5_20 (μ : X) (i : I) (n : ℕ) :
    xev cs μ [up i] [up i] (([up i], .lcup i, []) ::
      ([([], Shape.cross i i, [dn i])] ++ dotsL [up i] i [dn i] n ++
        [([up i], Shape.cap i, [])]).map ofL) ∈ LeL D Sc cs μ [up i] [up i] 0 := by
  rw [show xev cs μ [up i] [up i] (([up i], .lcup i, []) :: _) = _ from
    xev_cons_eq cs μ ([up i], .lcup i, []) _, xev_map_ofL]
  change reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i] _ ∈ _
  rw [eq_5_20]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _
    (leL_comp0 cs (cl_mem_leL cs (by simp)) (rbub_mem_leL cs μ i (bubL_mem_leL cs _ i _))))

/-- (5.21): the right curl with `n` dots on the loop before the crossing lies in the span of
diagrams without crossings. -/
theorem curl_5_21 (μ : X) (i : I) (n : ℕ) :
    xev cs μ [up i] [up i] (([up i], .lcup i, []) ::
      (dotsL [up i] i [dn i] n ++ curlRList i).map ofL) ∈ LeL D Sc cs μ [up i] [up i] 0 := by
  rw [show xev cs μ [up i] [up i] (([up i], .lcup i, []) :: _) = _ from
    xev_cons_eq cs μ ([up i], .lcup i, []) _, xev_map_ofL]
  change reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i] _ ∈ _
  rw [eq_5_21]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _
    (leL_comp0 cs (rbub_mem_leL cs μ i (bubL_mem_leL cs _ i _)) (cl_mem_leL cs (by simp))))

/-! ## Pitchforks (Proposition 7.2, (7.5)) -/

/-- (7.5), cap: an upward strand slides through the leftward cap `ε'`, turning the upward
crossing into the leftward crossing. Both sides have one crossing. -/
theorem pitchfork_cap (μ : X) (i j : I) :
    xev cs μ [dn i, up j, up i] [up j] [([dn i], .gen (.cross j i), []), ([], .lcap i, [up j])] =
      xev cs μ [dn i, up j, up i] [up j] [([], .gen (.lcross i j), [up i]), ([up j], .lcap i, [])] := by
  have e₁ : xev cs μ [dn i, up j, up i] [up j]
      [([dn i], .gen (.cross j i), []), ([], .lcap i, [up j])] = pfL cs i j μ := by
    change cl D Sc μ [dn i, up j, up i] [dn i, up j, up i] [] ≫ cl D Sc μ _ _ _ ≫
      (cl D Sc μ [dn i, up i, up j] [dn i, up i, up j] [] ≫ _ ≫ cl D Sc μ [up j] [up j] []) = _
    rw [cl_nil, cl_nil, cl_nil, Category.id_comp, Category.id_comp, Category.comp_id]
    rfl
  have e₂ : xev cs μ [dn i, up j, up i] [up j]
      [([], .gen (.lcross i j), [up i]), ([up j], .lcap i, [])] = pfR cs i j μ := by
    change cl D Sc μ [dn i, up j, up i] [dn i, up j, up i] [] ≫ cl D Sc μ _ _ _ ≫
      (cl D Sc μ [up j, dn i, up i] [up j, dn i, up i] [] ≫ _ ≫ cl D Sc μ [up j] [up j] []) = _
    rw [cl_nil, cl_nil, cl_nil, Category.id_comp, Category.id_comp, Category.comp_id]
    rfl
  rw [e₁, e₂, eq_7_5_a]

/-- (7.5), cup: an upward strand slides through the leftward cup `η'`, turning the upward
crossing into the leftward crossing. Both sides have one crossing. -/
theorem pitchfork_cup (μ : X) (i j : I) :
    xev cs μ [up j] [up i, up j, dn i] [([up j], .lcup i, []), ([], .gen (.cross j i), [dn i])] =
      xev cs μ [up j] [up i, up j, dn i] [([], .lcup i, [up j]), ([up i], .gen (.lcross i j), [])] := by
  have e₁ : xev cs μ [up j] [up i, up j, dn i]
      [([up j], .lcup i, []), ([], .gen (.cross j i), [dn i])] = pcuL cs i j μ := by
    change cl D Sc μ [up j] [up j] [] ≫ _ ≫
      (cl D Sc μ [up j, up i, dn i] [up j, up i, dn i] [] ≫ cl D Sc μ _ _ _ ≫
        cl D Sc μ [up i, up j, dn i] [up i, up j, dn i] []) = _
    rw [cl_nil, cl_nil, cl_nil, Category.id_comp, Category.id_comp, Category.comp_id]
    rfl
  have e₂ : xev cs μ [up j] [up i, up j, dn i]
      [([], .lcup i, [up j]), ([up i], .gen (.lcross i j), [])] = pcuR cs i j μ := by
    change cl D Sc μ [up j] [up j] [] ≫ _ ≫
      (cl D Sc μ [up i, dn i, up j] [up i, dn i, up j] [] ≫ cl D Sc μ _ _ _ ≫
        cl D Sc μ [up i, up j, dn i] [up i, up j, dn i] []) = _
    rw [cl_nil, cl_nil, cl_nil, Category.id_comp, Category.id_comp, Category.comp_id]
    rfl
  rw [e₁, e₂, eq_7_5_b]

end OddMath.SKM
