/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanCaps
import OddMath.SKM.PitchforkRot

/-!
# Local relations for letters of both orientations, modulo lower terms

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11. The cap push of the proof of KL III
Proposition 3.11 moves a cap past dots, crossings and cups of strands of either orientation. This
file states the local relations it uses for the crossings `xCrL l₁ l₂`, dots `xDotL l`, cups
`xCupL l` and caps `xCapL l` of letters `l` of either orientation, modulo diagrams with fewer
crossings.

## Equality up to sign modulo lower terms

The signs of the super interchange law and of the odd dot slides are units `±1`; they are
irrelevant for spans. `XEq ν s t c L L'` says that the extended diagrams `L` and `L'` from `s` to
`t` agree up to a sign `±1` modulo `LeL c`. It is an equivalence relation (`XEq.refl`,
`XEq.symm`, `XEq.trans`), holds in any context (`XEq.at`) and contains the super interchange law
(`XEq.ichg`).

## Main results

* `ds_left`, `ds_right`: a dot slides through a crossing of two strands of any orientations
  (Lemma 3.1 (3.1)–(3.6), Proposition 4.1 (4.1), (4.2)).
* `r2_all`: a double crossing of two strands of any orientations is a lower term ((1.7), its mate,
  (1.12)–(1.14), (2.12)).
* `capPF`: a strand passes through a cap of either orientation ((2.4), (2.5), Proposition 7.2
  (7.5), (7.6)).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## Equality up to sign modulo lower terms -/

/-- The extended diagrams `L` and `L'` from `s` to `t` agree up to a sign modulo diagrams with at
most `c` crossings. -/
def XEq (ν : X) (s t : List (Letter I)) (c : ℕ) (L L' : List (XLayer I)) : Prop :=
  ∃ p : ZMod 2, xev cs ν s t L - zsign k p • xev cs ν s t L' ∈ LeL D Sc cs ν s t c

namespace XEq

variable {cs} {ν : X} {s t : List (Letter I)} {c c' : ℕ} {L L' L'' : List (XLayer I)}

theorem refl (L : List (XLayer I)) : XEq cs ν s t c L L :=
  ⟨0, by rw [zsign_zero, one_smul, sub_self]; exact Submodule.zero_mem _⟩

theorem of_eq (h : L = L') : XEq cs ν s t c L L' := h ▸ refl L

theorem of_smul (p : ZMod 2) (h : xev cs ν s t L = zsign k p • xev cs ν s t L') :
    XEq cs ν s t c L L' :=
  ⟨p, by rw [h, sub_self]; exact Submodule.zero_mem _⟩

theorem of_sub (h : xev cs ν s t L - xev cs ν s t L' ∈ LeL D Sc cs ν s t c) :
    XEq cs ν s t c L L' :=
  ⟨0, by rwa [zsign_zero, one_smul]⟩

theorem symm (h : XEq cs ν s t c L L') : XEq cs ν s t c L' L := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p, ?_⟩
  have e : xev cs ν s t L' - zsign k p • xev cs ν s t L =
      (-zsign k p) • (xev cs ν s t L - zsign k p • xev cs ν s t L') := by
    rw [smul_sub, smul_smul, neg_mul, zsign_mul_self', neg_smul, neg_smul, one_smul]; abel
  rw [e]; exact Submodule.smul_mem _ _ hp

theorem trans (h₁ : XEq cs ν s t c L L') (h₂ : XEq cs ν s t c L' L'') : XEq cs ν s t c L L'' := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  refine ⟨p + q, ?_⟩
  have := Submodule.add_mem _ hp (Submodule.smul_mem _ (zsign k p) hq)
  rwa [smul_sub, smul_smul, ← zsign_add, sub_add_sub_cancel] at this

theorem mono (h : XEq cs ν s t c L L') (hc : c ≤ c') : XEq cs ν s t c' L L' := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, leL_mono cs hc hp⟩

/-- Lower terms are equivalent to each other. -/
theorem of_low (h : xev cs ν s t L ∈ LeL D Sc cs ν s t c)
    (h' : xev cs ν s t L' ∈ LeL D Sc cs ν s t c) : XEq cs ν s t c L L' :=
  of_sub (Submodule.sub_mem _ h h')

theorem low (h : XEq cs ν s t c L L') (h' : xev cs ν s t L' ∈ LeL D Sc cs ν s t c) :
    xev cs ν s t L ∈ LeL D Sc cs ν s t c := by
  obtain ⟨p, hp⟩ := h
  have := Submodule.add_mem _ hp (Submodule.smul_mem _ (zsign k p) h')
  rwa [sub_add_cancel] at this

/-- **A local relation in context.** -/
theorem ctx {s₀ t₀ : List (Letter I)} (pre post : List (XLayer I)) (u v : List (Letter I))
    {A B : List (XLayer I)} (E : XEq cs (wt D ν v) s t c A B)
    (hpre : XChain s₀ pre (u ++ s ++ v)) (hA : XChain s A t) (hB : XChain s B t) :
    XEq cs ν s₀ t₀ (xcnt pre + c + xcnt post) (pre ++ A.map (xwhL u v) ++ post)
      (pre ++ B.map (xwhL u v) ++ post) := by
  obtain ⟨p, hp⟩ := E
  refine ⟨p, ?_⟩
  have e : xev cs ν s₀ (u ++ s ++ v) pre ≫ plcL D Sc ν u v s t (xev cs (wt D ν v) s t A) ≫
        xev cs ν (u ++ t ++ v) t₀ post -
      zsign k p • (xev cs ν s₀ (u ++ s ++ v) pre ≫ plcL D Sc ν u v s t (xev cs (wt D ν v) s t B) ≫
        xev cs ν (u ++ t ++ v) t₀ post) =
      xev cs ν s₀ (u ++ s ++ v) pre ≫ plcL D Sc ν u v s t (xev cs (wt D ν v) s t A -
        zsign k p • xev cs (wt D ν v) s t B) ≫ xev cs ν (u ++ t ++ v) t₀ post := by
    simp only [map_sub, map_smul, Preadditive.comp_sub, Preadditive.sub_comp, Linear.comp_smul,
      Linear.smul_comp]
  rw [xev_ctx cs ν pre post u v hpre hA, xev_ctx cs ν pre post u v hpre hB, e]
  exact leL_comp_le cs (xev_mem_leL cs le_rfl)
    (leL_comp cs (plcL_leL cs hp) (xev_mem_leL cs le_rfl)) (by omega)

/-- **A local relation in context**, with the diagrams given up to equality. -/
theorem «at» {s₀ t₀ : List (Letter I)} (pre post : List (XLayer I)) (u v : List (Letter I))
    {A B : List (XLayer I)} {c₀ : ℕ} (E : XEq cs (wt D ν v) s t c₀ A B)
    (hpre : XChain s₀ pre (u ++ s ++ v)) (hA : XChain s A t) (hB : XChain s B t)
    (hL : L = pre ++ A.map (xwhL u v) ++ post) (hL' : L' = pre ++ B.map (xwhL u v) ++ post)
    (hc : xcnt pre + c₀ + xcnt post ≤ c) : XEq cs ν s₀ t₀ c L L' := by
  subst hL hL'
  exact (ctx pre post u v E hpre hA hB).mono hc

end XEq

/-- **A local lower term in context**, with the diagram given up to equality. -/
theorem xev_low_at {ν : X} {s₀ t₀ s t : List (Letter I)} {c c₀ : ℕ} {L : List (XLayer I)}
    (pre post : List (XLayer I)) (u v : List (Letter I)) {A : List (XLayer I)}
    (E : xev cs (wt D ν v) s t A ∈ LeL D Sc cs (wt D ν v) s t c₀)
    (hpre : XChain s₀ pre (u ++ s ++ v)) (hA : XChain s A t)
    (hL : L = pre ++ A.map (xwhL u v) ++ post) (hc : xcnt pre + c₀ + xcnt post ≤ c) :
    xev cs ν s₀ t₀ L ∈ LeL D Sc cs ν s₀ t₀ c := by
  subst hL
  exact leL_mono cs hc (xev_mem_ctx cs ν pre post u v E hpre hA)

/-- **The super interchange law**, up to sign, with the diagrams given up to equality. -/
theorem XEq.ichg {ν : X} {S T : List (Letter I)} {c : ℕ} {L L' : List (XLayer I)}
    (pre post : List (XLayer I)) (P Q : List (Letter I)) {s s' t t' : List (Letter I)}
    {A B : List (XLayer I)} (hA : XChain s A s') (hB : XChain t B t')
    (hpre : XChain S pre (P ++ (s ++ t) ++ Q))
    (hL : L = pre ++ A.map (xwhL P (t ++ Q)) ++ B.map (xwhL (P ++ s') Q) ++ post)
    (hL' : L' = pre ++ B.map (xwhL (P ++ s) Q) ++ A.map (xwhL P (t' ++ Q)) ++ post) :
    XEq cs ν S T c L L' := by
  subst hL hL'
  obtain ⟨p, hp⟩ := xev_ichg cs ν (T := T) pre post P Q hA hB hpre
  exact XEq.of_smul p hp

/-! ## Lists of layers -/

theorem XChain.app {s r r' t : List (Letter I)} {L M : List (XLayer I)} (h₁ : XChain s L r)
    (h₂ : XChain r' M t) (h : r = r') : XChain s (L ++ M) t := h₁.append (h ▸ h₂)

theorem XChain.cast {s s' t t' : List (Letter I)} {L : List (XLayer I)} (h : XChain s L t)
    (hs : s = s') (ht : t = t') : XChain s' L t' := hs ▸ ht ▸ h

@[simp] theorem xChain_nil_iff {s t : List (Letter I)} : XChain s ([] : List (XLayer I)) t ↔ s = t :=
  Iff.rfl

theorem lmLc_append (S₁ S₂ : List (Letter I)) (b : Letter I) :
    lmLc (S₁ ++ S₂) b = (lmLc S₂ b).map (xwhL S₁ []) ++ (lmLc S₁ b).map (xwhL [] S₂) := by
  induction S₁ with
  | nil => simp [lmLc]
  | cons s S₁ ih =>
    simp only [List.cons_append, lmLc, ih, List.map_append, map_xwhL_xwhL, List.append_assoc]
    simp

theorem lmLc_snoc (S : List (Letter I)) (s b : Letter I) :
    lmLc (S ++ [s]) b = (xCrL s b).map (xwhL S []) ++ (lmLc S b).map (xwhL [] [s]) := by
  rw [lmLc_append]; simp [lmLc]

/-! ## Normal-form relations as relations of extended diagrams -/

namespace XEq

variable {cs} {ν : X} {s t : List (Letter I)} {c : ℕ} {L L' : List (XLayer I)}

theorem of_cl {A B : List (LayerData I)} (hL : L = A.map ofL) (hL' : L' = B.map ofL) (p : ZMod 2)
    (h : cl D Sc ν s t A - zsign k p • cl D Sc ν s t B ∈ LeL D Sc cs ν s t c) :
    XEq cs ν s t c L L' :=
  ⟨p, by subst hL hL'; rwa [xev_map_ofL, xev_map_ofL]⟩

theorem of_cl' {A B : List (LayerData I)} (hL : L = A.map ofL) (hL' : L' = B.map ofL)
    (p : ZMod 2) (h : zsign k p • cl D Sc ν s t A - cl D Sc ν s t B ∈ LeL D Sc cs ν s t c) :
    XEq cs ν s t c L L' := by
  refine ⟨p, ?_⟩
  subst hL hL'
  rw [xev_map_ofL, xev_map_ofL]
  have e : cl D Sc ν s t A - zsign k p • cl D Sc ν s t B =
      zsign k p • (zsign k p • cl D Sc ν s t A - cl D Sc ν s t B) := by
    rw [smul_sub, smul_smul, zsign_mul_self', one_smul]
  rw [e]; exact Submodule.smul_mem _ _ h

end XEq

theorem xDotL_up (i : I) : xDotL (up i) = [([], .gen (.dot i), [])] := rfl
theorem xDotL_dn (i : I) : xDotL (dn i) = (ddotL i).map ofL := rfl
theorem xCrL_up_up (i j : I) : xCrL (up i) (up j) = [([], .gen (.cross i j), [])] := rfl
theorem xCrL_dn_up (i j : I) : xCrL (dn i) (up j) = [([], .gen (.lcross i j), [])] := rfl
theorem xCrL_up_dn (i j : I) : xCrL (up j) (dn i) = (sigmaL i j).map ofL := rfl
theorem xCrL_dn_dn (i j : I) : xCrL (dn i) (dn j) = (dcrossL i j).map ofL := rfl
theorem xCapL_up (i : I) : xCapL (up i) = [([], .lcap i, [])] := rfl
theorem xCapL_dn (i : I) : xCapL (dn i) = [([], .gen (.cap i), [])] := rfl
theorem xCupL_up (i : I) : xCupL (up i) = [([], .lcup i, [])] := rfl
theorem xCupL_dn (i : I) : xCupL (dn i) = [([], .gen (.cup i), [])] := rfl

/-! ## Dot slides -/

theorem ddotsL_one' (i : I) : ddotsL i 1 = ddotL i := by simp [ddotsL]

theorem sChain_ddotL_r (i : I) :
    SChain [up i, dn i] ((ddotL i).map (whL [up i] [])) [up i, dn i] :=
  (sChain_ddotL i).wh [up i] [] rfl rfl

theorem sChain_ddotsL_wh (i : I) (n : ℕ) (u v : List (Letter I)) :
    SChain (u ++ [dn i] ++ v) ((ddotsL i n).map (whL u v)) (u ++ [dn i] ++ v) :=
  (sChain_ddotsL i n).wh u v rfl rfl

/-- **A dot slides through a crossing**, from the left incoming to the right outgoing strand
(Lemma 3.1 (3.1), (3.3), (3.5), Proposition 4.1 (4.1)), up to sign modulo diagrams without
crossings. -/
theorem ds_left (ν : X) (a b : Letter I) :
    XEq cs ν [a, b] [b, a] 0 ((xDotL a).map (xwhL [] [b]) ++ xCrL a b)
      (xCrL a b ++ (xDotL a).map (xwhL [b] [])) := by
  obtain ⟨_ | _, i⟩ := a <;> obtain ⟨_ | _, j⟩ := b
  · -- two downward strands, (3.5)
    refine XEq.symm (XEq.of_cl' (A := dcrossL i j ++ (ddotsL i 1).map (whL [dn j] []))
      (B := (ddotsL i 1).map (whL [] [dn j]) ++ dcrossL i j) ?_ ?_ _ (dsDn0 cs ν j i 1))
    · simp only [xDotL_dn, xCrL_dn_dn, ddotsL_one', map_xwhL_map_ofL, List.map_append]
    · simp only [xDotL_dn, xCrL_dn_dn, ddotsL_one', map_xwhL_map_ofL, List.map_append]
  · -- the leftward crossing, (4.1)
    by_cases hij : i = j
    · subst hij
      refine XEq.of_cl (A := (ddotL i).map (whL [] [up i]) ++ lcrossL i i)
        (B := lcrossL i i ++ (ddotL i).map (whL [up i] [])) ?_ ?_ (D.parity i) ?_
      · simp only [xDotL_dn, xCrL_dn_up, map_xwhL_map_ofL, List.map_append]; rfl
      · simp only [xDotL_dn, xCrL_dn_up, map_xwhL_map_ofL, List.map_append]; rfl
      · have E := lemma41_eq1_one' Sc cs i ν
        rw [cl_comp (sChain_ddotL' i) (sChain_lcrossL i i),
          cl_comp (sChain_lcrossL i i) (sChain_ddotL_r i)] at E
        rw [E]
        exact leL_comp0 cs (epsP_mem_leL cs ν i 0) (etaP_mem_leL cs ν i 0)
    · refine XEq.of_cl (A := (ddotsL i 1).map (whL [] [up j]) ++ lcrossL i j)
        (B := lcrossL i j ++ (ddotsL i 1).map (whL [up j] [])) ?_ ?_
        (D.parity i * D.parity j * (1 : ℕ)) ?_
      · simp only [xDotL_dn, xCrL_dn_up, map_xwhL_map_ofL, List.map_append, ddotsL_one']; rfl
      · simp only [xDotL_dn, xCrL_dn_up, map_xwhL_map_ofL, List.map_append, ddotsL_one']; rfl
      · have E := lemma41_eq1_ne Sc i j ν hij 1
        rw [cl_comp (s := [dn i, up j]) (t := [dn i, up j]) (sChain_ddotsL_wh i 1 [] [up j])
            (sChain_lcrossL i j),
          cl_comp (t := [up j, dn i]) (r := [up j, dn i]) (sChain_lcrossL i j)
            (sChain_ddotsL_wh i 1 [up j] [])] at E
        rw [E]; exact Submodule.zero_mem _
  · -- `σ`, (3.3)
    refine XEq.symm (XEq.of_cl (A := sigmaL j i ++ dotsL [dn j] i [] 1)
      (B := dotsL [] i [dn j] 1 ++ sigmaL j i) ?_ ?_ _ (dsSigma0 cs ν i j 1))
    · simp only [xDotL_up, xCrL_up_dn, List.map_append]; rfl
    · simp only [xDotL_up, xCrL_up_dn, List.map_append]; rfl
  · -- two upward strands, (3.1)
    refine XEq.of_cl (A := dotsL [] i [up j] 1 ++ crossL [] i j [])
      (B := crossL [] i j [] ++ dotsL [up j] i [] 1) ?_ ?_ _ (dsUp0 cs ν i j 1)
    · rfl
    · rfl

/-- **A dot slides through a crossing**, from the right incoming to the left outgoing strand
(Lemma 3.1 (3.2), (3.4), (3.6), Proposition 4.1 (4.2)), up to sign modulo diagrams without
crossings. -/
theorem ds_right (ν : X) (a b : Letter I) :
    XEq cs ν [a, b] [b, a] 0 ((xDotL b).map (xwhL [a] []) ++ xCrL a b)
      (xCrL a b ++ (xDotL b).map (xwhL [] [a])) := by
  obtain ⟨_ | _, i⟩ := a <;> obtain ⟨_ | _, j⟩ := b
  · -- two downward strands, (3.6)
    refine XEq.of_cl' (A := (ddotsL j 1).map (whL [dn i] []) ++ dcrossL i j)
      (B := dcrossL i j ++ (ddotsL j 1).map (whL [] [dn i])) ?_ ?_ _ (dsDn1 cs ν j i 1)
    · simp only [xDotL_dn, xCrL_dn_dn, ddotsL_one', map_xwhL_map_ofL, List.map_append]
    · simp only [xDotL_dn, xCrL_dn_dn, ddotsL_one', map_xwhL_map_ofL, List.map_append]
  · -- the leftward crossing, (4.2)
    by_cases hij : i = j
    · subst hij
      refine XEq.of_cl' (A := dotsL [dn i] i [] 1 ++ lcrossL i i)
        (B := lcrossL i i ++ dotsL [] i [dn i] 1) ?_ ?_ (D.parity i) ?_
      · rfl
      · rfl
      · have E := lemma41_eq2_one' Sc cs i ν
        rw [cl_comp (s := [dn i, up i]) (t := [dn i, up i]) (sChain_dotsL [dn i] i [] 1)
            (sChain_lcrossL i i),
          cl_comp (t := [up i, dn i]) (r := [up i, dn i]) (sChain_lcrossL i i)
            (sChain_dotsL [] i [dn i] 1)] at E
        rw [E]
        exact Submodule.smul_mem _ _
          (leL_comp0 cs (epsP_mem_leL cs ν i 0) (etaP_mem_leL cs ν i 0))
    · refine XEq.of_cl' (A := dotsL [dn i] j [] 1 ++ lcrossL i j)
        (B := lcrossL i j ++ dotsL [] j [dn i] 1) ?_ ?_
        (D.parity i * D.parity j * (1 : ℕ)) ?_
      · rfl
      · rfl
      · have E := lemma41_eq2_ne Sc i j ν hij 1
        rw [cl_comp (s := [dn i, up j]) (t := [dn i, up j]) (sChain_dotsL [dn i] j [] 1)
            (sChain_lcrossL i j),
          cl_comp (t := [up j, dn i]) (r := [up j, dn i]) (sChain_lcrossL i j)
            (sChain_dotsL [] j [dn i] 1)] at E
        rw [E]; exact Submodule.zero_mem _
  · -- `σ`, (3.4)
    refine XEq.symm (XEq.of_cl' (A := sigmaL j i ++ (ddotsL j 1).map (whL [] [up i]))
      (B := (ddotsL j 1).map (whL [up i] []) ++ sigmaL j i) ?_ ?_ _ (dsSigma1 cs ν i j 1))
    · simp only [xDotL_dn, xCrL_up_dn, ddotsL_one', map_xwhL_map_ofL, List.map_append]
    · simp only [xDotL_dn, xCrL_up_dn, ddotsL_one', map_xwhL_map_ofL, List.map_append]
  · -- two upward strands, (3.2)
    refine XEq.symm (XEq.of_cl (A := crossL [] i j [] ++ dotsL [] j [up i] 1)
      (B := dotsL [up i] j [] 1 ++ crossL [] i j []) ?_ ?_ _ (dsUp1 cs ν i j 1))
    · rfl
    · rfl

/-! ## Reidemeister II -/

/-- **A double crossing of two strands of any orientations is a lower term** ((1.7), its mate,
(1.12)–(1.14), (2.12)). -/
theorem r2_all (ν : X) (a b : Letter I) :
    xev cs ν [a, b] [a, b] (xCrL a b ++ xCrL b a) ∈ LeL D Sc cs ν [a, b] [a, b] 0 := by
  obtain ⟨_ | _, i⟩ := a <;> obtain ⟨_ | _, j⟩ := b
  · rw [xCrL_dn_dn, xCrL_dn_dn, ← List.map_append, xev_map_ofL]; exact r2Dn cs ν i j
  · rw [xCrL_dn_up, xCrL_up_dn,
      show [([], XShape.gen (Shape.lcross i j), [])] = (lcrossL i j).map ofL from rfl,
      ← List.map_append, xev_map_ofL]
    exact r2Lcross cs ν i j
  · rw [xCrL_dn_up, xCrL_up_dn,
      show [([], XShape.gen (Shape.lcross j i), [])] = (lcrossL j i).map ofL from rfl,
      ← List.map_append, xev_map_ofL]
    exact r2Sigma cs ν j i
  · have h := r2Up cs ν i j
    rw [← xev_map_ofL cs] at h
    exact h

/-! ## Pitchforks through caps -/

/-- `ε'` placed between strands is a single extended layer. -/
theorem xev_lcap_at (ν : X) (u v : List (Letter I)) (i : I) :
    xev cs ν (u ++ [dn i, up i] ++ v) (u ++ [] ++ v) [(u, .lcap i, v)] = capAt cs i ν u v :=
  xev_single cs ν (u, .lcap i, v)

/-- **A strand passes through a cap** of either orientation: the strand `m` crossing the left leg
`A = l*` of the cap `xCapL l` equals `m` crossing its right leg `B = l` ((2.4), (2.5),
Proposition 7.2 (7.5), (7.6)). Both sides have one crossing. -/
theorem capPF (ν : X) (l m : Letter I) :
    XEq cs ν [flipL l, m, l] [m] 0
      ((xCrL (flipL l) m).map (xwhL [] [l]) ++ (xCapL l).map (xwhL [m] []))
      ((xCrL m l).map (xwhL [flipL l] []) ++ (xCapL l).map (xwhL [] [m])) := by
  obtain ⟨_ | _, i⟩ := l <;> obtain ⟨_ | _, j⟩ := m <;>
    simp only [flipL, Bool.not_false, Bool.not_true]
  · -- the rightward cap and a downward strand, (2.5)
    refine XEq.of_cl (A := (sigmaL j i).map (whL [] [dn i]) ++ [([dn j], Shape.cap i, [])])
      (B := (dcrossL j i).map (whL [up i] []) ++ [([], Shape.cap i, [dn j])]) ?_ ?_ 0 ?_
    · simp only [xCrL_up_dn, xCapL_dn, map_xwhL_map_ofL, List.map_append]
      rfl
    · simp only [xCrL_dn_dn, xCapL_dn, map_xwhL_map_ofL, List.map_append]
      rfl
    · rw [eq_2_5_b, zsign_zero, one_smul, sub_self]; exact Submodule.zero_mem _
  · -- the rightward cap and an upward strand, (2.4)
    refine XEq.of_cl (A := [([], Shape.cross i j, [dn i]), ([up j], Shape.cap i, [])])
      (B := (sigmaL i j).map (whL [up i] []) ++ [([], Shape.cap i, [up j])]) ?_ ?_ 0 ?_
    · rfl
    · simp only [xCrL_up_dn, xCapL_dn, map_xwhL_map_ofL, List.map_append]
      rfl
    · rw [eq_2_4_a, zsign_zero, one_smul, sub_self]; exact Submodule.zero_mem _
  · -- the leftward cap and a downward strand, (7.6)
    have hA : SChain [dn i, dn j, up i] ((dcrossL i j).map (whL [] [up i])) [dn j, dn i, up i] :=
      (sChain_dcrossL i j).wh [] [up i] rfl rfl
    have hB : SChain [dn i, dn j, up i] ((lcrossL j i).map (whL [dn i] [])) [dn i, up i, dn j] :=
      (sChain_lcrossL j i).wh [dn i] [] rfl rfl
    have e₁ : (xCrL (dn i) (dn j)).map (xwhL [] [up i]) ++
        (xCapL (up i)).map (xwhL [dn j] []) =
        ((dcrossL i j).map (whL [] [up i])).map ofL ++ [([dn j], .lcap i, [])] := by
      simp only [xCrL_dn_dn, xCapL_up, map_xwhL_map_ofL]; rfl
    have e₂ : (xCrL (dn j) (up i)).map (xwhL [dn i] []) ++
        (xCapL (up i)).map (xwhL [] [dn j]) =
        ((lcrossL j i).map (whL [dn i] [])).map ofL ++ [([], .lcap i, [dn j])] := by
      simp only [xCrL_dn_up, xCapL_up]; rfl
    refine ⟨D.parity i * D.parity j, ?_⟩
    rw [e₁, e₂, xev_append cs _ (XChain.of_sChain hA), xev_append cs _ (XChain.of_sChain hB),
      xev_map_ofL, xev_map_ofL, show xev cs ν [dn j, dn i, up i] [dn j] [([dn j], .lcap i, [])] =
        capAt cs i ν [dn j] [] from xev_lcap_at cs ν [dn j] [] i,
      show xev cs ν [dn i, up i, dn j] [dn j] [([], .lcap i, [dn j])] =
        capAt cs i ν [] [dn j] from xev_lcap_at cs ν [] [dn j] i]
    have E := eq_7_6_b cs i j ν
    unfold pdcapL pdcapR at E
    rw [E, sub_self]; exact Submodule.zero_mem _
  · -- the leftward cap and an upward strand, (7.5)
    refine XEq.symm (XEq.of_smul 0 ?_)
    rw [zsign_zero, one_smul]
    exact pitchfork_cap cs ν i j

/-! ## Dots around caps -/

theorem dotCap_dn (ν : X) (i : I) : ∃ (p : ZMod 2) (r : k),
    xev cs ν [up i, dn i] [] ((xDotL (dn i)).map (xwhL [up i] []) ++ xCapL (dn i)) =
      zsign k p • xev cs ν [up i, dn i] [] ((xDotL (up i)).map (xwhL [] [dn i]) ++ xCapL (dn i)) +
        r • (xev cs ν [up i, dn i] [] (xCapL (dn i)) ≫ oddBubble cs i ν) := by
  refine ⟨D.parity i * ((1 / 2 : ℕ) : ZMod 2), 0, ?_⟩
  rw [zero_smul, add_zero]
  have E := eq_2_3_b' (Sc := Sc) i ν 1
  rw [← xev_map_ofL cs, ← xev_map_ofL cs, ddotsL_one'] at E
  exact E

theorem dotCap_up (ν : X) (i : I) : ∃ (p : ZMod 2) (r : k),
    xev cs ν [dn i, up i] [] ((xDotL (up i)).map (xwhL [dn i] []) ++ xCapL (up i)) =
      zsign k p • xev cs ν [dn i, up i] [] ((xDotL (dn i)).map (xwhL [] [up i]) ++ xCapL (up i)) +
        r • (xev cs ν [dn i, up i] [] (xCapL (up i)) ≫ oddBubble cs i ν) := by
  have hL : xev cs ν [dn i, up i] [] ((xDotL (up i)).map (xwhL [dn i] []) ++ xCapL (up i)) =
      uRM D Sc i ν ≫ epsP cs i ν := by
    rw [xev_append cs _ (show XChain [dn i, up i] ((xDotL (up i)).map (xwhL [dn i] []))
      [dn i, up i] from ⟨rfl, rfl⟩), xCapL_up, xev_lcap,
      show (xDotL (up i)).map (xwhL [dn i] []) = (dotsL [dn i] i [] 1).map ofL from rfl,
      xev_map_ofL]
  have hR : xev cs ν [dn i, up i] [] ((xDotL (dn i)).map (xwhL [] [up i]) ++ xCapL (up i)) =
      dLM D Sc i ν ≫ epsP cs i ν := by
    rw [xDotL_dn, map_xwhL_map_ofL, xev_append cs _ (XChain.of_sChain (sChain_ddotL' i)),
      xCapL_up, xev_lcap, xev_map_ofL]
  rw [hL, hR, xCapL_up, xev_lcap]
  rcases zmod2_cases (D.parity i) with hi | hi
  · exact ⟨0, 0, by rw [lemma41_eq3_one_even cs i ν hi, zsign_zero, one_smul, zero_smul,
      add_zero]⟩
  · exact ⟨_, 2, lemma41_eq3_one_odd cs i ν hi⟩

/-- **A dot moves around a cap** ((2.3), Proposition 4.1 (4.3)): a dot on the right leg `l` of the
cap `xCapL l` is, up to sign, a dot on its left leg, plus (for the leftward cap `ε'` and odd `i`)
twice the odd bubble (2.18) in the region of the cap. -/
theorem dotCap (ν : X) (l : Letter I) : ∃ (p : ZMod 2) (r : k),
    xev cs ν [flipL l, l] [] ((xDotL l).map (xwhL [flipL l] []) ++ xCapL l) =
      zsign k p • xev cs ν [flipL l, l] [] ((xDotL (flipL l)).map (xwhL [] [l]) ++ xCapL l) +
        r • (xev cs ν [flipL l, l] [] (xCapL l) ≫ oddBubble cs l.2 ν) := by
  obtain ⟨_ | _, i⟩ := l
  · exact dotCap_dn cs ν i
  · exact dotCap_up cs ν i

end OddMath.SKM
