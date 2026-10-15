/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanCapCup

/-!
# Curls formed by a crossing and a cap or a cup

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11. The cap push uses that a crossing of
the two legs of a cap, or of a cup, gives lower terms. These are the curl relations of
Corollary 5.4 ((5.18), (5.20) without dots), after moving the crossing next to a cap or cup of
the opposite orientation:

* the rightward crossing `σ` (1.11) is the cup `η`, the upward crossing and the cap `ε`, so
  `σ` followed by `ε'`, and `η'` followed by `σ`, are curls up to the super interchange law;
* the leftward crossing is turned into the upward crossing by bending its downward strand with
  the zigzag (6.6) and applying the pitchfork relation (7.5).

## Main results

* `capCurl_up`, `capCurl_dn`, `capCurlRel`: the curl of a crossing and a cap (`CapCurlRel`).
* `cupCurl_up`, `cupCurl_dn`, `cupCurlRel`: the curl of a cup and a crossing (`CupCurlRel`).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## Equality up to sign -/

/-- The extended diagrams `L` and `L'` from `s` to `t` agree up to a sign `±1` (with no lower
terms). The super interchange law, the zigzags and the pitchfork relations have this form. -/
def XSgn (ν : X) (s t : List (Letter I)) (L L' : List (XLayer I)) : Prop :=
  ∃ p : ZMod 2, xev cs ν s t L = zsign k p • xev cs ν s t L'

namespace XSgn

variable {cs} {ν : X} {s t : List (Letter I)} {L L' L'' : List (XLayer I)}

theorem refl (L : List (XLayer I)) : XSgn cs ν s t L L := ⟨0, by rw [zsign_zero, one_smul]⟩

theorem of_eq (h : L = L') : XSgn cs ν s t L L' := h ▸ refl L

theorem symm (h : XSgn cs ν s t L L') : XSgn cs ν s t L' L := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, by rw [hp, smul_smul, zsign_mul_self', one_smul]⟩

theorem trans (h₁ : XSgn cs ν s t L L') (h₂ : XSgn cs ν s t L' L'') : XSgn cs ν s t L L'' := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  exact ⟨p + q, by rw [hp, hq, smul_smul, ← zsign_add]⟩

/-- Equality up to sign implies equality up to sign modulo lower terms. -/
theorem xeq (h : XSgn cs ν s t L L') (c : ℕ) : XEq cs ν s t c L L' := by
  obtain ⟨p, hp⟩ := h
  exact XEq.of_smul p hp

/-- **A relation up to sign in context.** -/
theorem «at» {s₀ t₀ : List (Letter I)} (pre post : List (XLayer I)) (u v : List (Letter I))
    {A B : List (XLayer I)} (E : XSgn cs (wt D ν v) s t A B)
    (hpre : XChain s₀ pre (u ++ s ++ v)) (hA : XChain s A t) (hB : XChain s B t)
    (hL : L = pre ++ A.map (xwhL u v) ++ post) (hL' : L' = pre ++ B.map (xwhL u v) ++ post) :
    XSgn cs ν s₀ t₀ L L' := by
  obtain ⟨p, hp⟩ := E
  subst hL hL'
  refine ⟨p, ?_⟩
  rw [xev_ctx cs ν pre post u v hpre hA, xev_ctx cs ν pre post u v hpre hB, hp, map_smul,
    Linear.smul_comp, Linear.comp_smul]

end XSgn

/-- **The super interchange law**, up to sign, with the diagrams given up to equality. -/
theorem XSgn.ichg {ν : X} {S T : List (Letter I)} {L L' : List (XLayer I)}
    (pre post : List (XLayer I)) (P Q : List (Letter I)) {s s' t t' : List (Letter I)}
    {A B : List (XLayer I)} (hA : XChain s A s') (hB : XChain t B t')
    (hpre : XChain S pre (P ++ (s ++ t) ++ Q))
    (hL : L = pre ++ A.map (xwhL P (t ++ Q)) ++ B.map (xwhL (P ++ s') Q) ++ post)
    (hL' : L' = pre ++ B.map (xwhL (P ++ s) Q) ++ A.map (xwhL P (t' ++ Q)) ++ post) :
    XSgn cs ν S T L L' := by
  subst hL hL'
  exact xev_ichg cs ν pre post P Q hA hB hpre

/-- The zigzag with the cup on the right ((1.10), (6.6)), up to sign. -/
theorem zigR_sgn (ν : X) (l : Letter I) :
    XSgn cs ν [flipL l] [flipL l]
      ((xCupL l).map (xwhL [flipL l] []) ++ (xCapL l).map (xwhL [] [flipL l])) [] := by
  obtain ⟨p, hp⟩ := zigR cs ν l
  exact ⟨p, by rw [xev_nil, cl_nil]; exact hp⟩

/-! ## The curls of Corollary 5.4 as extended diagrams -/

/-- The left curl of (5.18) without dots: the cup `η` on the left, the upward crossing, `ε'` on
the left. -/
def curlLX (i : I) : List (XLayer I) :=
  ([([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] 0 ++
    [([dn i], Shape.cross i i, [])]).map ofL ++ [([], .lcap i, [up i])]

/-- The right curl of (5.20) without dots: `η'` on the right, the upward crossing, the cap `ε` on
the right. -/
def curlRX (i : I) : List (XLayer I) :=
  ([up i], .lcup i, []) :: ([([], Shape.cross i i, [dn i])] ++ dotsL [up i] i [dn i] 0 ++
    [([up i], Shape.cap i, [])]).map ofL

theorem xChain_curlLX (i : I) : XChain [up i] (curlLX i) [up i] :=
  (XChain.of_sChain (sChain_curl_5_18 i 0)).append ⟨rfl, rfl⟩

theorem xChain_curlRX (i : I) : XChain [up i] (curlRX i) [up i] :=
  ⟨rfl, XChain.of_sChain (SChain.append (t' := [up i, up i, dn i])
    (SChain.append (t' := [up i, up i, dn i]) ⟨rfl, rfl⟩ (sChain_dotsL [up i] i [dn i] 0))
    ⟨rfl, rfl⟩)⟩

theorem curlLX_mem (μ : X) (i : I) :
    xev cs μ [up i] [up i] (curlLX i) ∈ LeL D Sc cs μ [up i] [up i] 0 :=
  curl_5_18 cs μ i 0

theorem curlRX_mem (μ : X) (i : I) :
    xev cs μ [up i] [up i] (curlRX i) ∈ LeL D Sc cs μ [up i] [up i] 0 :=
  curl_5_20 cs μ i 0

/-! ## The leftward crossing as a rotation of the upward crossing -/

/-- **The leftward crossing, rotated**: bending its downward strand by the zigzag (6.6) and the
pitchfork relation (7.5) turn the leftward crossing into `η'` on the right, the upward crossing
and `ε'` on the left, up to sign modulo lower terms, in a context `pre`, `post` without
crossings. -/
theorem lcross_rot {ν : X} {s₀ t₀ : List (Letter I)} (i : I) (pre post : List (XLayer I))
    (hpre : XChain s₀ pre [dn i, up i]) (hc : xcnt pre + xcnt post = 0) :
    XEq cs ν s₀ t₀ 0 (pre ++ [([], .gen (.lcross i i), [])] ++ post)
      (pre ++ [([dn i, up i], .lcup i, []), ([dn i], .gen (.cross i i), [dn i]),
        ([], .lcap i, [up i, dn i])] ++ post) := by
  have hX : XChain [dn i, up i] [([], .gen (.lcross i i), [])] [up i, dn i] := ⟨rfl, rfl⟩
  have hZ : XChain [dn i] [([dn i], .lcup i, []), ([], .lcap i, [dn i])] [dn i] :=
    ⟨rfl, rfl, rfl⟩
  have hU : XChain [] [([], .lcup i, [])] [up i, dn i] := ⟨rfl, rfl⟩
  -- step 1: the zigzag on the downward strand
  have E₁ := XSgn.at (cs := cs) (ν := ν) (s₀ := s₀) (t₀ := t₀)
    (L := pre ++ [([], .gen (.lcross i i), [])] ++ post) (pre ++ [([], .gen (.lcross i i), [])])
    post [up i] [] (XSgn.symm (zigR_sgn cs _ (up i))) (hpre.app hX rfl) rfl hZ (by simp) rfl
  -- step 2: `η'` passes below the leftward crossing
  have E₂ := XSgn.ichg cs (ν := ν) (S := s₀) (T := t₀)
    (L := pre ++ [([], .gen (.lcross i i), [])] ++ ((xCupL (up i)).map (xwhL [flipL (up i)] []) ++
      (xCapL (up i)).map (xwhL [] [flipL (up i)])).map (xwhL [up i] []) ++ post)
    pre ([([up i], .lcap i, [dn i])] ++ post) [] [] hX hU (by simpa using hpre)
    (by simp [xwhL, xCupL_up, xCapL_up]) rfl
  refine ((E₁.trans E₂).xeq 0).trans ?_
  -- step 3: the pitchfork (7.5)
  refine XEq.at (pre ++ [([dn i, up i], .lcup i, [])]) post [] [dn i] (capPF cs _ (up i) (up i))
    (hpre.app (show XChain [dn i, up i] [([dn i, up i], .lcup i, [])] [dn i, up i, up i, dn i]
      from ⟨rfl, rfl⟩) rfl) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ?_ ?_ ?_
  · simp [xwhL, xCrL_dn_up, xCapL_up]
  · simp [xwhL, xCrL_up_up, xCapL_up]
  · simp at hc ⊢; simp [hc, XShape.isCross]

/-! ## A crossing followed by a cap -/

/-- `σ` followed by `ε'` is the left curl (5.18), placed to the left of a downward strand and
followed by the cap `ε`, up to sign. -/
theorem capCurl_up (ν : X) (i : I) :
    xev cs ν [up i, dn i] [] (xCrL (up i) (dn i) ++ xCapL (up i)) ∈
      LeL D Sc cs ν [up i, dn i] [] 0 := by
  refine (XEq.symm (XEq.ichg cs (ν := ν) (c := 0) (S := [up i, dn i]) (T := [])
    [([], .gen (.cup i), [up i, dn i]), ([dn i], .gen (.cross i i), [dn i])] [] [] []
    (s := [dn i, up i]) (s' := []) (t := [up i, dn i]) (t' := [])
    (A := [([], .lcap i, [])]) (B := [([], .gen (.cap i), [])]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    ⟨rfl, rfl, rfl⟩ rfl (by simp [xCrL_up_dn, xCapL_up, sigmaL, ofL, xwhL]))).low ?_
  exact xev_low_at cs [] [([], .gen (.cap i), [])] [] [dn i] (curlLX_mem cs _ i) (by simp)
    (xChain_curlLX i) (by simp [curlLX, dotsL, ofL, xwhL]) (by simp [XShape.isCross, Shape.isCross])

/-- The leftward crossing followed by `ε` is the right curl (5.20), placed to the right of a
downward strand and followed by `ε'`, up to sign. -/
theorem capCurl_dn (ν : X) (i : I) :
    xev cs ν [dn i, up i] [] (xCrL (dn i) (up i) ++ xCapL (dn i)) ∈
      LeL D Sc cs ν [dn i, up i] [] 0 := by
  have E₁ := lcross_rot cs (ν := ν) (s₀ := [dn i, up i]) (t₀ := []) i [] [([], .gen (.cap i), [])]
    rfl (by simp [XShape.isCross, Shape.isCross])
  -- `ε'` passes below `ε`
  have E₂ : XEq cs ν [dn i, up i] [] 0 ([] ++ [([dn i, up i], .lcup i, []),
      ([dn i], .gen (.cross i i), [dn i]), ([], .lcap i, [up i, dn i])] ++
        [([], .gen (.cap i), [])])
      ([([dn i, up i], .lcup i, []), ([dn i], .gen (.cross i i), [dn i]),
        ([dn i, up i], .gen (.cap i), []), ([], .lcap i, [])]) :=
    XEq.ichg cs [([dn i, up i], .lcup i, []), ([dn i], .gen (.cross i i), [dn i])] [] [] []
      (s := [dn i, up i]) (s' := []) (t := [up i, dn i]) (t' := [])
      (A := [([], .lcap i, [])]) (B := [([], .gen (.cap i), [])]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      ⟨rfl, rfl, rfl⟩ (by simp [xwhL]) rfl
  refine (XEq.congr cs (by simp [xCrL_dn_up, xCapL_dn]) rfl (E₁.trans E₂)).low ?_
  exact xev_low_at cs [] [([], .lcap i, [])] [dn i] [] (curlRX_mem cs _ i) (by simp)
    (xChain_curlRX i) (by simp [curlRX, dotsL, ofL, xwhL]) (by simp [XShape.isCross])

/-- **The curl of a crossing and a cap** (`CapCurlRel`): Corollary 5.4 (5.18), (5.20). -/
theorem capCurlRel : CapCurlRel D Sc cs := by
  rintro ν ⟨_ | _, i⟩
  · exact capCurl_dn cs ν i
  · exact capCurl_up cs ν i

/-! ## A cup followed by a crossing -/

/-- `η` followed by the leftward crossing is `η'` followed by the left curl (5.18), placed to the
left of a downward strand, up to sign. -/
theorem cupCurl_up (ν : X) (i : I) :
    xev cs ν [] [up i, dn i] (xCupL (dn i) ++ xCrL (dn i) (up i)) ∈
      LeL D Sc cs ν [] [up i, dn i] 0 := by
  have E₁ := lcross_rot cs (ν := ν) (s₀ := []) (t₀ := [up i, dn i]) i [([], .gen (.cup i), [])] []
    ⟨rfl, rfl⟩ (by simp [XShape.isCross, Shape.isCross])
  -- `η` passes below `η'`
  have E₂ : XEq cs ν [] [up i, dn i] 0 ([([], .gen (.cup i), [])] ++
      [([dn i, up i], .lcup i, []), ([dn i], .gen (.cross i i), [dn i]),
        ([], .lcap i, [up i, dn i])] ++ [])
      ([([], .lcup i, []), ([], .gen (.cup i), [up i, dn i]), ([dn i], .gen (.cross i i), [dn i]),
        ([], .lcap i, [up i, dn i])]) :=
    XEq.ichg cs [] [([dn i], .gen (.cross i i), [dn i]), ([], .lcap i, [up i, dn i])] [] []
      (s := []) (s' := [dn i, up i]) (t := []) (t' := [up i, dn i])
      (A := [([], .gen (.cup i), [])]) (B := [([], .lcup i, [])]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      rfl (by simp [xwhL]) rfl
  refine (XEq.congr cs (by simp [xCrL_dn_up, xCupL_dn]) rfl (E₁.trans E₂)).low ?_
  exact xev_low_at cs [([], .lcup i, [])] [] [] [dn i] (curlLX_mem cs _ i) ⟨rfl, rfl⟩
    (xChain_curlLX i) (by simp [curlLX, dotsL, ofL, xwhL]) (by simp [XShape.isCross])

/-- `η'` followed by `σ` is `η` followed by the right curl (5.20), placed to the right of a
downward strand, up to sign. -/
theorem cupCurl_dn (ν : X) (i : I) :
    xev cs ν [] [dn i, up i] (xCupL (up i) ++ xCrL (up i) (dn i)) ∈
      LeL D Sc cs ν [] [dn i, up i] 0 := by
  refine (XEq.symm (XEq.ichg cs (ν := ν) (c := 0) (S := []) (T := [dn i, up i]) []
    [([dn i], .gen (.cross i i), [dn i]), ([dn i, up i], .gen (.cap i), [])] [] []
    (s := []) (s' := [dn i, up i]) (t := []) (t' := [up i, dn i])
    (A := [([], .gen (.cup i), [])]) (B := [([], .lcup i, [])]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    rfl rfl (by simp [xCrL_up_dn, xCupL_up, sigmaL, ofL, xwhL]))).low ?_
  exact xev_low_at cs [([], .gen (.cup i), [])] [] [dn i] [] (curlRX_mem cs _ i) ⟨rfl, rfl⟩
    (xChain_curlRX i) (by simp [curlRX, dotsL, ofL, xwhL])
    (by simp [XShape.isCross, Shape.isCross])

/-- **The curl of a cup and a crossing** (`CupCurlRel`): Corollary 5.4 (5.18), (5.20). -/
theorem cupCurlRel : CupCurlRel D Sc cs := by
  rintro ν ⟨_ | _, i⟩
  · exact cupCurl_dn cs ν i
  · exact cupCurl_up cs ν i

end OddMath.SKM
