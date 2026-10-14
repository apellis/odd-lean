/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanClosed
import OddMath.SKM.LeftDot
import OddMath.SKM.ChevalleyLeft

/-!
# Local moves of a cap

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1 and (1.21)–(1.22) for diagrams without crossings, following the argument for closed
crossingless diagrams in M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*,
arXiv:0807.3250v1, §3.2.1 (proof of Proposition 3.6).

A cap `l* l → 1` (`capBlk l m`) carries a block of `m` dots on its upward leg: the rightward cap
`ε` (`l = dn i`) on its left leg, the leftward cap `ε'` (`l = up i`) on its right leg. This file
records what happens when the cap meets the layer just below it.

* A dot on the upward leg joins the block (`dotUp_capBlk_dn`, `dotUp_capBlk_up`).
* A downward dot on the downward leg moves to the upward leg: exactly for `ε` ((2.3),
  `ddot_capBlk_dn`); for `ε'` by Proposition 4.1 (4.3), which adds a term with the odd bubble
  (2.18) when `i` is odd (`ddot_capBlk_up`).
* A cup creating both legs closes up to a dotted bubble (`isBub_cup_capBlk`, Definition 2.3).
* A cup sharing one leg with the cap forms a zigzag. The zigzags of the right adjunction
  ((1.10), `zig_dn_left`, `zig_dn_right`) and the zigzag `(ε' ⊗ 1) ∘ (1 ⊗ η') = 1` on `Eᵢ`
  ((6.6), `zig_up_left`) leave dots on the strand; the zigzag on `Fᵢ` with dots on its middle
  segment needs Proposition 4.1 (4.4), which adds terms with odd bubbles (`zig_up_right`). In
  all four cases the result lies in `slideSetR` (dots followed by elements of the image of `β`
  in the region to the right of the strand).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## The cap with a block of dots -/

/-- The cap `l* l → 1` with `m` dots on its upward leg: dots on the left leg of `ε` (`l = dn i`),
on the right leg of `ε'` (`l = up i`). -/
def capBlk : Letter I → ℕ → List (XLayer I)
  | (false, i), m => (xDots (up i) m).map (xwhL [] [dn i]) ++ [([], .gen (.cap i), [])]
  | (true, i), m => (xDots (up i) m).map (xwhL [dn i] []) ++ [([], .lcap i, [])]

theorem xChain_capBlk : ∀ (l : Letter I) (m : ℕ), XChain [flipL l, l] (capBlk l m) []
  | (false, i), m => XChain.append (by simpa using (xChain_xDots (up i) m).whisk [] [dn i])
      (show XChain [up i, dn i] [([], .gen (.cap i), [])] [] from ⟨rfl, rfl⟩)
  | (true, i), m => XChain.append (by simpa using (xChain_xDots (up i) m).whisk [dn i] [])
      (show XChain [dn i, up i] [([], .lcap i, [])] [] from ⟨rfl, rfl⟩)

theorem capBlk_ne_nil : ∀ (l : Letter I) (m : ℕ), capBlk l m ≠ []
  | (false, _), _ => by simp [capBlk]
  | (true, _), _ => by simp [capBlk]

theorem capBlk_zero : ∀ l : Letter I, capBlk l 0 = match l with
    | (false, i) => [([], .gen (.cap i), [])]
    | (true, i) => [([], .lcap i, [])]
  | (false, _) => rfl
  | (true, _) => rfl

/-- A dot on the upward (left) leg of `ε` joins the block. -/
theorem dotUp_capBlk_dn (i : I) (m : ℕ) :
    (CMove.dot (up i)).loc.map (xwhL [] [dn i]) ++ capBlk (dn i) m = capBlk (dn i) (m + 1) := by
  simp [capBlk, xDots_succ]

/-- A dot on the upward (right) leg of `ε'` joins the block. -/
theorem dotUp_capBlk_up (i : I) (m : ℕ) :
    (CMove.dot (up i)).loc.map (xwhL [dn i] []) ++ capBlk (up i) m = capBlk (up i) (m + 1) := by
  simp [capBlk, xDots_succ]

/-! ## Evaluating short extended diagrams -/

theorem xev_append_congr (μ : X) {s r t : List (Letter I)} {L L' : List (XLayer I)}
    (M : List (XLayer I)) (hL : XChain s L r) (hL' : XChain s L' r) {c : k}
    (h : xev cs μ s r L = c • xev cs μ s r L') :
    xev cs μ s t (L ++ M) = c • xev cs μ s t (L' ++ M) := by
  rw [xev_append cs M hL, xev_append cs M hL', h, Linear.smul_comp]

theorem xev_dots_up (μ : X) (u v : List (Letter I)) (i : I) (m : ℕ) :
    xev cs μ (u ++ [up i] ++ v) (u ++ [up i] ++ v) ((xDots (up i) m).map (xwhL u v)) =
      cl D Sc μ (u ++ [up i] ++ v) (u ++ [up i] ++ v) (dotsL u i v m) := by
  rw [xDots_eq, map_xwhL_map_ofL, xev_map_ofL]
  congr 1
  simp [dotsLay, dotsL, List.map_replicate, whL]

theorem cl_dotsLay_mem_slideSetR (μ : X) (l : Letter I) (a : ℕ) :
    cl D Sc μ [l] [l] (dotsLay l a) ∈ slideSetR cs μ l := by
  have := gen_mem_slideSetR (cs := cs) (μ := μ) (l := l) a IsBub.id ⟨0, id_mem_closedPar _⟩
  rw [plcL_id] at this
  erw [Category.comp_id] at this
  exact this

theorem xev_xDots_mem_slideSetR (μ : X) (l : Letter I) (a : ℕ) {c : k} :
    c • xev cs μ [l] [l] (xDots l a) ∈ slideSetR cs μ l := by
  rw [xev_xDots]; exact Submodule.smul_mem _ _ (cl_dotsLay_mem_slideSetR cs μ l a)

/-! ## Bubbles -/

/-- **A cup creating both legs of the cap closes up to a dotted bubble.** -/
theorem isBub_cup_capBlk (μ : X) : ∀ (l : Letter I) (m : ℕ),
    IsBub cs μ (xev cs μ [] [] ((CMove.cup (flipL l)).loc ++ capBlk l m))
  | (false, i), m => by
    have e : (CMove.cup (flipL (dn i))).loc ++ capBlk (dn i) m =
        [([], .lcup i, [])] ++ (epsL i m).map ofL := by
      simp [capBlk, epsL, xDots_eq, dotsLay, dotsL, List.map_replicate, ofL]
    rw [e, xev_append cs _ (show XChain [] [([], .lcup i, [])] [up i, dn i] from ⟨rfl, rfl⟩),
      xev_lcup, xev_map_ofL, ← bubL_nat]
    exact isBub_bubL cs i μ m
  | (true, i), m => by
    have e : (CMove.cup (flipL (up i))).loc ++ capBlk (up i) m =
        (etaL i m).map ofL ++ [([], .lcap i, [])] := by
      simp [capBlk, etaL, xDots_eq, dotsLay, dotsL, List.map_replicate, ofL]
    rw [e, xev_append cs _ (XChain.of_sChain (sChain_etaL i m)), xev_lcap, xev_map_ofL,
      ← bubR_nat]
    exact isBub_bubR cs i μ m

/-! ## Downward dots on the downward leg -/

theorem xChain_dot_whisk (l : Letter I) (u v : List (Letter I)) :
    XChain (u ++ [l] ++ v) ((CMove.dot l).loc.map (xwhL u v)) (u ++ [l] ++ v) :=
  (CMove.dot l).xChain_loc.whisk u v

theorem xChain_cup_whisk (l : Letter I) (u v : List (Letter I)) :
    XChain (u ++ v) ((CMove.cup l).loc.map (xwhL u v)) (u ++ [l, flipL l] ++ v) := by
  simpa using (CMove.cup l).xChain_loc.whisk u v

theorem xChain_xDots_whisk (l : Letter I) (a : ℕ) (u v : List (Letter I)) :
    XChain (u ++ [l] ++ v) ((xDots l a).map (xwhL u v)) (u ++ [l] ++ v) :=
  (xChain_xDots l a).whisk u v

/-- **A downward dot on the right leg of `ε`** moves to its left leg ((2.3)). -/
theorem ddot_capBlk_dn (μ : X) (i : I) (m : ℕ) :
    ∃ c : k, xev cs μ [up i, dn i] []
        ((CMove.dot (dn i)).loc.map (xwhL [up i] []) ++ capBlk (dn i) m) =
      c • xev cs μ [up i, dn i] [] (capBlk (dn i) (m + 1)) := by
  -- the downward dot moves below the block of upward dots
  obtain ⟨p, hp⟩ := xev_swap' cs μ (xChain_xDots (up i) m) ((CMove.dot (dn i)).xChain_loc)
    [] [] [] [up i, dn i] [up i, dn i]
  simp only [List.nil_append, List.append_nil, CMove.dom_dot, CMove.cod_dot] at hp
  have h₁ := xChain_dot_whisk (dn i) [up i] []
  have h₂ := xChain_xDots_whisk (up i) m [] [dn i]
  simp only [List.nil_append, List.append_nil, List.cons_append] at h₁ h₂
  have e₁ : (CMove.dot (dn i)).loc.map (xwhL [up i] []) ++ capBlk (dn i) m =
      ((CMove.dot (dn i)).loc.map (xwhL [up i] []) ++ (xDots (up i) m).map (xwhL [] [dn i])) ++
        [([], .gen (.cap i), [])] := by simp [capBlk]
  rw [e₁, xev_append_congr cs μ _ (h₁.append h₂) (h₂.append h₁) hp]
  -- (2.3): the downward dot on the right leg of `ε` is a dot on its left leg
  have E := eq_2_3_b Sc i μ 1
  rw [ddotsL_one] at E
  refine ⟨zsign k p * zsign k (D.parity i * ((1 / 2 : ℕ) : ZMod 2)), ?_⟩
  rw [List.append_assoc, xev_append cs _ h₂, capBlk, xDots_succ', List.map_append,
    List.append_assoc, xev_append cs _ h₂]
  have e₂ : (CMove.dot (dn i)).loc.map (xwhL [up i] []) ++ [([], .gen (.cap i), [])] =
      ((ddotL i).map (whL [up i] []) ++ [([], Shape.cap i, [])]).map ofL := by
    simp [ofL, List.map_map, Function.comp_def, whL]
  have e₃ : (CMove.dot (up i)).loc.map (xwhL [] [dn i]) ++ [([], .gen (.cap i), [])] =
      ((dotsL [] i [] 1).map (whL [] [dn i]) ++ [([], Shape.cap i, [])]).map ofL := by
    simp [ofL, dotsL, whL]
  rw [e₂, e₃, xev_map_ofL, xev_map_ofL, E]
  simp only [Linear.comp_smul, smul_smul]
  congr 1
  rw [mul_assoc, zsign_mul_self, mul_one]

/-- **A downward dot on the left leg of `ε'`** moves to its right leg (Proposition 4.1 (4.3));
for odd `i` this adds `ε'` followed by the odd bubble. -/
theorem ddot_capBlk_up (μ : X) (i : I) (m : ℕ) :
    ∃ a b : k, xev cs μ [dn i, up i] []
        ((CMove.dot (dn i)).loc.map (xwhL [] [up i]) ++ capBlk (up i) m) =
      a • xev cs μ [dn i, up i] [] (capBlk (up i) (m + 1)) +
        b • (xev cs μ [dn i, up i] [] (capBlk (up i) m) ≫ oddBubble cs i μ) := by
  obtain ⟨p, hp⟩ := xev_swap cs μ ((CMove.dot (dn i)).xChain_loc) (xChain_xDots (up i) m)
    [] [] [] [dn i, up i] [dn i, up i]
  simp only [List.nil_append, List.append_nil, CMove.dom_dot, CMove.cod_dot] at hp
  have h₁ := xChain_dot_whisk (dn i) [] [up i]
  have h₂ := xChain_xDots_whisk (up i) m [dn i] []
  simp only [List.nil_append, List.append_nil, List.cons_append] at h₁ h₂
  have e₁ : (CMove.dot (dn i)).loc.map (xwhL [] [up i]) ++ capBlk (up i) m =
      ((CMove.dot (dn i)).loc.map (xwhL [] [up i]) ++ (xDots (up i) m).map (xwhL [dn i] [])) ++
        [([], .lcap i, [])] := by simp [capBlk]
  -- (4.3) solved for the downward dot
  have E : ∃ a b : k, dLM D Sc i μ ≫ epsP cs i μ =
      a • (uRM D Sc i μ ≫ epsP cs i μ) + b • (epsP cs i μ ≫ oddBubble cs i μ) := by
    rcases zmod2_cases (D.parity i) with hi | hi
    · exact ⟨1, 0, by rw [lemma41_eq3_one_even cs i μ hi]; simp⟩
    · refine ⟨zsign k (D.h i μ : ZMod 2), -(zsign k (D.h i μ : ZMod 2) * 2), ?_⟩
      rw [lemma41_eq3_one_odd cs i μ hi, smul_add, smul_smul, zsign_mul_self, one_smul,
        smul_smul, neg_smul, mul_comm]
      abel
  obtain ⟨a, b, E⟩ := E
  have eD : xev cs μ [dn i, up i] [] ((CMove.dot (dn i)).loc.map (xwhL [] [up i]) ++
      [([], .lcap i, [])]) = dLM D Sc i μ ≫ epsP cs i μ := by
    rw [xev_append cs _ h₁, xev_lcap]
    congr 1
    rw [show (CMove.dot (dn i)).loc.map (xwhL [] [up i]) = ((ddotL i).map (whL [] [up i])).map ofL
      by simp [List.map_map, Function.comp_def, ofL, whL], xev_map_ofL]
  have h₃ := xChain_dot_whisk (up i) [dn i] []
  simp only [List.nil_append, List.append_nil, List.cons_append] at h₃
  have eU : xev cs μ [dn i, up i] [] ((CMove.dot (up i)).loc.map (xwhL [dn i] []) ++
      [([], .lcap i, [])]) = uRM D Sc i μ ≫ epsP cs i μ := by
    rw [xev_append cs _ h₃, xev_lcap]
    congr 1
    rw [show (CMove.dot (up i)).loc.map (xwhL [dn i] []) = (dotsL [dn i] i [] 1).map ofL
      by simp [dotsL, ofL], xev_map_ofL]
  refine ⟨zsign k p * a, zsign k p * b, ?_⟩
  rw [e₁, xev_append_congr cs μ _ (h₁.append h₂) (h₂.append h₁) hp, List.append_assoc,
    xev_append cs _ h₂, eD, E, capBlk, capBlk, xDots_succ', List.map_append, List.append_assoc,
    xev_append cs _ h₂, eU, xev_append cs _ h₂, xev_lcap]
  simp only [Preadditive.comp_add, Linear.comp_smul, smul_add, smul_smul, Category.assoc]

/-! ## Zigzags -/

/-- The zigzag `(1 ⊗ ε) ∘ (η ⊗ 1)` on `Fᵢ` with `m` dots on its middle segment is `±` the
`m`-th power of the downward dot ((2.2)). -/
theorem zig_dn_left (μ : X) (i : I) (m : ℕ) :
    xev cs μ [dn i] [dn i]
        ((CMove.cup (dn i)).loc.map (xwhL [] [dn i]) ++ (capBlk (dn i) m).map (xwhL [dn i] [])) ∈
      slideSetR cs μ (dn i) := by
  have e : (CMove.cup (dn i)).loc.map (xwhL [] [dn i]) ++ (capBlk (dn i) m).map (xwhL [dn i] []) =
      (mateL i (dotsL [] i [] m)).map ofL := by
    simp [capBlk, mateL, xDots_eq, dotsLay, dotsL, List.map_replicate, whL, ofL]
  rw [e, xev_map_ofL]
  have E := cl_ddot_pow Sc i μ m
  rw [← cl_ddotsL] at E
  have : cl D Sc μ [dn i] [dn i] (mateL i (dotsL [] i [] m)) =
      zsign k (D.parity i * ((m / 2 : ℕ) : ZMod 2)) • cl D Sc μ [dn i] [dn i] (ddotsL i m) := by
    rw [E, smul_smul, zsign_mul_self, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (cl_dotsLay_mem_slideSetR cs μ (dn i) m)

/-- The zigzag `(ε ⊗ 1) ∘ (1 ⊗ η)` on `Eᵢ`, with `m` dots on the strand below: `m` dots
((1.10)). -/
theorem zig_dn_right (μ : X) (i : I) (m : ℕ) :
    xev cs μ [up i] [up i]
        ((CMove.cup (dn i)).loc.map (xwhL [up i] []) ++ (capBlk (dn i) m).map (xwhL [] [up i])) ∈
      slideSetR cs μ (up i) := by
  obtain ⟨p, hp⟩ := xev_swap' cs μ (xChain_xDots (up i) m) ((CMove.cup (dn i)).xChain_loc)
    [] [] [] [up i] [up i, dn i, up i]
  simp only [List.nil_append, List.append_nil, CMove.dom_cup, CMove.cod_cup, map_xwhL_nil,
    flipL_dn] at hp
  have h₁ := xChain_cup_whisk (dn i) [up i] []
  have h₂ := xChain_xDots_whisk (up i) m [] [dn i, up i]
  simp only [List.nil_append, List.append_nil, List.cons_append, flipL_dn] at h₁ h₂
  have e : (CMove.cup (dn i)).loc.map (xwhL [up i] []) ++ (capBlk (dn i) m).map (xwhL [] [up i]) =
      ((CMove.cup (dn i)).loc.map (xwhL [up i] []) ++
        (xDots (up i) m).map (xwhL [] [dn i, up i])) ++ [([], .gen (.cap i), [up i])] := by
    simp [capBlk]
  rw [e, xev_append_congr cs μ _ (h₁.append h₂) ((xChain_xDots (up i) m).append h₁) hp,
    List.append_assoc, xev_append cs _ (xChain_xDots (up i) m)]
  have Z : xev cs μ [up i] [up i] ((CMove.cup (dn i)).loc.map (xwhL [up i] []) ++
      [([], .gen (.cap i), [up i])]) = 𝟙 _ := by
    rw [show (CMove.cup (dn i)).loc.map (xwhL [up i] []) ++ [([], .gen (.cap i), [up i])] =
      [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])].map ofL by
        simp [ofL], xev_map_ofL, cl_zigE, cl_nil]
  rw [Z, Category.comp_id]
  simpa using xev_xDots_mem_slideSetR cs μ (up i) m (c := zsign k p)

/-- The zigzag `(ε' ⊗ 1) ∘ (1 ⊗ η')` on `Eᵢ` with `m` dots on the strand below: `±` the
dots ((6.6), first relation). -/
theorem zig_up_left (μ : X) (i : I) (m : ℕ) :
    xev cs μ [up i] [up i]
        ((CMove.cup (up i)).loc.map (xwhL [] [up i]) ++ (capBlk (up i) m).map (xwhL [up i] [])) ∈
      slideSetR cs μ (up i) := by
  obtain ⟨p, hp⟩ := xev_swap cs μ ((CMove.cup (up i)).xChain_loc) (xChain_xDots (up i) m)
    [] [] [] [up i] [up i, dn i, up i]
  simp only [List.nil_append, List.append_nil, CMove.dom_cup, CMove.cod_cup, map_xwhL_nil,
    flipL_up] at hp
  have h₁ := xChain_cup_whisk (up i) [] [up i]
  have h₂ := xChain_xDots_whisk (up i) m [up i, dn i] []
  simp only [List.nil_append, List.append_nil, List.cons_append, flipL_up] at h₁ h₂
  have e : (CMove.cup (up i)).loc.map (xwhL [] [up i]) ++ (capBlk (up i) m).map (xwhL [up i] []) =
      ((CMove.cup (up i)).loc.map (xwhL [] [up i]) ++
        (xDots (up i) m).map (xwhL [up i, dn i] [])) ++ [([up i], .lcap i, [])] := by
    simp [capBlk]
  rw [e, xev_append_congr cs μ _ (h₁.append h₂) ((xChain_xDots (up i) m).append h₁) hp,
    List.append_assoc, xev_append cs _ (xChain_xDots (up i) m)]
  have Z : xev cs μ [up i] [up i] ((CMove.cup (up i)).loc.map (xwhL [] [up i]) ++
      [([up i], .lcap i, [])]) = zsign k (ipar D i μ) • 𝟙 _ := by
    rw [← eq_6_6_a cs i μ]
    simp only [CMove.loc_cup_up, List.map_cons, List.map_nil, xwhL_mk, List.nil_append,
      List.append_nil, List.cons_append, xev_cons, xev_nil, XShape.dom, XShape.cod, cl_nil,
      Category.id_comp, Category.comp_id]
    rfl
  rw [Z, Linear.comp_smul, Category.comp_id, smul_smul]
  exact xev_xDots_mem_slideSetR cs μ (up i) m

/-- The zigzag `(ε' ⊗ 1) ∘ (1 ⊗ η')` on `Fᵢ` with `m` dots on its middle segment lies in
`slideSetR` ((6.6), second relation, and Proposition 4.1 (4.4)). -/
theorem zig_up_right (μ : X) (i : I) : ∀ m : ℕ,
    xev cs μ [dn i] [dn i]
        ((CMove.cup (up i)).loc.map (xwhL [dn i] []) ++ (capBlk (up i) m).map (xwhL [] [dn i])) ∈
      slideSetR cs μ (dn i)
  | 0 => by
    have Z : xev cs μ [dn i] [dn i] ((CMove.cup (up i)).loc.map (xwhL [dn i] []) ++
        (capBlk (up i) 0).map (xwhL [] [dn i])) = 𝟙 _ := by
      rw [← eq_6_6_b cs i μ]
      simp only [CMove.loc_cup_up, capBlk, xDots, List.replicate_zero, List.flatten_nil,
        List.map_nil, List.map_cons, xwhL_mk, List.nil_append, List.append_nil, List.cons_append,
        xev_cons, xev_nil, XShape.dom, XShape.cod, cl_nil, Category.id_comp, Category.comp_id]
      rfl
    rw [Z]
    have := cl_dotsLay_mem_slideSetR cs μ (dn i) 0
    rwa [dotsLay_zero, cl_nil] at this
  | m + 1 => by
    set REST := (capBlk (up i) m).map (xwhL [] [dn i]) with hRESTdef
    have hREST : XChain [dn i, up i, dn i] REST [dn i] := by
      simpa using (xChain_capBlk (up i) m).whisk [] [dn i]
    have IH := zig_up_right μ i m
    -- the lowest dot moves through `η'` ((4.4))
    set A : List (XLayer I) := [([], .lcup i, []), ([], .gen (.dot i), [dn i])] with hAdef
    have hA : XChain [] A [up i, dn i] := ⟨rfl, rfl, rfl⟩
    have hAw : XChain [dn i] (A.map (xwhL [dn i] [])) [dn i, up i, dn i] := by
      simpa using hA.whisk [dn i] []
    have e : (CMove.cup (up i)).loc.map (xwhL [dn i] []) ++
        (capBlk (up i) (m + 1)).map (xwhL [] [dn i]) = A.map (xwhL [dn i] []) ++ REST := by
      simp [hAdef, hRESTdef, capBlk, xDots_succ]
    have EA : xev cs (wt D μ []) [] [up i, dn i] A = etaP cs i (wt D μ []) ≫ uLM D Sc i (wt D μ []) := by
      rw [hAdef, show [([], XShape.lcup i, []), ([], XShape.gen (Shape.dot i), [dn i])] =
        [([], XShape.lcup i, ([] : List (Letter I)))] ++ (dotsL [] i [dn i] 1).map ofL by
          simp [dotsL, ofL], xev_append cs _ (show XChain [] [([], XShape.lcup i, [])]
            [up i, dn i] from ⟨rfl, rfl⟩), xev_lcup, xev_map_ofL]
    have E44 : ∃ a b : k, etaP cs i (wt D μ []) ≫ uLM D Sc i (wt D μ []) =
        a • (etaP cs i (wt D μ []) ≫ dRM D Sc i (wt D μ [])) +
          b • (oddBubble cs i (wt D μ []) ≫ etaP cs i (wt D μ [])) := by
      rcases zmod2_cases (D.parity i) with hi | hi
      · exact ⟨1, 0, by rw [lemma41_eq4_one_even cs i _ hi]; simp⟩
      · exact ⟨_, _, lemma41_eq4_one_odd cs i _ hi⟩
    obtain ⟨a, b, E44⟩ := E44
    have hA₀ : XChain [] [([], XShape.lcup i, ([] : List (Letter I)))] [up i, dn i] := ⟨rfl, rfl⟩
    have eη : ∀ s t : List (Letter I), plcW μ s t [dn i] [] [] [up i, dn i]
        (etaP cs i (wt D μ [])) =
          xev cs μ s t ([([], XShape.lcup i, ([] : List (Letter I)))].map (xwhL [dn i] [])) := by
      intro s t
      rw [xev_eq_plcW μ [dn i] [] hA₀ (by simp), xev_lcup]
    rw [e, xev_append cs _ hAw, xev_eq_plcW μ [dn i] [] hA (by simp [hAdef]), EA, E44, map_add,
      map_smul, map_smul, Preadditive.add_comp, Linear.smul_comp, Linear.smul_comp, plcW_comp,
      plcW_comp]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · -- the downward dot on the right leg of `η'` moves to the top
      set Dl := (CMove.dot (dn i)).loc.map (xwhL [up i] []) with hDl
      have hD : XChain [up i, dn i] Dl [up i, dn i] := by
        exact (CMove.dot (dn i)).xChain_loc.whisk [up i] []
      have eR : xev cs (wt D μ []) [up i, dn i] [up i, dn i] Dl = dRM D Sc i (wt D μ []) := by
        rw [hDl, show (CMove.dot (dn i)).loc.map (xwhL [up i] []) =
          ((ddotL i).map (whL [up i] [])).map ofL by
            simp [List.map_map, Function.comp_def, ofL, whL], xev_map_ofL]
      have hDne : Dl ≠ [] := by simp [hDl, ddotL, mateL]
      rw [eη, ← eR, ← xev_eq_plcW μ [dn i] [] hD hDne, Category.assoc]
      have hL₂ : XChain ([dn i] ++ [up i, dn i] ++ []) (Dl.map (xwhL [dn i] []))
          [dn i, up i, dn i] := hD.whisk [dn i] []
      have hL₁ : XChain [dn i] ([([], XShape.lcup i, ([] : List (Letter I)))].map (xwhL [dn i] []))
          ([dn i] ++ [up i, dn i] ++ []) := hA₀.whisk [dn i] []
      rw [← xev_append cs REST hL₂]
      obtain ⟨p, hp⟩ := xev_swap' cs μ (xChain_capBlk (up i) m) ((CMove.dot (dn i)).xChain_loc)
        [] [] [] ([dn i] ++ [up i, dn i] ++ []) [dn i]
      simp only [List.nil_append, List.append_nil, CMove.dom_dot, CMove.cod_dot,
        flipL_up, map_xwhL_nil] at hp
      have eL : Dl.map (xwhL [dn i] []) ++ REST =
          (CMove.dot (dn i)).loc.map (xwhL [dn i, up i] []) ++ (capBlk (up i) m).map (xwhL [] [dn i]) := by
        rw [hDl, map_xwhL_comp]; simp [hRESTdef]
      rw [eL, hp, Linear.comp_smul]
      refine Submodule.smul_mem _ _ ?_
      rw [← xev_append cs _ hL₁, ← List.append_assoc]
      have hZ : XChain [dn i] ([([], XShape.lcup i, ([] : List (Letter I)))].map (xwhL [dn i] []) ++
          (capBlk (up i) m).map (xwhL [] [dn i])) [dn i] := hL₁.append (by simpa using hREST)
      rw [xev_append cs _ hZ]
      refine slideSetR_comp ?_ ?_
      · simpa using IH
      · have := cl_dotsLay_mem_slideSetR cs μ (dn i) 1
        rwa [dotsLay_dn, ddotsL_one, ← xev_map_ofL cs μ [dn i] [dn i] (ddotL i)] at this
    · -- the odd bubble in the region to the right of `Fᵢ`
      rw [eη, Category.assoc]
      have hL₁ : XChain ([dn i] ++ [] ++ [])
          ([([], XShape.lcup i, ([] : List (Letter I)))].map (xwhL [dn i] []))
          [dn i, up i, dn i] := hA₀.whisk [dn i] []
      rw [← xev_append cs REST hL₁]
      change plcW μ [dn i] [dn i] [dn i] [] [] [] (oddBubble cs i (wt D μ [])) ≫
        xev cs μ [dn i] [dn i] (_ ++ REST) ∈ _
      refine slideSetR_comp ?_ (by simpa using IH)
      rw [plcW_apply]
      change cl D Sc μ [dn i] [dn i] [] ≫ plcL D Sc μ [dn i] [] [] [] (oddBubble cs i (wt D μ [])) ≫
        cl D Sc μ [dn i] [dn i] [] ∈ _
      rw [cl_nil]
      erw [Category.id_comp, Category.comp_id]
      exact plcL_mem_slideSetR (isBub_oddBubble cs i _) ⟨_, oddBubble_mem cs i _⟩

end OddMath.SKM
