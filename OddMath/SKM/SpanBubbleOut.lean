/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanCapsElim
import OddMath.SKM.SpanBubbleSlides

/-!
# Bubbles slide out to the rightmost region

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11.

* `bubbleProdSpan_eq`: the span of the products of bubbles (`IsBubbleProd`) is the image of `β_ν`
  (`bubbleSpan`, (1.21)); so an element of the image of `β_ν` (`IsBub`) is a linear combination
  of products of bubbles (`isBub_iff_mem_bubbleProdSpan`).
* `plcL_mem_mvSp_of_isBub`: an element of the image of `β` placed in any region of a word is a
  combination of dots on the strands to its right followed by an element of the image of `β` in the
  rightmost region. This is the iterate of the bubble slides `bubble_slide_right` ([BE2]
  Proposition 7.3, Corollary 7.4 and the mates for downward strands).
* `bubbleSlideOut`: the hypothesis `BubbleSlideOut` of the elimination of caps holds.
* `capElim_of_push`: the elimination of caps, with the cap push as its only hypothesis.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## Products of bubbles span the image of `β` -/

/-- The span of the products of bubbles in `End(1_ν)`. -/
def bubbleProdSpan (ν : X) : Submodule k (End ((pres D Sc).obj (ob D ν []))) :=
  Submodule.span k {β | IsBubbleProd cs ν β}

theorem IsBubbleProd.mem_bubbleProdSpan {ν : X}
    {β : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν [])} (hβ : IsBubbleProd cs ν β) :
    (β : End _) ∈ bubbleProdSpan cs ν :=
  Submodule.subset_span hβ

/-- The span of the products of bubbles is closed under composition. -/
theorem comp_mem_bubbleProdSpan {ν : X}
    {f g : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν [])}
    (hf : (f : End _) ∈ bubbleProdSpan cs ν) (hg : (g : End _) ∈ bubbleProdSpan cs ν) :
    (f ≫ g : End _) ∈ bubbleProdSpan cs ν := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    induction hg using Submodule.span_induction with
    | mem g hg => exact (IsBubbleProd.comp hf hg).mem_bubbleProdSpan cs
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ a hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ a hx

/-- **Products of bubbles span the image of `β_ν`.** -/
theorem bubbleProdSpan_eq (ν : X) :
    bubbleProdSpan cs ν = Subalgebra.toSubmodule (bubbleSpan cs ν) := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun β hβ => IsBubbleProd.isBub hβ
  · intro f hf
    change f ∈ Algebra.adjoin k (bubGens cs ν) at hf
    induction hf using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, n, rfl⟩ := hx
      exact (IsBubbleProd.of_bubL ν i _).mem_bubbleProdSpan cs
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one r]
      exact Submodule.smul_mem _ r ((IsBubbleProd.id (cs := cs) (ν := ν)).mem_bubbleProdSpan cs)
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy => exact comp_mem_bubbleProdSpan cs hy hx

/-- An element of the image of `β_ν` is a linear combination of products of bubbles. -/
theorem isBub_iff_mem_bubbleProdSpan {ν : X}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν [])} :
    IsBub cs ν f ↔ (f : End _) ∈ bubbleProdSpan cs ν := by
  rw [bubbleProdSpan_eq]; rfl

/-! ## Moves and casts -/

section Moves

variable {cs}

theorem mvSp_wordCast {μ : X} {w v w' v' : List (Letter I)} (hw : w = w') (hv : v = v') {c : ℕ}
    {f : (pres D Sc).obj (ob D μ w) ⟶ (pres D Sc).obj (ob D μ v)}
    (hf : f ∈ MvSp D Sc cs μ w v c) : wordCast μ hw hv f ∈ MvSp D Sc cs μ w' v' c := by
  subst hw hv; exact hf

theorem wordCast_symm_wordCast (μ : X) {s t s' t' : List (Letter I)} (hs : s = s') (ht : t = t')
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    wordCast μ hs.symm ht.symm (wordCast μ hs ht f) = f := by
  subst hs ht; rfl

/-- An element of the image of `β_μ` in the rightmost region is a move diagram without moves
followed by a combination of products of bubbles. -/
theorem bubAt_mem_mvSp_of_isBub {μ : X} (v : List (Letter I))
    {γ : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])} (hγ : IsBub cs μ γ) :
    bubAt D Sc μ v γ ∈ MvSp D Sc cs μ v v 0 := by
  rw [isBub_iff_mem_bubbleProdSpan] at hγ
  induction hγ using Submodule.span_induction with
  | mem β hβ =>
    exact Submodule.subset_span ⟨[], β, rfl, le_rfl, hβ, by
      rw [mvLay_nil, xev_nil, cl_nil, Category.id_comp]⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- `a` dots on the strand `l`, placed between `P` and `Q`, are the move diagram of `a` dot
moves. -/
theorem map_ofL_dotsLay (P : List (Letter I)) (l : Letter I) (Q : List (Letter I)) (a : ℕ) :
    ((dotsLay l a).map (whL P Q)).map ofL = mvLay (dotMv a P l Q) := by
  induction a with
  | zero => rw [dotsLay_zero]; rfl
  | succ a ih =>
    have e1 : dotsLay l (a + 1) = dotsLay l 1 ++ dotsLay l a := by
      rw [dotsLay_add, Nat.add_comm]
    have e2 : dotMv (a + 1) P l Q = Mv.dot P l Q :: dotMv a P l Q := List.replicate_succ ..
    rw [e1, e2, List.map_append, List.map_append, ih, mvLay_cons]
    congr 1
    obtain ⟨_ | _, j⟩ := l
    · simp [dotsLay, ddotsL, Mv.lay, Mv.loc, Mv.pre, Mv.post, xDotL, List.map_map,
        Function.comp_def]
    · simp [dotsLay, dotsL, Mv.lay, Mv.loc, Mv.pre, Mv.post, xDotL, xwhL, whL, ofL]

theorem plcL_dotsLay_mem_mvSp (μ : X) (P : List (Letter I)) (l : Letter I) (Q : List (Letter I))
    (a : ℕ) :
    plcL D Sc μ P Q [l] [l] (cl D Sc (wt D μ Q) [l] [l] (dotsLay l a)) ∈
      MvSp D Sc cs μ (P ++ [l] ++ Q) (P ++ [l] ++ Q) 0 := by
  rw [plcL_cl, ← xev_map_ofL cs, map_ofL_dotsLay]
  exact xev_mvLay_mem_mvSp cs (mvChain_dotMv a P l Q) (by simp)

end Moves

/-! ## Nested placements -/

section Nested

/-- A closed 2-morphism to the right of the strand `l`, placed between `P` and `Q`. -/
theorem plcL_plcL_right (μ : X) (P Q : List (Letter I)) (l : Letter I)
    (f : (pres D Sc).obj (ob D (wt D μ Q) []) ⟶ (pres D Sc).obj (ob D (wt D μ Q) [])) :
    plcL D Sc μ P Q [l] [l] (plcL D Sc (wt D μ Q) [l] [] [] [] f) =
      wordCast μ (by simp) (by simp) (plcL D Sc μ (P ++ [l]) Q [] [] f) := by
  have hf := mem_span_cl (wt D μ Q) f
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, -, rfl⟩ := hf
    have e := plcL_cl D Sc (wt D μ Q) [l] [] [] [] L
    erw [e, plcL_cl, plcL_cl, wordCast_cl]
    simp
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, hx]

/-- A closed 2-morphism to the left of the strand `l`, placed between `P` and `Q`. -/
theorem plcL_plcL_left (μ : X) (P Q : List (Letter I)) (l : Letter I)
    (f : (pres D Sc).obj (ob D (wt D μ (l :: Q)) []) ⟶
      (pres D Sc).obj (ob D (wt D μ (l :: Q)) [])) :
    plcL D Sc μ P Q [l] [l] (plcL D Sc (wt D μ Q) [] [l] [] [] f) =
      wordCast μ (by simp) (by simp) (plcL D Sc μ P (l :: Q) [] [] f) := by
  have hf := mem_span_cl (wt D μ (l :: Q)) f
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, -, rfl⟩ := hf
    have e := plcL_cl D Sc (wt D μ Q) [] [l] [] [] L
    erw [e, plcL_cl, plcL_cl, wordCast_cl]
    simp
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, hx]

end Nested

/-! ## Bubbles slide out -/

variable {cs}

/-- The placement of the right slide set of the strand `l` between `P` and `Q` lies in the span
of move diagrams followed by bubbles, provided the bubbles to the right of `l` slide out. -/
theorem plcL_slideSetR_mem_mvSp {μ : X} {P Q : List (Letter I)} {l : Letter I}
    (ih : ∀ (P' : List (Letter I))
      (γ : (pres D Sc).obj (ob D (wt D μ Q) []) ⟶ (pres D Sc).obj (ob D (wt D μ Q) [])),
      IsBub cs (wt D μ Q) γ →
        plcL D Sc μ P' Q [] [] γ ∈ MvSp D Sc cs μ (P' ++ [] ++ Q) (P' ++ [] ++ Q) 0)
    {f} (hf : f ∈ slideSetR cs (wt D μ Q) l) :
    plcL D Sc μ P Q [l] [l] f ∈ MvSp D Sc cs μ (P ++ [l] ++ Q) (P ++ [l] ++ Q) 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, γ, hγ, -, rfl⟩ := hf
    rw [plcL_comp, plcL_plcL_right]
    have h2 := mvSp_wordCast (w' := P ++ [l] ++ Q) (v' := P ++ [l] ++ Q) (by simp) (by simp)
      (ih (P ++ [l]) γ hγ)
    simpa using mvSp_comp cs (plcL_dotsLay_mem_mvSp μ P l Q a) h2
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- **Bubbles slide out to the rightmost region**: an element of the image of `β` placed between
the strands `P` and `Q` is a combination of dots on the strands of `Q` followed by products of
bubbles in the rightmost region ([BE2] Proposition 7.3, Corollary 7.4 and their mates, iterated
over the strands of `Q`). -/
theorem plcL_mem_mvSp_of_isBub (μ : X) :
    ∀ (Q P : List (Letter I))
      (γ : (pres D Sc).obj (ob D (wt D μ Q) []) ⟶ (pres D Sc).obj (ob D (wt D μ Q) [])),
      IsBub cs (wt D μ Q) γ →
        plcL D Sc μ P Q [] [] γ ∈ MvSp D Sc cs μ (P ++ [] ++ Q) (P ++ [] ++ Q) 0
  | [], P, γ, hγ => by
    have h : P ++ [] ++ [] = P := by simp
    have E : plcL D Sc μ P [] [] [] γ = wordCast μ h.symm h.symm (bubAt D Sc μ P γ) :=
      (wordCast_symm_wordCast μ h h _).symm
    rw [E]
    exact mvSp_wordCast _ _ (bubAt_mem_mvSp_of_isBub P hγ)
  | l :: Q, P, γ, hγ => by
    have hs := bubble_slide_right cs (wt D μ Q) l hγ
    have h1 := plcL_slideSetR_mem_mvSp (P := P) (plcL_mem_mvSp_of_isBub μ Q) hs
    rw [plcL_plcL_left] at h1
    have h2 := mvSp_wordCast (w' := P ++ [] ++ l :: Q) (v' := P ++ [] ++ l :: Q) (by simp)
      (by simp) h1
    rwa [wordCast_symm_wordCast] at h2

variable (D Sc cs) in
/-- **The bubble slides of the elimination of caps hold.** -/
theorem bubbleSlideOut : BubbleSlideOut D Sc cs :=
  fun μ P Q β hβ => plcL_mem_mvSp_of_isBub μ Q P β hβ.isBub

/-- **Elimination of caps**, given the cap push: every extended diagram `E_{w₀} 1_μ → E_v 1_μ`
with at most `c` crossings is a combination of move diagrams with at most `c` crossings followed
by products of bubbles in the rightmost region, modulo 2-morphisms factoring through sequences
shorter than `w₀`. -/
theorem capElim_of_push (μ : X) (w₀ : List (Letter I))
    (hP : ∀ c, LowHyp cs μ w₀ c → ∀ ms, PushHyp cs μ w₀ c ms) :
    ∀ (c : ℕ) (v : List (Letter I)) (L : List (XLayer I)), xcnt L ≤ c →
      xev cs μ w₀ v L ∈ CapTarget D Sc cs μ w₀ v c :=
  capElim μ w₀ (bubbleSlideOut D Sc cs) hP

end OddMath.SKM
