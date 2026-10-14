/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanCaps

/-!
# Elimination of caps, given the cap push

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11. As in the proof of KL III
Proposition 3.11, every diagram `E_{w₀} 1_μ → E_v 1_μ` with at most `c` crossings lies in
`CapTarget c`: it is a combination of move diagrams (dots, crossings, cups; no caps) with at most
`c` crossings followed by products of bubbles in the rightmost region, modulo 2-morphisms factoring
through sequences shorter than `w₀`.

The argument is by induction on the number of crossings and then on the number of layers: a
diagram is a diagram with one layer less followed by one generator.

* Dots, crossings (upward and leftward), cups `η` and `η'` are moves.
* The `♦`-cup with label `n` is, by (5.11) (`eq_5_11`), a combination of a bubble in the region
  of the cup, the cup `η'` and dots; for `n ≥ ⟨hᵢ, λ⟩` it is zero. The `♦`-cap is, by (5.12)
  (`eq_5_12`), a combination of dots, the cap `ε'` and a bubble.
* Caps `ε`, `ε'` are pushed down through the move diagram (the cap push, `PushHyp`).
* A bubble in a region of the top of a move diagram is moved to the rightmost region by the bubble
  slides (`BubbleSlideOut`).

This file proves the induction (`capElim`) from two inputs, which are explicit hypotheses:

* `BubbleSlideOut`: a product of bubbles placed in any region is a combination of dots on the
  strands to its right followed by products of bubbles in the rightmost region ([BE2]
  Proposition 7.3 and Corollary 7.4, and their mates for downward strands);
* the cap push: assuming the statement for fewer crossings (`LowHyp c`), a cap block
  (`capBlk`) on top of a move diagram lies in `CapTarget` (`PushHyp c ms`), as in KL III.

The cap push for a move diagram without moves (`pushHyp_nil`: the diagram factors through a
shorter sequence), for a move away from the block (`push_disjL`, `push_disjR`: super
interchange) and for a dot on the left leg of the cap (`push_dotA`) are proved here; the remaining
steps (`PushGoal`: a dot, crossing or cup meeting the block) need the local relations of the cap
block. For odd `i`, moving a dot around `ε'` or `η'` ((4.3), (4.4))
produces twice an odd bubble times a diagram with the same number of crossings; it is a bubble
term, handled by `BubbleSlideOut`, not a lower term.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## Bubbles in the regions of a move diagram -/

variable (D Sc) in
/-- **Bubbles slide out to the rightmost region**: a product of bubbles placed between the
strands `P` and `Q` is a combination of dots on the strands followed by products of bubbles in the
rightmost region ([BE2] Proposition 7.3, Corollary 7.4 and their mates). An input of the
elimination of caps, taken as a hypothesis. -/
def BubbleSlideOut : Prop :=
  ∀ (μ : X) (P Q : List (Letter I))
    (β : (pres D Sc).obj (ob D (wt D μ Q) []) ⟶ (pres D Sc).obj (ob D (wt D μ Q) [])),
    IsBubbleProd cs (wt D μ Q) β →
      plcL D Sc μ P Q [] [] β ∈ MvSp D Sc cs μ (P ++ [] ++ Q) (P ++ [] ++ Q) 0

variable {cs}

theorem capTarget_comp_bubble (hS : BubbleSlideOut D Sc cs) {μ : X} {w₀ P Q : List (Letter I)}
    {c : ℕ} {f} (hf : f ∈ CapTarget D Sc cs μ w₀ (P ++ [] ++ Q) c)
    {β : (pres D Sc).obj (ob D (wt D μ Q) []) ⟶ (pres D Sc).obj (ob D (wt D μ Q) [])}
    (hβ : IsBubbleProd cs (wt D μ Q) β) :
    f ≫ plcL D Sc μ P Q [] [] β ∈ CapTarget D Sc cs μ w₀ (P ++ [] ++ Q) c := by
  simpa using capTarget_comp_mvSp cs hf (hS μ P Q β hβ)

/-! ## Generators as moves -/

theorem map_ofL_dotsL (u : List (Letter I)) (i : I) (v a b : List (Letter I)) (n : ℕ) :
    ((dotsL u i v n).map (whL a b)).map ofL = mvLay (dotMv n (a ++ u) (up i) (v ++ b)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e1 : dotsL u i v (n + 1) = (u, Shape.dot i, v) :: dotsL u i v n := List.replicate_succ ..
    have e2 : dotMv (n + 1) (a ++ u) (up i) (v ++ b) =
        Mv.dot (a ++ u) (up i) (v ++ b) :: dotMv n (a ++ u) (up i) (v ++ b) := List.replicate_succ ..
    rw [e1, e2, List.map_cons, List.map_cons, ih, mvLay_cons]
    simp [Mv.lay, Mv.loc, Mv.pre, Mv.post, xDotL, xwhL, whL, ofL]

theorem plcL_dotsL_eq (μ : X) (a b u v : List (Letter I)) (i : I) (n : ℕ) :
    plcL D Sc μ a b (u ++ [up i] ++ v) (u ++ [up i] ++ v)
        (cl D Sc (wt D μ b) (u ++ [up i] ++ v) (u ++ [up i] ++ v) (dotsL u i v n)) =
      xev cs μ (a ++ (u ++ [up i] ++ v) ++ b) (a ++ (u ++ [up i] ++ v) ++ b)
        (mvLay (dotMv n (a ++ u) (up i) (v ++ b))) := by
  rw [plcL_cl, ← map_ofL_dotsL, xev_map_ofL]

theorem mvChain_dotMv' (n : ℕ) (a u : List (Letter I)) (i : I) (v b : List (Letter I)) :
    MvChain (a ++ (u ++ [up i] ++ v) ++ b) (dotMv n (a ++ u) (up i) (v ++ b))
      (a ++ (u ++ [up i] ++ v) ++ b) := by
  simpa using mvChain_dotMv n (a ++ u) (up i) (v ++ b)

theorem plcL_etaP_eq (μ : X) (a b : List (Letter I)) (i : I) :
    plcL D Sc μ a b [] [up i, dn i] (etaP cs i (wt D μ b)) =
      xev cs μ (a ++ [] ++ b) (a ++ [up i, dn i] ++ b) (Mv.cup a (up i) b).lay := by
  rw [← xev_lcup, plcL_xev]; rfl

theorem plcL_epsP_eq (μ : X) (a b : List (Letter I)) (i : I) :
    plcL D Sc μ a b [dn i, up i] [] (epsP cs i (wt D μ b)) =
      xev cs μ (a ++ [dn i, up i] ++ b) (a ++ [] ++ b) ((xCapL (up i)).map (xwhL a b)) := by
  rw [← xev_lcap, plcL_xev]; rfl

/-! ## The induction hypotheses -/

section Push

variable {μ : X} {w₀ : List (Letter I)}

variable (cs μ w₀) in
/-- The induction hypothesis on the number of crossings. -/
def LowHyp (c : ℕ) : Prop :=
  ∀ c' < c, ∀ (v : List (Letter I)) (L : List (XLayer I)), xcnt L ≤ c' →
    xev cs μ w₀ v L ∈ CapTarget D Sc cs μ w₀ v c'

theorem capT_of_leL {v : List (Letter I)} {c c' t : ℕ} (hF : LowHyp cs μ w₀ c) (hc : c' < c)
    (ht : c' ≤ t) {f} (hf : f ∈ LeL D Sc cs μ w₀ v c') : f ∈ CapTarget D Sc cs μ w₀ v t := by
  refine capTarget_mono cs ht ?_
  refine (Submodule.span_le.mpr ?_) hf
  rintro _ ⟨L, hL, rfl⟩
  exact hF c' hc v L hL

theorem capT_of_sub {v : List (Letter I)} {c c' t : ℕ} (hF : LowHyp cs μ w₀ c) (hc : c' < c)
    (ht : c' ≤ t) {a b} (h : a - b ∈ LeL D Sc cs μ w₀ v c') (hb : b ∈ CapTarget D Sc cs μ w₀ v t) :
    a ∈ CapTarget D Sc cs μ w₀ v t := by
  have := Submodule.add_mem _ (capT_of_leL hF hc ht h) hb
  simpa using this

variable (cs μ w₀) in
/-- **The cap push** for a move diagram `ms`: a cap block on top of `ms` lies in `CapTarget`. -/
def PushHyp (c : ℕ) (ms : List (Mv I)) : Prop :=
  ∀ (P S Q : List (Letter I)) (l : Letter I) (d : ℕ),
    MvChain w₀ ms (P ++ [flipL l] ++ S ++ [l] ++ Q) → xcnt (mvLay ms) + S.length ≤ c →
    xev cs μ w₀ (P ++ S ++ Q) (mvLay ms ++ (capBlk S l d).map (xwhL P Q)) ∈
      CapTarget D Sc cs μ w₀ (P ++ S ++ Q) (xcnt (mvLay ms) + S.length)

/-- The cap push without moves: the diagram factors through a shorter sequence. -/
theorem pushHyp_nil (c : ℕ) : PushHyp cs μ w₀ c [] := by
  intro P S Q l d h _
  have h' : w₀ = P ++ [flipL l] ++ S ++ [l] ++ Q := h
  subst h'
  refine Submodule.mem_sup_right ?_
  have := xev_mem_thruShort cs (μ := μ) (w₀ := P ++ [flipL l] ++ S ++ [l] ++ Q)
    (v := P ++ S ++ Q) (u := P ++ S ++ Q) ((capBlk S l d).map (xwhL P Q)) [] (by simp)
  rw [xev_nil, cl_nil, Category.comp_id] at this
  simpa using this

/-- Composing with a cap preserves `CapTarget`, given the cap push. -/
theorem capTarget_comp_cap {c c₁ : ℕ} (hP : ∀ ms, PushHyp cs μ w₀ c ms) (hc₁ : c₁ ≤ c)
    {P Q : List (Letter I)} {l : Letter I} {f}
    (hf : f ∈ CapTarget D Sc cs μ w₀ (P ++ [flipL l, l] ++ Q) c₁) :
    f ≫ xev cs μ (P ++ [flipL l, l] ++ Q) (P ++ [] ++ Q) ((xCapL l).map (xwhL P Q)) ∈
      CapTarget D Sc cs μ w₀ (P ++ [] ++ Q) c₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
  rw [Preadditive.add_comp]
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (thruShort_comp hb _))
  clear hf hb
  induction ha using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨ms, β, hch, hcc, hβ, rfl⟩ := hg
    obtain ⟨p, hp⟩ := bubAt_comp_xev cs (μ := μ) (s := P ++ [flipL l, l] ++ Q)
      (t := P ++ [] ++ Q) ((xCapL l).map (xwhL P Q)) hβ
    rw [Category.assoc, hp, Linear.comp_smul, ← Category.assoc,
      ← xev_append cs _ hch.xChain]
    refine Submodule.smul_mem _ _ ?_
    have h := hP ms P [] Q l 0 (by simpa using hch) (by simp; omega)
    rw [capBlk_nil, List.length_nil, add_zero] at h
    exact capTarget_mono cs hcc (capTarget_comp_bubAt cs h hβ)
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

/-! ## The `♦`-cups and `♦`-caps -/

/-- (5.11): composing with a `♦`-cup preserves `CapTarget`. -/
theorem capTarget_comp_dcup (hS : BubbleSlideOut D Sc cs) {c : ℕ} {a b : List (Letter I)}
    (i : I) (n : ℕ) {f} (hf : f ∈ CapTarget D Sc cs μ w₀ (a ++ [] ++ b) c) :
    f ≫ xev cs μ (a ++ [] ++ b) (a ++ [up i, dn i] ++ b) [(a, .gen (.dcup i n), b)] ∈
      CapTarget D Sc cs μ w₀ (a ++ [up i, dn i] ++ b) c := by
  have e : xev cs μ (a ++ [] ++ b) (a ++ [up i, dn i] ++ b) [(a, .gen (.dcup i n), b)] =
      plcL D Sc μ a b [] [up i, dn i] (cl D Sc (wt D μ b) [] [up i, dn i] (dcupL i n)) := by
    rw [plcL_cl, ← xev_map_ofL cs]
    congr 1
    simp [dcupL, whL, ofL]
  rw [e]
  by_cases hn : (n : ℤ) < D.h i (wt D μ b)
  · rw [eq_5_11 cs i _ n hn, dcupRHS, map_sum, Preadditive.comp_sum]
    refine Submodule.sum_mem _ fun r _ => ?_
    rw [map_smul, Linear.comp_smul]
    refine Submodule.smul_mem _ _ ?_
    rw [plcL_comp, plcL_comp, ← Category.assoc, ← Category.assoc]
    have h1 := capTarget_comp_bubble hS hf (IsBubbleProd.of_bubR _ i (-(n : ℤ) - r - 2))
    have h2 := capTarget_comp_mv cs h1 (Mv.cup a (up i) b) rfl
    rw [Mv.xcnt_lay, show xcnt (Mv.cup a (up i) b).loc = 0 by simp [Mv.loc], add_zero] at h2
    have h2' : (f ≫ plcL D Sc μ a b [] [] (bubR cs i (wt D μ b) (-(n : ℤ) - r - 2))) ≫
        plcL D Sc μ a b [] [up i, dn i] (etaP cs i (wt D μ b)) ∈
          CapTarget D Sc cs μ w₀ (a ++ [up i, dn i] ++ b) c := by
      rw [plcL_etaP_eq]; exact h2
    have h3 := capTarget_comp_mvs cs h2' (mvChain_dotMv' r a [] i [dn i] b)
    rw [xcnt_mvLay_dotMv, add_zero] at h3
    have hd : plcL D Sc μ a b [up i, dn i] [up i, dn i]
        (cl D Sc (wt D μ b) [up i, dn i] [up i, dn i] (dotsL [] i [dn i] r)) =
        xev cs μ (a ++ [up i, dn i] ++ b) (a ++ [up i, dn i] ++ b)
          (mvLay (dotMv r (a ++ []) (up i) ([dn i] ++ b))) :=
      plcL_dotsL_eq μ a b [] [dn i] i r
    rw [hd]
    exact h3
  · rw [cl_dcupZero Sc i _ n (by omega), map_zero, Limits.comp_zero]
    exact Submodule.zero_mem _

/-- (5.12): composing with a `♦`-cap preserves `CapTarget`, given the cap push. -/
theorem capTarget_comp_dcap (hS : BubbleSlideOut D Sc cs) {c c₁ : ℕ}
    (hP : ∀ ms, PushHyp cs μ w₀ c ms) (hc₁ : c₁ ≤ c) {a b : List (Letter I)}
    (i : I) (n : ℕ) {f} (hf : f ∈ CapTarget D Sc cs μ w₀ (a ++ [dn i, up i] ++ b) c₁) :
    f ≫ xev cs μ (a ++ [dn i, up i] ++ b) (a ++ [] ++ b) [(a, .gen (.dcap i n), b)] ∈
      CapTarget D Sc cs μ w₀ (a ++ [] ++ b) c₁ := by
  have e : xev cs μ (a ++ [dn i, up i] ++ b) (a ++ [] ++ b) [(a, .gen (.dcap i n), b)] =
      plcL D Sc μ a b [dn i, up i] [] (cl D Sc (wt D μ b) [dn i, up i] [] (dcapL i n)) := by
    rw [plcL_cl, ← xev_map_ofL cs]
    congr 1
    simp [dcapL, whL, ofL]
  rw [e]
  by_cases hn : (n : ℤ) < -D.h i (wt D μ b)
  · rw [eq_5_12 cs i _ n hn, dcapRHS, map_sum, Preadditive.comp_sum]
    refine Submodule.sum_mem _ fun r _ => ?_
    rw [map_smul, Linear.comp_smul]
    refine Submodule.smul_mem _ _ ?_
    rw [plcL_comp, plcL_comp, ← Category.assoc, ← Category.assoc]
    have hd : plcL D Sc μ a b [dn i, up i] [dn i, up i]
        (cl D Sc (wt D μ b) [dn i, up i] [dn i, up i] (dotsL [dn i] i [] r)) =
        xev cs μ (a ++ [dn i, up i] ++ b) (a ++ [dn i, up i] ++ b)
          (mvLay (dotMv r (a ++ [dn i]) (up i) ([] ++ b))) :=
      plcL_dotsL_eq μ a b [dn i] [] i r
    have h1 := capTarget_comp_mvs cs hf (mvChain_dotMv' r a [dn i] i [] b)
    rw [xcnt_mvLay_dotMv, add_zero] at h1
    have h1' : f ≫ plcL D Sc μ a b [dn i, up i] [dn i, up i]
        (cl D Sc (wt D μ b) [dn i, up i] [dn i, up i] (dotsL [dn i] i [] r)) ∈
          CapTarget D Sc cs μ w₀ (a ++ [flipL (up i), up i] ++ b) c₁ := by
      rw [hd]; exact h1
    have h2 := capTarget_comp_cap hP hc₁ (P := a) (Q := b) (l := up i) h1'
    have h2' : (f ≫ plcL D Sc μ a b [dn i, up i] [dn i, up i]
        (cl D Sc (wt D μ b) [dn i, up i] [dn i, up i] (dotsL [dn i] i [] r))) ≫
        plcL D Sc μ a b [dn i, up i] [] (epsP cs i (wt D μ b)) ∈
          CapTarget D Sc cs μ w₀ (a ++ [] ++ b) c₁ := by
      rw [plcL_epsP_eq]; exact h2
    exact capTarget_comp_bubble hS h2' (IsBubbleProd.of_bubL _ i _)
  · rw [cl_dcapZero Sc i _ n (by omega), map_zero, Limits.comp_zero]
    exact Submodule.zero_mem _

/-! ## Elimination of caps -/

theorem capTarget_snoc_mv {c : ℕ} {L : List (XLayer I)} (x : XLayer I)
    (hL : xev cs μ w₀ (x.1 ++ x.2.1.dom ++ x.2.2) L ∈
      CapTarget D Sc cs μ w₀ (x.1 ++ x.2.1.dom ++ x.2.2) c)
    (hch : XChain w₀ L (x.1 ++ x.2.1.dom ++ x.2.2)) (m : Mv I) (hlay : m.lay = [x])
    (hsrc : m.src = x.1 ++ x.2.1.dom ++ x.2.2) (htgt : m.tgt = x.1 ++ x.2.1.cod ++ x.2.2) :
    xev cs μ w₀ (x.1 ++ x.2.1.cod ++ x.2.2) (L ++ [x]) ∈
      CapTarget D Sc cs μ w₀ (x.1 ++ x.2.1.cod ++ x.2.2) (c + xcnt [x]) := by
  have h := capTarget_comp_mv cs hL m hsrc
  rw [htgt, hlay] at h
  rw [xev_append cs _ hch]
  exact h

variable (μ w₀) in
/-- **Elimination of caps**, given the bubble slides and the cap push: every extended diagram
`E_{w₀} 1_μ → E_v 1_μ` with at most `c` crossings is a combination of move diagrams with at most
`c` crossings followed by products of bubbles in the rightmost region, modulo 2-morphisms factoring
through sequences shorter than `w₀`. -/
theorem capElim (hS : BubbleSlideOut D Sc cs)
    (hP : ∀ c, LowHyp cs μ w₀ c → ∀ ms, PushHyp cs μ w₀ c ms) :
    ∀ (c : ℕ) (v : List (Letter I)) (L : List (XLayer I)), xcnt L ≤ c →
      xev cs μ w₀ v L ∈ CapTarget D Sc cs μ w₀ v c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
  have hF : LowHyp cs μ w₀ c := fun c' hc' v L hL => ihc c' hc' v L hL
  have hPc := hP c hF
  suffices H : ∀ (L : List (XLayer I)) (v : List (Letter I)), xcnt L ≤ c →
      xev cs μ w₀ v L ∈ CapTarget D Sc cs μ w₀ v (xcnt L) from
    fun v L hL => capTarget_mono cs hL (H L v hL)
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro v _
    by_cases h : w₀ = v
    · subst h
      exact Submodule.mem_sup_left (xev_mvLay_mem_mvSp cs (ms := []) rfl le_rfl)
    · rw [xev_of_not cs (show ¬ XChain w₀ [] v from h)]; exact Submodule.zero_mem _
  | append_singleton L x ih =>
    intro v hL
    rw [xcnt_append] at hL ⊢
    by_cases h : XChain w₀ (L ++ [x]) v
    · obtain ⟨r, h1, h2⟩ := XChain.split h
      obtain ⟨hr, hv⟩ := h2
      have hv' : x.1 ++ x.2.1.cod ++ x.2.2 = v := hv
      subst hr hv'
      have hL' := ih (x.1 ++ x.2.1.dom ++ x.2.2) (by omega)
      obtain ⟨a, g, b⟩ := x
      cases g with
      | gen g =>
        cases g with
        | dot i =>
          exact capTarget_snoc_mv _ hL' h1 (Mv.dot a (up i) b) (by simp [Mv.lay, Mv.loc,
            Mv.pre, Mv.post, xDotL, xwhL]) rfl rfl
        | cross i j =>
          exact capTarget_snoc_mv _ hL' h1 (Mv.cross a (up i) (up j) b) (by simp [Mv.lay,
            Mv.loc, Mv.pre, Mv.post, xCrL, xwhL]) rfl rfl
        | cup i =>
          exact capTarget_snoc_mv _ hL' h1 (Mv.cup a (dn i) b) (by simp [Mv.lay, Mv.loc,
            Mv.pre, Mv.post, xCupL, xwhL]) rfl rfl
        | lcross i j =>
          exact capTarget_snoc_mv _ hL' h1 (Mv.cross a (dn i) (up j) b) (by simp [Mv.lay,
            Mv.loc, Mv.pre, Mv.post, xCrL, xwhL]) rfl rfl
        | cap i =>
          rw [xev_append cs _ h1]
          have e : xev cs μ (a ++ [up i, dn i] ++ b) (a ++ [] ++ b) [(a, .gen (.cap i), b)] =
              xev cs μ (a ++ [flipL (dn i), dn i] ++ b) (a ++ [] ++ b)
                ((xCapL (dn i)).map (xwhL a b)) := by
            congr 1; simp [xCapL, xwhL]
          have := capTarget_comp_cap hPc (c₁ := xcnt L) (by omega) (P := a) (Q := b)
            (l := dn i) hL'
          rw [← e] at this
          rw [show xcnt [(a, XShape.gen (Shape.cap i), b)] = 0 by
            simp [XShape.isCross, Shape.isCross], add_zero]
          exact this
        | dcup i n =>
          rw [xev_append cs _ h1]
          rw [show xcnt [(a, XShape.gen (Shape.dcup i n), b)] = 0 by
            simp [XShape.isCross, Shape.isCross], add_zero]
          exact capTarget_comp_dcup hS i n hL'
        | dcap i n =>
          rw [xev_append cs _ h1]
          rw [show xcnt [(a, XShape.gen (Shape.dcap i n), b)] = 0 by
            simp [XShape.isCross, Shape.isCross], add_zero]
          exact capTarget_comp_dcap hS hPc (c₁ := xcnt L) (by omega) i n hL'
      | lcup i =>
        exact capTarget_snoc_mv _ hL' h1 (Mv.cup a (up i) b) (by simp [Mv.lay, Mv.loc,
          Mv.pre, Mv.post, xCupL, xwhL]) rfl rfl
      | lcap i =>
        rw [xev_append cs _ h1]
        have e : xev cs μ (a ++ [dn i, up i] ++ b) (a ++ [] ++ b) [(a, .lcap i, b)] =
            xev cs μ (a ++ [flipL (up i), up i] ++ b) (a ++ [] ++ b)
              ((xCapL (up i)).map (xwhL a b)) := by
          congr 1; simp [xCapL, xwhL]
        have := capTarget_comp_cap hPc (c₁ := xcnt L) (by omega) (P := a) (Q := b)
          (l := up i) hL'
        rw [← e] at this
        rw [show xcnt [(a, XShape.lcap i, b)] = 0 by simp [XShape.isCross], add_zero]
        exact this
    · rw [xev_of_not cs h]; exact Submodule.zero_mem _

variable (cs μ w₀) in
/-- The step of the cap push: the goal for `ms ++ [m]`. -/
def PushGoal (c : ℕ) (ms : List (Mv I)) (m : Mv I) : Prop :=
  ∀ (P S Q : List (Letter I)) (l : Letter I) (d : ℕ),
    m.tgt = P ++ [flipL l] ++ S ++ [l] ++ Q → xcnt (mvLay ms) + xcnt m.lay + S.length ≤ c →
    xev cs μ w₀ (P ++ S ++ Q) (mvLay ms ++ m.lay ++ (capBlk S l d).map (xwhL P Q)) ∈
      CapTarget D Sc cs μ w₀ (P ++ S ++ Q) (xcnt (mvLay ms) + xcnt m.lay + S.length)

/-- The cap push follows from its steps. -/
theorem pushHyp_of_goal {c : ℕ}
    (hG : ∀ ms m, PushHyp cs μ w₀ c ms → MvChain w₀ ms m.src → PushGoal cs μ w₀ c ms m) :
    ∀ ms, PushHyp cs μ w₀ c ms := by
  intro ms
  induction ms using List.reverseRecOn with
  | nil => exact pushHyp_nil c
  | append_singleton ms m ih =>
    intro P S Q l d hch hc
    obtain ⟨hms, htgt⟩ := MvChain.of_snoc hch
    rw [mvLay_append, mvLay_singleton] at hc ⊢
    rw [xcnt_append] at hc ⊢
    exact hG ms m ih hms P S Q l d htgt hc

theorem capTarget_mem_of_smul {v : List (Letter I)} {t : ℕ} {a b} (p : ZMod 2) (h : a = zsign k p • b)
    (hb : b ∈ CapTarget D Sc cs μ w₀ v t) : a ∈ CapTarget D Sc cs μ w₀ v t := by
  rw [h]; exact Submodule.smul_mem _ _ hb

/-- **The cap push past a move to the left of the block** (super interchange). -/
theorem push_disjL {c : ℕ} {ms : List (Mv I)} (hIH : PushHyp cs μ w₀ c ms) {m : Mv I}
    (hms : MvChain w₀ ms m.src) {P S Q : List (Letter I)} {l : Letter I} (d : ℕ)
    (R : List (Letter I)) (hP : P = m.pre ++ m.ltgt ++ R)
    (hv : m.post = R ++ [flipL l] ++ S ++ [l] ++ Q)
    (hc : xcnt (mvLay ms) + xcnt m.lay + S.length ≤ c) :
    xev cs μ w₀ (P ++ S ++ Q) (mvLay ms ++ m.lay ++ (capBlk S l d).map (xwhL P Q)) ∈
      CapTarget D Sc cs μ w₀ (P ++ S ++ Q) (xcnt (mvLay ms) + xcnt m.lay + S.length) := by
  subst hP
  have hB : XChain (R ++ [flipL l] ++ S ++ [l]) ((capBlk S l d).map (xwhL R [])) (R ++ S) := by
    simpa using (xChain_capBlk S l d).whisk R []
  have hsrc : m.src = m.pre ++ (m.lsrc ++ (R ++ [flipL l] ++ S ++ [l])) ++ Q := by
    rw [Mv.src, hv]; simp
  obtain ⟨p, hp⟩ := xev_ichg cs μ (S := w₀) (T := m.pre ++ m.ltgt ++ R ++ S ++ Q) (mvLay ms) []
    m.pre Q m.xChain_loc hB (hsrc ▸ hms.xChain)
  set m' := m.reCtx m.pre (R ++ S ++ Q)
  have e₁ : mvLay ms ++ m.lay ++ (capBlk S l d).map (xwhL (m.pre ++ m.ltgt ++ R) Q) =
      mvLay ms ++ m.loc.map (xwhL m.pre (R ++ [flipL l] ++ S ++ [l] ++ Q)) ++
        ((capBlk S l d).map (xwhL R [])).map (xwhL (m.pre ++ m.ltgt) Q) ++ [] := by
    rw [Mv.lay, hv, map_xwhL_xwhL]; simp
  have e₂ : mvLay ms ++ ((capBlk S l d).map (xwhL R [])).map (xwhL (m.pre ++ m.lsrc) Q) ++
      m.loc.map (xwhL m.pre (R ++ S ++ Q)) ++ [] =
      mvLay ms ++ (capBlk S l d).map (xwhL (m.pre ++ m.lsrc ++ R) Q) ++ m'.lay := by
    rw [map_xwhL_xwhL]; simp [m', Mv.lay]
  rw [e₁]
  refine capTarget_mem_of_smul p hp ?_
  rw [e₂]
  have hsrc' : m.src = (m.pre ++ m.lsrc ++ R) ++ [flipL l] ++ S ++ [l] ++ Q := by
    rw [Mv.src, hv]; simp
  have h1 := hIH (m.pre ++ m.lsrc ++ R) S Q l d (hsrc' ▸ hms) (by simp at hc ⊢; omega)
  have hm' : m'.src = m.pre ++ m.lsrc ++ R ++ S ++ Q := by simp [m', Mv.src]
  have h2 := capTarget_comp_mv cs h1 m' hm'
  have hm't : m'.tgt = m.pre ++ m.ltgt ++ R ++ S ++ Q := by simp [m', Mv.tgt]
  rw [hm't] at h2
  have hc1 : XChain w₀ (mvLay ms ++ (capBlk S l d).map (xwhL (m.pre ++ m.lsrc ++ R) Q))
      (m.pre ++ m.lsrc ++ R ++ S ++ Q) :=
    (hsrc' ▸ hms.xChain).append (by
      simpa using (xChain_capBlk S l d).whisk (m.pre ++ m.lsrc ++ R) Q)
  rw [← xev_append cs _ hc1] at h2
  refine capTarget_mono cs (le_of_eq ?_) h2
  simp [m']; omega

/-- **The cap push past a move to the right of the block** (super interchange). -/
theorem push_disjR {c : ℕ} {ms : List (Mv I)} (hIH : PushHyp cs μ w₀ c ms) {m : Mv I}
    (hms : MvChain w₀ ms m.src) {P S Q : List (Letter I)} {l : Letter I} (d : ℕ)
    (R : List (Letter I)) (hQ : Q = R ++ m.ltgt ++ m.post)
    (hu : m.pre = P ++ [flipL l] ++ S ++ [l] ++ R)
    (hc : xcnt (mvLay ms) + xcnt m.lay + S.length ≤ c) :
    xev cs μ w₀ (P ++ S ++ Q) (mvLay ms ++ m.lay ++ (capBlk S l d).map (xwhL P Q)) ∈
      CapTarget D Sc cs μ w₀ (P ++ S ++ Q) (xcnt (mvLay ms) + xcnt m.lay + S.length) := by
  subst hQ
  have hA : XChain ([flipL l] ++ S ++ [l] ++ R) ((capBlk S l d).map (xwhL [] R)) (S ++ R) := by
    simpa using (xChain_capBlk S l d).whisk [] R
  have hsrc : m.src = P ++ (([flipL l] ++ S ++ [l] ++ R) ++ m.lsrc) ++ m.post := by
    rw [Mv.src, hu]; simp
  obtain ⟨p, hp⟩ := xev_ichg cs μ (S := w₀) (T := P ++ S ++ (R ++ m.ltgt ++ m.post)) (mvLay ms)
    [] P m.post hA m.xChain_loc (hsrc ▸ hms.xChain)
  set m' := m.reCtx (P ++ S ++ R) m.post
  have e₁ : mvLay ms ++ m.lay ++ (capBlk S l d).map (xwhL P (R ++ m.ltgt ++ m.post)) =
      mvLay ms ++ m.loc.map (xwhL (P ++ ([flipL l] ++ S ++ [l] ++ R)) m.post) ++
        ((capBlk S l d).map (xwhL [] R)).map (xwhL P (m.ltgt ++ m.post)) ++ [] := by
    rw [Mv.lay, hu, map_xwhL_xwhL]; simp
  have e₂ : mvLay ms ++ ((capBlk S l d).map (xwhL [] R)).map (xwhL P (m.lsrc ++ m.post)) ++
      m.loc.map (xwhL (P ++ (S ++ R)) m.post) ++ [] =
      mvLay ms ++ (capBlk S l d).map (xwhL P (R ++ m.lsrc ++ m.post)) ++ m'.lay := by
    rw [map_xwhL_xwhL]; simp [m', Mv.lay]
  have hp' := congrArg (zsign k p • ·) hp
  simp only [smul_smul, zsign_mul_self', one_smul] at hp'
  rw [e₁]
  refine capTarget_mem_of_smul p hp'.symm ?_
  rw [e₂]
  have hsrc' : m.src = P ++ [flipL l] ++ S ++ [l] ++ (R ++ m.lsrc ++ m.post) := by
    rw [Mv.src, hu]; simp
  have h1 := hIH P S (R ++ m.lsrc ++ m.post) l d (hsrc' ▸ hms) (by simp at hc ⊢; omega)
  have hm' : m'.src = P ++ S ++ (R ++ m.lsrc ++ m.post) := by simp [m', Mv.src]
  have h2 := capTarget_comp_mv cs h1 m' hm'
  have hm't : m'.tgt = P ++ S ++ (R ++ m.ltgt ++ m.post) := by simp [m', Mv.tgt]
  rw [hm't] at h2
  have hc1 : XChain w₀ (mvLay ms ++ (capBlk S l d).map (xwhL P (R ++ m.lsrc ++ m.post)))
      (P ++ S ++ (R ++ m.lsrc ++ m.post)) :=
    (hsrc' ▸ hms.xChain).append (by
      simpa using (xChain_capBlk S l d).whisk P (R ++ m.lsrc ++ m.post))
  rw [← xev_append cs _ hc1] at h2
  refine capTarget_mono cs (le_of_eq ?_) h2
  simp [m']; omega

/-- **The cap push past a dot on the left leg `A` of the cap**: the dot joins the dots of the
block (super interchange with the strand `B` moving across `S`). -/
theorem push_dotA {c : ℕ} {ms : List (Mv I)} (hIH : PushHyp cs μ w₀ c ms)
    {P S Q : List (Letter I)} {l : Letter I} (d : ℕ)
    (hms : MvChain w₀ ms (Mv.dot P (flipL l) (S ++ [l] ++ Q)).src)
    (hc : xcnt (mvLay ms) + xcnt (Mv.dot P (flipL l) (S ++ [l] ++ Q)).lay + S.length ≤ c) :
    xev cs μ w₀ (P ++ S ++ Q) (mvLay ms ++ (Mv.dot P (flipL l) (S ++ [l] ++ Q)).lay ++
        (capBlk S l d).map (xwhL P Q)) ∈
      CapTarget D Sc cs μ w₀ (P ++ S ++ Q)
        (xcnt (mvLay ms) + xcnt (Mv.dot P (flipL l) (S ++ [l] ++ Q)).lay + S.length) := by
  have hsrc : (Mv.dot P (flipL l) (S ++ [l] ++ Q)).src = P ++ ([flipL l] ++ (S ++ [l])) ++ Q := by
    simp [Mv.src, Mv.pre, Mv.lsrc, Mv.post]
  obtain ⟨p, hp⟩ := xev_ichg cs μ (S := w₀) (T := P ++ S ++ Q) (mvLay ms)
    (((xDotsL (flipL l) d).map (xwhL [] (l :: S)) ++ (xCapL l).map (xwhL [] S)).map (xwhL P Q))
    P Q (xChain_xDotL (flipL l)) (xChain_lmLc S l) (hsrc ▸ hms.xChain)
  have e₁ : mvLay ms ++ (Mv.dot P (flipL l) (S ++ [l] ++ Q)).lay ++ (capBlk S l d).map (xwhL P Q) =
      mvLay ms ++ (xDotL (flipL l)).map (xwhL P (S ++ [l] ++ Q)) ++
        (lmLc S l).map (xwhL (P ++ [flipL l]) Q) ++
        (((xDotsL (flipL l) d).map (xwhL [] (l :: S)) ++ (xCapL l).map (xwhL [] S)).map
          (xwhL P Q)) := by
    simp [Mv.lay, Mv.loc, Mv.pre, Mv.post, capBlk]
  have e₂ : mvLay ms ++ (lmLc S l).map (xwhL (P ++ [flipL l]) Q) ++
      (xDotL (flipL l)).map (xwhL P ((l :: S) ++ Q)) ++
        (((xDotsL (flipL l) d).map (xwhL [] (l :: S)) ++ (xCapL l).map (xwhL [] S)).map
          (xwhL P Q)) = mvLay ms ++ (capBlk S l (d + 1)).map (xwhL P Q) := by
    simp [capBlk, xDotsL, List.replicate_succ]
  rw [e₁, hp, e₂]
  refine Submodule.smul_mem _ _ ?_
  have hsrc' : (Mv.dot P (flipL l) (S ++ [l] ++ Q)).src = P ++ [flipL l] ++ S ++ [l] ++ Q := by
    simp [Mv.src, Mv.pre, Mv.lsrc, Mv.post]
  have h := hIH P S Q l (d + 1) (hsrc' ▸ hms) (by simp at hc ⊢; omega)
  refine capTarget_mono cs (le_of_eq ?_) h
  simp [Mv.loc]

end Push

end OddMath.SKM
