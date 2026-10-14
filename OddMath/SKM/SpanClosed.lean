/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanBubbleSlides

/-!
# Cup diagrams over the image of `β`

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1 and (1.21)–(1.22) (`β_λ : SYM → End(1_λ)` is surjective), for diagrams without
crossings. The template is the argument for closed crossingless diagrams in M. Khovanov,
A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.1 (proof of
Proposition 3.6): such a diagram is reduced by removing its caps one at a time.

We organise the argument around the 2-morphisms `1_ν → E_s 1_ν` built from an element of the
image of `β_ν` by dots and cups (`CupSpan cs ν s f`): an element of `bubbleSpan` followed by
moves (`CMove`), each a dot on a strand (the upward dot, or the downward dot (2.2)) or a cup
(the rightward cup `η`, or the leftward cup `η'` (2.10)) placed between strands. On the empty
sequence these are exactly the elements of `bubbleSpan` (`OddMath.SKM.SpanClosedCaps`).

## Main results

* `xev_whisk_eq`: an extended diagram placed between strands is the placement of its
  2-morphism, for all boundaries.
* `xev_swap`: the super interchange law for two blocks of extended layers side by side, up to a
  scalar.
* `CupSpan`, `cupSpan_dots`: closure under dots.
* `cupSpan_plcAt_right`: an element of the image of `β` in the rightmost region moves down to
  the bottom (super interchange law).
* `cupSpan_plcAt`: **an element of the image of `β` placed in any region** of a 2-morphism in
  `CupSpan` keeps it in `CupSpan`; the element is moved to the right across the strands by the
  bubble slides (`bubble_slide_right`, Proposition 7.3), leaving dots behind.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## Boundaries of extended diagrams -/

theorem XChain.target_unique {s t t' : List (Letter I)} {L : List (XLayer I)} (h : XChain s L t)
    (h' : XChain s L t') : t = t' := by
  induction L generalizing s with
  | nil => exact h.symm.trans h'
  | cons x L ih => exact ih h.2 h'.2

theorem XChain.split_append {s t : List (Letter I)} {L M : List (XLayer I)}
    (h : XChain s (L ++ M) t) : ∃ r, XChain s L r ∧ XChain r M t := by
  induction L generalizing s with
  | nil => exact ⟨s, rfl, h⟩
  | cons x L ih =>
    obtain ⟨r, h₁, h₂⟩ := ih h.2
    exact ⟨r, ⟨h.1, h₁⟩, h₂⟩

/-- A nonempty block placed between strands determines its boundary. -/
theorem XChain.whisk_bdry {u v a b s t : List (Letter I)} {A : List (XLayer I)}
    (hA : XChain a A b) (hne : A ≠ []) (h : XChain s (A.map (xwhL u v)) t) :
    s = u ++ a ++ v ∧ t = u ++ b ++ v := by
  obtain ⟨x, A', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hs : s = u ++ a ++ v := by
    rw [h.1, hA.1]; simp [xwhL, List.append_assoc]
  refine ⟨hs, ?_⟩
  subst hs
  exact XChain.target_unique h (hA.whisk u v)

theorem XShape.weight_dom_eq_cod (ν : X) (g : XShape I) : wt D ν g.dom = wt D ν g.cod := by
  cases g with
  | gen g => exact Shape.wt_dom_eq_wt_cod D ν g
  | lcup i => simp [XShape.dom, XShape.cod, sh]
  | lcap i => simp [XShape.dom, XShape.cod, sh]

theorem XChain.weight_eq (ν : X) {s t : List (Letter I)} {L : List (XLayer I)} (h : XChain s L t) :
    wt D ν s = wt D ν t := by
  induction L generalizing s with
  | nil => exact congrArg _ h
  | cons x L ih =>
    obtain ⟨rfl, h⟩ := h
    rw [← ih h, wt_append, wt_append, wt_append, wt_append, XShape.weight_dom_eq_cod]

theorem xev_append_of_not {ν : X} {s t : List (Letter I)} {L M : List (XLayer I)}
    (h : ¬ ∃ r, XChain s L r) : xev cs ν s t (L ++ M) = 0 :=
  xev_of_not cs fun h' => by
    obtain ⟨r, h₁, -⟩ := h'.split_append
    exact h ⟨r, h₁⟩

/-! ## Homogeneity -/

theorem cl_homogeneous (μ : X) (s t : List (Letter I)) (L : List (LayerData I)) :
    ∃ p, cl D Sc μ s t L ∈ homPar D Sc μ s t p := by
  by_cases h : SChain s L t
  · exact ⟨_, cl_mem_homPar h rfl⟩
  · exact ⟨0, by rw [cl_of_not h]; exact Submodule.zero_mem _⟩

theorem xlay_homogeneous (ν : X) (x : XLayer I) :
    ∃ p, xlay cs ν x ∈ homPar D Sc ν (x.1 ++ x.2.1.dom ++ x.2.2) (x.1 ++ x.2.1.cod ++ x.2.2) p := by
  obtain ⟨a, g, b⟩ := x
  cases g with
  | gen g => exact cl_homogeneous ν _ _ [(a, g, b)]
  | lcup i => exact ⟨_, plcL_mem ν a b (etaP_mem cs i (wt D ν b))⟩
  | lcap i => exact ⟨_, plcL_mem ν a b (epsP_mem cs i (wt D ν b))⟩

/-- **Extended diagrams are homogeneous.** -/
theorem xev_homogeneous (ν : X) (s t : List (Letter I)) (L : List (XLayer I)) :
    ∃ p, xev cs ν s t L ∈ homPar D Sc ν s t p := by
  induction L generalizing s with
  | nil => exact cl_homogeneous ν s t []
  | cons x L ih =>
    obtain ⟨p, hp⟩ := ih (x.1 ++ x.2.1.cod ++ x.2.2)
    obtain ⟨q, hq⟩ := xlay_homogeneous cs ν x
    obtain ⟨r, hr⟩ := cl_homogeneous (D := D) (Sc := Sc) ν s (x.1 ++ x.2.1.dom ++ x.2.2) []
    exact ⟨_, comp_mem_homPar hr (comp_mem_homPar hq hp)⟩

/-! ## Placement of extended diagrams, for all boundaries -/

/-- **An extended block placed between strands** is the placement of its 2-morphism, composed
with the identifications of the boundaries (`0` if they do not match). -/
theorem xev_whisk_eq (ν : X) (u v : List (Letter I)) {a b : List (Letter I)} {A : List (XLayer I)}
    (hA : XChain a A b) (hne : A ≠ []) (s t : List (Letter I)) :
    xev cs ν s t (A.map (xwhL u v)) =
      cl D Sc ν s (u ++ a ++ v) [] ≫ plcL D Sc ν u v a b (xev cs (wt D ν v) a b A) ≫
        cl D Sc ν (u ++ b ++ v) t [] := by
  by_cases h : XChain s (A.map (xwhL u v)) t
  · obtain ⟨rfl, rfl⟩ := XChain.whisk_bdry hA hne h
    rw [cl_nil, cl_nil, Category.id_comp, Category.comp_id, plcL_xev]
  · rw [xev_of_not cs h]
    by_cases hs : s = u ++ a ++ v
    · subst hs
      have ht : t ≠ u ++ b ++ v := fun ht => h (ht ▸ hA.whisk u v)
      rw [cl_of_not (show ¬ SChain (u ++ b ++ v) [] t from fun e => ht e.symm),
        Limits.comp_zero, Limits.comp_zero]
    · rw [cl_of_not (show ¬ SChain s [] (u ++ a ++ v) from hs), Limits.zero_comp]

theorem wordCast_xev (ν : X) {s t s' t' : List (Letter I)} (hs : s = s') (ht : t = t')
    (L : List (XLayer I)) : wordCast ν hs ht (xev cs ν s t L) = xev cs ν s' t' L := by
  subst hs ht; rfl

theorem plcRight_xev (ν : X) (u : List (Letter I)) {t t' : List (Letter I)} (B : List (XLayer I)) :
    plcRight ν u t t' (xev cs ν t t' B) = xev cs ν (u ++ t) (u ++ t') (B.map (xwhL u [])) := by
  dsimp only [plcRight, LinearMap.comp_apply]
  have h := plcL_xev cs ν u [] (s := t) (t := t') B
  erw [h]
  exact wordCast_xev cs ν _ _ _

/-! ## The super interchange law -/

/-- Super interchange of two blocks side by side, at the matching boundary. -/
theorem xev_swap_core (ν : X) {a a' b b' : List (Letter I)} {A B : List (XLayer I)}
    (hA : XChain a A a') (hB : XChain b B b') :
    ∃ p : ZMod 2, xev cs ν (a ++ b) (a' ++ b') (A.map (xwhL [] b) ++ B.map (xwhL a' [])) =
      zsign k p • xev cs ν (a ++ b) (a' ++ b') (B.map (xwhL a []) ++ A.map (xwhL [] b')) := by
  obtain ⟨p, hp⟩ := xev_homogeneous cs (wt D ν b) a a' A
  obtain ⟨q, hq⟩ := xev_homogeneous cs ν b b' B
  have hw : wt D ν b = wt D ν b' := hB.weight_eq ν
  have E := plcL_interchange_hom (D := D) (Sc := Sc) ν hw hp hq
  have e₁ := plcL_xev cs ν [] b (s := a) (t := a') A
  have e₂ := plcL_xev cs ν [] b' (s := a) (t := a') A
  rw [regionCast_family (f := fun ν => xev cs ν a a' A), e₁, e₂, plcRight_xev,
    plcRight_xev] at E
  refine ⟨p * q, ?_⟩
  have hA' : XChain (a ++ b) (A.map (xwhL [] b)) (a' ++ b) := by simpa using hA.whisk [] b
  have hB' : XChain (a ++ b) (B.map (xwhL a [])) (a ++ b') := by simpa using hB.whisk a []
  rw [xev_append cs _ hA', xev_append cs _ hB']
  exact E

theorem map_xwhL_comp (u v u' v' : List (Letter I)) (L : List (XLayer I)) :
    (L.map (xwhL u v)).map (xwhL u' v') = L.map (xwhL (u' ++ u) (v ++ v')) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro x _
  obtain ⟨a, g, b⟩ := x
  simp [xwhL, List.append_assoc]

@[simp] theorem map_xwhL_nil (L : List (XLayer I)) : L.map (xwhL [] []) = L := by
  induction L with
  | nil => rfl
  | cons x L ih => obtain ⟨a, g, b⟩ := x; simp [xwhL, ih]

/-- **Super interchange of two blocks side by side**, between any boundaries, up to a scalar:
the block `A` (left) and the block `B` (right), with the strands `P`, `Q`, `R` around them. -/
theorem xev_swap (ν : X) {a a' b b' : List (Letter I)} {A B : List (XLayer I)}
    (hA : XChain a A a') (hB : XChain b B b') (P Q R s t : List (Letter I)) :
    ∃ p : ZMod 2,
      xev cs ν s t (A.map (xwhL P (Q ++ b ++ R)) ++ B.map (xwhL (P ++ a' ++ Q) R)) =
        zsign k p • xev cs ν s t (B.map (xwhL (P ++ a ++ Q) R) ++ A.map (xwhL P (Q ++ b' ++ R))) := by
  rcases eq_or_ne A [] with rfl | hAne
  · obtain rfl : a = a' := hA
    exact ⟨0, by simp [zsign_zero]⟩
  rcases eq_or_ne B [] with rfl | hBne
  · obtain rfl : b = b' := hB
    exact ⟨0, by simp [zsign_zero]⟩
  have hAQ : XChain (a ++ Q) (A.map (xwhL [] Q)) (a' ++ Q) := by simpa using hA.whisk [] Q
  obtain ⟨c, hc⟩ := xev_swap_core cs (wt D ν R) hAQ hB
  refine ⟨c, ?_⟩
  have e₁ : A.map (xwhL P (Q ++ b ++ R)) ++ B.map (xwhL (P ++ a' ++ Q) R) =
      ((A.map (xwhL [] Q)).map (xwhL [] b) ++ B.map (xwhL (a' ++ Q) [])).map (xwhL P R) := by
    simp only [List.map_append, map_xwhL_comp, List.append_nil, List.nil_append,
      List.append_assoc]
  have e₂ : B.map (xwhL (P ++ a ++ Q) R) ++ A.map (xwhL P (Q ++ b' ++ R)) =
      (B.map (xwhL (a ++ Q) []) ++ (A.map (xwhL [] Q)).map (xwhL [] b')).map (xwhL P R) := by
    simp only [List.map_append, map_xwhL_comp, List.append_nil, List.nil_append,
      List.append_assoc]
  have hne₁ : (A.map (xwhL [] Q)).map (xwhL [] b) ++ B.map (xwhL (a' ++ Q) []) ≠ [] := by
    simp [hAne]
  have hne₂ : B.map (xwhL (a ++ Q) []) ++ (A.map (xwhL [] Q)).map (xwhL [] b') ≠ [] := by
    simp [hBne]
  have hc₁ : XChain (a ++ Q ++ b) ((A.map (xwhL [] Q)).map (xwhL [] b) ++
      B.map (xwhL (a' ++ Q) [])) (a' ++ Q ++ b') :=
    (by simpa using hAQ.whisk [] b : XChain _ _ (a' ++ Q ++ b)).append
      (by simpa using hB.whisk (a' ++ Q) [])
  have hc₂ : XChain (a ++ Q ++ b) (B.map (xwhL (a ++ Q) []) ++
      (A.map (xwhL [] Q)).map (xwhL [] b')) (a' ++ Q ++ b') :=
    (by simpa using hB.whisk (a ++ Q) [] : XChain _ _ (a ++ Q ++ b')).append
      (by simpa using hAQ.whisk [] b')
  rw [e₁, e₂, xev_whisk_eq cs ν P R hc₁ hne₁, xev_whisk_eq cs ν P R hc₂ hne₂, hc, map_smul,
    Linear.smul_comp, Linear.comp_smul]

@[simp] theorem xwhL_mk (u v a b : List (Letter I)) (g : XShape I) :
    xwhL u v (a, g, b) = (u ++ a, g, b ++ v) := rfl

/-- The super interchange law, read in the other direction. -/
theorem xev_swap' (ν : X) {a a' b b' : List (Letter I)} {A B : List (XLayer I)}
    (hA : XChain a A a') (hB : XChain b B b') (P Q R s t : List (Letter I)) :
    ∃ p : ZMod 2,
      xev cs ν s t (B.map (xwhL (P ++ a ++ Q) R) ++ A.map (xwhL P (Q ++ b' ++ R))) =
        zsign k p • xev cs ν s t (A.map (xwhL P (Q ++ b ++ R)) ++ B.map (xwhL (P ++ a' ++ Q) R)) := by
  obtain ⟨p, hp⟩ := xev_swap cs ν hA hB P Q R s t
  refine ⟨p, ?_⟩
  rw [hp, smul_smul, zsign_mul_self, one_smul]

/-! ## Moves: dots and cups -/

/-- A dot on the strand `l`, or a cup `1 → l l*`. -/
inductive CMove (I : Type u)
  /-- A dot on `l`: the upward dot, or the downward dot (2.2). -/
  | dot (l : Letter I)
  /-- The cup `1 → l l*`: the leftward cup `η'` for `l = up i`, the rightward cup `η` for
  `l = dn i`. -/
  | cup (l : Letter I)

namespace CMove

/-- Bottom boundary. -/
def dom : CMove I → List (Letter I)
  | dot l => [l]
  | cup _ => []

/-- Top boundary. -/
def cod : CMove I → List (Letter I)
  | dot l => [l]
  | cup l => [l, flipL l]

/-- The extended layers of a move. -/
def loc : CMove I → List (XLayer I)
  | dot (true, i) => [([], .gen (.dot i), [])]
  | dot (false, i) => (ddotL i).map ofL
  | cup (true, i) => [([], .lcup i, [])]
  | cup (false, i) => [([], .gen (.cup i), [])]

@[simp] theorem dom_dot (l : Letter I) : (dot l).dom = [l] := rfl
@[simp] theorem cod_dot (l : Letter I) : (dot l).cod = [l] := rfl
@[simp] theorem dom_cup (l : Letter I) : (cup l).dom = [] := rfl
@[simp] theorem cod_cup (l : Letter I) : (cup l).cod = [l, flipL l] := rfl
@[simp] theorem loc_dot_up (i : I) : (dot (up i)).loc = [([], .gen (.dot i), [])] := rfl
@[simp] theorem loc_dot_dn (i : I) : (dot (dn i)).loc = (ddotL i).map ofL := rfl
@[simp] theorem loc_cup_up (i : I) : (cup (up i)).loc = [([], .lcup i, [])] := rfl
@[simp] theorem loc_cup_dn (i : I) : (cup (dn i)).loc = [([], .gen (.cup i), [])] := rfl

theorem xChain_loc : ∀ m : CMove I, XChain m.dom m.loc m.cod
  | dot (true, _) => ⟨rfl, rfl⟩
  | dot (false, i) => XChain.of_sChain (sChain_ddotL i)
  | cup (true, _) => ⟨rfl, rfl⟩
  | cup (false, _) => ⟨rfl, rfl⟩

theorem loc_ne_nil : ∀ m : CMove I, m.loc ≠ []
  | dot (true, _) => by simp [loc]
  | dot (false, i) => by simp [loc, ddotL, mateL]
  | cup (true, _) => by simp [loc]
  | cup (false, _) => by simp [loc]

end CMove

/-- `a` dots on the strand `l`. -/
def xDots (l : Letter I) (a : ℕ) : List (XLayer I) := (List.replicate a (CMove.dot l).loc).flatten

theorem xDots_eq (l : Letter I) (a : ℕ) : xDots l a = (dotsLay l a).map ofL := by
  obtain ⟨_ | _, i⟩ := l
  · simp [xDots, CMove.loc, ddotsL, List.map_flatten, List.map_replicate]
  · induction a with
    | zero => rfl
    | succ a ih =>
      rw [xDots, List.replicate_succ, List.flatten_cons, ← xDots, ih]
      simp [CMove.loc, dotsL, List.replicate_succ, ofL]

theorem xChain_xDots (l : Letter I) (a : ℕ) : XChain [l] (xDots l a) [l] := by
  rw [xDots_eq]; exact XChain.of_sChain (sChain_dotsLay l a)

theorem xev_xDots (μ : X) (l : Letter I) (a : ℕ) :
    xev cs μ [l] [l] (xDots l a) = cl D Sc μ [l] [l] (dotsLay l a) := by
  rw [xDots_eq, xev_map_ofL]

theorem xDots_succ (l : Letter I) (a : ℕ) : xDots l (a + 1) = (CMove.dot l).loc ++ xDots l a := by
  rw [xDots, List.replicate_succ, List.flatten_cons, ← xDots]

theorem xDots_succ' (l : Letter I) (a : ℕ) : xDots l (a + 1) = xDots l a ++ (CMove.dot l).loc := by
  rw [xDots, List.replicate_succ', List.flatten_append, List.flatten_singleton, ← xDots]

theorem xDots_add (l : Letter I) (a b : ℕ) : xDots l (a + b) = xDots l a ++ xDots l b := by
  rw [xDots, List.replicate_add, List.flatten_append, ← xDots, ← xDots]

/-! ## Cup diagrams over the image of `β` -/

variable (ν : X)

/-- `CupSpan cs ν s f`: the 2-morphism `f : 1_ν → E_s 1_ν` lies in the span of the diagrams
consisting of an element of the image of `β_ν` (at the bottom) followed by dots and cups placed
between strands. -/
inductive CupSpan : (s : List (Letter I)) →
    ((pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)) → Prop
  /-- An element of the image of `β_ν`. -/
  | bub {β} : IsBub cs ν β → CupSpan [] β
  /-- A dot or a cup placed between the strands `u` and `v`. -/
  | move {s t f} (m : CMove I) (u v : List (Letter I)) : CupSpan s f →
      CupSpan t (f ≫ xev cs ν s t (m.loc.map (xwhL u v)))
  | zero {s} : CupSpan s 0
  | add {s f g} : CupSpan s f → CupSpan s g → CupSpan s (f + g)
  | smul {s f} (r : k) : CupSpan s f → CupSpan s (r • f)

variable {cs}

theorem CupSpan.sum {s : List (Letter I)} {ι : Type*} (S : Finset ι)
    {F : ι → ((pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s))}
    (h : ∀ a ∈ S, CupSpan cs ν s (F a)) : CupSpan cs ν s (∑ a ∈ S, F a) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact .zero
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact .add (h a (Finset.mem_insert_self a S)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem CupSpan.of_eq {s : List (Letter I)}
    {f g : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)} (hf : CupSpan cs ν s f)
    (h : f = g) : CupSpan cs ν s g := h ▸ hf

/-- Composition with a block `L ++ M`, one part at a time. -/
theorem CupSpan.comp_append {s t : List (Letter I)}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)} {L M : List (XLayer I)}
    (hL : ∀ r, CupSpan cs ν r (f ≫ xev cs ν s r L))
    (hM : ∀ r t (g : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν r)),
      CupSpan cs ν r g → CupSpan cs ν t (g ≫ xev cs ν r t M)) :
    CupSpan cs ν t (f ≫ xev cs ν s t (L ++ M)) := by
  by_cases h : ∃ r, XChain s L r
  · obtain ⟨r, hr⟩ := h
    rw [xev_append cs _ hr, ← Category.assoc]
    exact hM _ _ _ (hL r)
  · rw [xev_append_of_not cs h, Limits.comp_zero]; exact .zero

/-- **Dots**: `a` dots on a strand. -/
theorem cupSpan_dots (l : Letter I) (u v : List (Letter I)) :
    ∀ (a : ℕ) {s t : List (Letter I)}
      {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)}, CupSpan cs ν s f →
      CupSpan cs ν t (f ≫ xev cs ν s t ((xDots l a).map (xwhL u v)))
  | 0, s, t, f, hf => by
    by_cases h : s = t
    · subst h; simp [xDots, xev_nil, cl_nil, hf]
    · rw [show (xDots l 0).map (xwhL u v) = [] from rfl, xev_nil,
        cl_of_not (show ¬ SChain s [] t from h), Limits.comp_zero]
      exact .zero
  | a + 1, s, t, f, hf => by
    rw [xDots_succ', List.map_append]
    exact CupSpan.comp_append ν (fun r => cupSpan_dots l u v a hf)
      (fun r t g hg => .move (.dot l) u v hg)

/-! ## Elements of the image of `β` placed in a region -/

/-- A 2-morphism `E_a → E_b` (at `ν + wt v`) placed between the strands `u` and `v`, from
`E_s` to `E_t` (`0` unless `s = u a v` and `t = u b v`). -/
def plcW (s t u v a b : List (Letter I)) :
    ((pres D Sc).obj (ob D (wt D ν v) a) ⟶ (pres D Sc).obj (ob D (wt D ν v) b)) →ₗ[k]
      ((pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)) where
  toFun g := cl D Sc ν s (u ++ a ++ v) [] ≫ plcL D Sc ν u v a b g ≫ cl D Sc ν (u ++ b ++ v) t []
  map_add' g₁ g₂ := by rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r g := by rw [map_smul, Linear.smul_comp, Linear.comp_smul]; rfl

theorem plcW_apply (s t u v a b : List (Letter I))
    (g : (pres D Sc).obj (ob D (wt D ν v) a) ⟶ (pres D Sc).obj (ob D (wt D ν v) b)) :
    plcW ν s t u v a b g =
      cl D Sc ν s (u ++ a ++ v) [] ≫ plcL D Sc ν u v a b g ≫ cl D Sc ν (u ++ b ++ v) t [] := rfl

/-- An element of `End(1_{ν + wt v})` placed between the strands `u` and `v`. -/
abbrev plcAt (s t u v : List (Letter I)) := plcW (D := D) (Sc := Sc) ν s t u v [] []

/-- Linear maps on 2-morphisms agree if they agree on normal-form diagrams. -/
theorem hom_ext_cl {μ : X} {s t : List (Letter I)} {M : Type*} [AddCommGroup M] [Module k M]
    (F G : ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) →ₗ[k] M)
    (h : ∀ L, F (cl D Sc μ s t L) = G (cl D Sc μ s t L)) : F = G := by
  ext f
  induction mem_span_cl μ f using Submodule.span_induction with
  | mem g hg => obtain ⟨L, -, rfl⟩ := hg; exact h L
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul r x _ hx => rw [map_smul, map_smul, hx]

theorem cl_sandwich_congr {s t X₁ Y₁ X₂ Y₂ : List (Letter I)} {L₁ L₂ : List (LayerData I)}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (hL : L₁ = L₂) :
    cl D Sc ν s X₁ [] ≫ cl D Sc ν X₁ Y₁ L₁ ≫ cl D Sc ν Y₁ t [] =
      cl D Sc ν s X₂ [] ≫ cl D Sc ν X₂ Y₂ L₂ ≫ cl D Sc ν Y₂ t [] := by
  subst hX hY hL; rfl

/-- A block of extended layers placed between strands, as `plcW`. -/
theorem xev_eq_plcW (u v : List (Letter I)) {a b : List (Letter I)} {A : List (XLayer I)}
    (hA : XChain a A b) (hne : A ≠ []) (s t : List (Letter I)) :
    xev cs ν s t (A.map (xwhL u v)) = plcW ν s t u v a b (xev cs (wt D ν v) a b A) :=
  xev_whisk_eq cs ν u v hA hne s t

theorem plcW_comp (s t u v a b c : List (Letter I))
    (g₁ : (pres D Sc).obj (ob D (wt D ν v) a) ⟶ (pres D Sc).obj (ob D (wt D ν v) b))
    (g₂ : (pres D Sc).obj (ob D (wt D ν v) b) ⟶ (pres D Sc).obj (ob D (wt D ν v) c)) :
    plcW ν s t u v a c (g₁ ≫ g₂) = plcW ν s (u ++ b ++ v) u v a b g₁ ≫
      plcW ν (u ++ b ++ v) t u v b c g₂ := by
  simp only [plcW_apply, plcL_comp, cl_nil, Category.id_comp, Category.comp_id, Category.assoc]

/-- An element of the image of `β` placed in the region left of the strand `l` is the
placement of `β` to the left of `l`. -/
theorem plcAt_cons (s t u v : List (Letter I)) (l : Letter I)
    (β : (pres D Sc).obj (ob D (wt D ν (l :: v)) []) ⟶ (pres D Sc).obj (ob D (wt D ν (l :: v)) [])) :
    plcAt ν s t u (l :: v) β =
      plcW ν s t u v [l] [l] (plcL D Sc (wt D ν v) [] [l] [] [] β) := by
  have key : plcAt (D := D) (Sc := Sc) ν s t u (l :: v) =
      (plcW ν s t u v [l] [l]).comp (plcL D Sc (wt D ν v) [] [l] [] []) := by
    refine hom_ext_cl _ _ fun L => ?_
    rw [LinearMap.comp_apply, plcW_apply, plcW_apply]
    erw [plcL_cl, plcL_cl, plcL_cl]
    exact cl_sandwich_congr ν (by simp) (by simp) (by simp [List.map_map, whL, Function.comp_def])
  exact LinearMap.congr_fun key β

/-- An element of the image of `β` placed to the right of the strand `l`. -/
theorem plcW_rbub (s t u v : List (Letter I)) (l : Letter I)
    (γ : (pres D Sc).obj (ob D (wt D ν v) []) ⟶ (pres D Sc).obj (ob D (wt D ν v) [])) :
    plcW ν s t u v [l] [l] (plcL D Sc (wt D ν v) [l] [] [] [] γ) =
      plcAt ν s t (u ++ [l]) v γ := by
  have key : (plcW (D := D) (Sc := Sc) ν s t u v [l] [l]).comp
      (plcL D Sc (wt D ν v) [l] [] [] []) = plcAt ν s t (u ++ [l]) v := by
    refine hom_ext_cl (μ := wt D ν v) _ _ fun L => ?_
    rw [LinearMap.comp_apply]
    erw [plcW_apply, plcW_apply, plcL_cl, plcL_cl, plcL_cl]
    exact cl_sandwich_congr ν (by simp) (by simp) (by simp [List.map_map, whL, Function.comp_def])
  exact LinearMap.congr_fun key γ

theorem plcAt_nil_cl (s : List (Letter I)) (N : List (LayerData I)) :
    plcAt ν s s s [] (cl D Sc ν [] [] N) = cl D Sc ν s s (N.map (whL s [])) := by
  rw [plcW_apply]
  erw [plcL_cl]
  exact cl_cast _ (by simp) (by simp)

/-- **Elements of the image of `β` in the rightmost region supercommute with diagrams.** -/
theorem xev_comp_plcAt_right {s s₁ : List (Letter I)} {M : List (XLayer I)} (hM : XChain s M s₁)
    {q : ZMod 2} {γ : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν [])}
    (hγ : γ ∈ closedPar D Sc ν q) (t : List (Letter I)) :
    ∃ c : k, xev cs ν s s₁ M ≫ plcAt ν s₁ t s₁ [] γ = c • (plcAt ν s s s [] γ ≫ xev cs ν s t M) := by
  by_cases ht : t = s₁
  · subst ht
    obtain ⟨p, hp⟩ := xev_homogeneous cs ν s t M
    refine ⟨zsign k (p * q), ?_⟩
    rw [closedPar_eq] at hγ
    refine homPar_induction₂ (μ := ν) (μ' := ν) (P := fun f g =>
      f ≫ plcAt ν t t t [] g = zsign k (p * q) • (plcAt ν s s s [] g ≫ f))
      (fun L N hL hpL hN hpN => ?_) (fun g => by simp) (fun f => by simp)
      (fun f₁ f₂ g h₁ h₂ => by rw [Preadditive.add_comp, h₁, h₂, Preadditive.comp_add, smul_add])
      (fun f g₁ g₂ h₁ h₂ => by
        rw [map_add, Preadditive.comp_add, h₁, h₂, map_add, Preadditive.add_comp, smul_add])
      (fun r f g h => by rw [Linear.smul_comp, h, Linear.comp_smul, smul_comm])
      (fun r f g h => by
        rw [map_smul, Linear.comp_smul, h, map_smul, Linear.smul_comp, smul_comm])
      hp hγ
    rw [plcAt_nil_cl, plcAt_nil_cl, cl_comp hL (by simpa using hN.whisk t []),
      cl_comp (by simpa using hN.whisk s []) hL]
    have E := cl_interchange (D := D) (Sc := Sc) (μ := ν) (S := s) (T := t) [] [] hL hN
    simp only [List.nil_append, List.append_nil, map_whL_nil_nil] at E
    rw [E, hpL, hpN]
  · refine ⟨1, ?_⟩
    have h1 : xev cs ν s t M = 0 := xev_of_not cs fun h => ht (XChain.target_unique h hM)
    rw [h1, plcW_apply, cl_of_not (show ¬ SChain (s₁ ++ [] ++ []) [] t from by simpa using Ne.symm ht)]
    simp

theorem plcL_closed_nil (μ : X)
    (γ : (pres D Sc).obj (ob D (wt D μ []) []) ⟶ (pres D Sc).obj (ob D (wt D μ []) [])) :
    plcL D Sc μ [] [] [] [] γ = γ := by
  induction mem_span_cl (D := D) (Sc := Sc) (wt D μ []) γ using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, -, rfl⟩ := hf
    exact plcL_nil_cl μ [] [] L
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul r x _ hx => rw [map_smul, hx]

/-- **An element of the image of `β` in the rightmost region** keeps a 2-morphism in
`CupSpan`. -/
theorem cupSpan_plcAt_right {s : List (Letter I)}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)} (hf : CupSpan cs ν s f) :
    ∀ (t : List (Letter I)) {γ : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν [])}
      (_ : IsBub cs ν γ) (q : ZMod 2) (_ : γ ∈ closedPar D Sc ν q),
      CupSpan cs ν t (f ≫ plcAt ν s t s [] γ) := by
  induction hf with
  | @bub β hβ =>
    intro t γ hγ q _
    by_cases ht : t = []
    · subst ht
      have e : plcAt ν [] [] [] [] γ = γ := by
        show cl D Sc ν [] [] [] ≫ plcL D Sc ν [] [] [] [] γ ≫ cl D Sc ν [] [] [] = γ
        rw [cl_nil]
        erw [Category.id_comp, Category.comp_id]
        exact plcL_closed_nil ν γ
      rw [e]; exact .bub (hβ.comp hγ)
    · rw [plcW_apply, cl_of_not (show ¬ SChain ([] ++ [] ++ []) [] t from fun h => ht h.symm)]
      simp only [Limits.comp_zero]; exact .zero
  | @move s s₁ f m u v _ ih =>
    intro t γ hγ q hq
    by_cases hM : XChain s (m.loc.map (xwhL u v)) s₁
    · obtain ⟨c, hc⟩ := xev_comp_plcAt_right (cs := cs) ν hM hq t
      rw [Category.assoc, hc, Linear.comp_smul, ← Category.assoc]
      exact .smul c (.move m u v (ih s hγ q hq))
    · rw [xev_of_not cs hM, Limits.comp_zero, Limits.zero_comp]; exact .zero
  | zero => intro t γ _ _ _; rw [Limits.zero_comp]; exact .zero
  | add _ _ ih₁ ih₂ =>
    intro t γ hγ q hq; rw [Preadditive.add_comp]; exact .add (ih₁ t hγ q hq) (ih₂ t hγ q hq)
  | smul r _ ih => intro t γ hγ q hq; rw [Linear.smul_comp]; exact .smul r (ih t hγ q hq)

/-- The image of `β_ν` is spanned by its homogeneous elements. -/
theorem isBub_mem_span_homogeneous {μ : X}
    {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])} (hβ : IsBub cs μ β) :
    β ∈ Submodule.span k {γ | IsBub cs μ γ ∧ ∃ q, γ ∈ closedPar D Sc μ q} := by
  have h : (β : End _) ∈ Subalgebra.toSubmodule (bubbleSpan cs μ) := hβ
  rw [bubbleSpan, Algebra.adjoin_eq_span] at h
  refine Submodule.span_le.2 ?_ h
  intro x hx
  refine Submodule.subset_span ?_
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, n, rfl⟩ := hx
    exact ⟨isBub_bubLs cs i μ n, bubLs_mem_closedPar cs i μ n⟩
  | one => exact ⟨IsBub.id, 0, id_mem_closedPar μ⟩
  | mul x y _ _ hx hy =>
    obtain ⟨hx, p, hp⟩ := hx
    obtain ⟨hy, q, hq⟩ := hy
    exact ⟨hy.comp hx, _, comp_mem_closedPar hq hp⟩

/-- Linearity of the placed element. -/
theorem cupSpan_plcW_of_span {s t u v a b : List (Letter I)}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)}
    {S : Set ((pres D Sc).obj (ob D (wt D ν v) a) ⟶ (pres D Sc).obj (ob D (wt D ν v) b))}
    (hS : ∀ g ∈ S, CupSpan cs ν t (f ≫ plcW ν s t u v a b g)) {g}
    (hg : g ∈ Submodule.span k S) : CupSpan cs ν t (f ≫ plcW ν s t u v a b g) := by
  induction hg using Submodule.span_induction with
  | mem g hg => exact hS g hg
  | zero => rw [map_zero, Limits.comp_zero]; exact .zero
  | add x y _ _ hx hy => rw [map_add, Preadditive.comp_add]; exact .add hx hy
  | smul r x _ hx => rw [map_smul, Linear.comp_smul]; exact .smul r hx

theorem xDots_ne_nil (l : Letter I) {a : ℕ} (ha : 0 < a) : xDots l a ≠ [] := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt ha
  rw [zero_add, xDots_succ]
  simp [CMove.loc_ne_nil]

/-- Dots placed between strands, as `plcW`. -/
theorem plcW_dots (u v : List (Letter I)) (l : Letter I) (a : ℕ) (t : List (Letter I)) :
    plcW ν (u ++ [l] ++ v) t u v [l] [l] (cl D Sc (wt D ν v) [l] [l] (dotsLay l a)) =
      xev cs ν (u ++ [l] ++ v) t ((xDots l a).map (xwhL u v)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [dotsLay_zero, cl_nil, plcW_apply, plcL_id, cl_nil, Category.id_comp, Category.id_comp]
    rfl
  · rw [xev_eq_plcW ν u v (xChain_xDots l a) (xDots_ne_nil l ha), xev_xDots]

/-- **Elements of the image of `β` slide out of every region.** An element of the image of
`β_{ν + wt v}` placed between `u` and `v` keeps a 2-morphism in `CupSpan`: it moves to the right
across the strands of `v` (`bubble_slide_right`), leaving dots, then down to the bottom
(`cupSpan_plcAt_right`). -/
theorem cupSpan_plcAt : ∀ (v u : List (Letter I)) {s t : List (Letter I)}
    {f : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν s)}, CupSpan cs ν s f →
    ∀ {β : (pres D Sc).obj (ob D (wt D ν v) []) ⟶ (pres D Sc).obj (ob D (wt D ν v) [])},
      IsBub cs (wt D ν v) β → CupSpan cs ν t (f ≫ plcAt ν s t u v β)
  | [], u, s, t, f, hf, β, hβ => by
    refine cupSpan_plcW_of_span ν (fun γ hγ => ?_) (isBub_mem_span_homogeneous hβ)
    obtain ⟨hγ, q, hq⟩ := hγ
    by_cases hs : s = u
    · subst hs
      have := cupSpan_plcAt_right ν hf t hγ q hq
      exact this
    · rw [plcW_apply, cl_of_not (show ¬ SChain s [] (u ++ [] ++ []) from by simpa using hs)]
      simp only [Limits.zero_comp, Limits.comp_zero]; exact .zero
  | l :: v, u, s, t, f, hf, β, hβ => by
    rw [plcAt_cons]
    have hmem := bubble_slide_right cs (wt D ν v) l hβ
    refine cupSpan_plcW_of_span ν (fun g hg => ?_) hmem
    obtain ⟨a, γ, hγ, ⟨q, hq⟩, rfl⟩ := hg
    rw [plcW_comp, plcW_rbub, ← Category.assoc]
    refine cupSpan_plcAt v (u ++ [l]) ?_ hγ
    by_cases hs : s = u ++ [l] ++ v
    · subst hs
      rw [plcW_dots]
      exact cupSpan_dots ν l u v a hf
    · rw [plcW_apply, cl_of_not (show ¬ SChain s [] (u ++ [l] ++ v) from hs)]
      simp only [Limits.zero_comp, Limits.comp_zero]; exact .zero

end OddMath.SKM
