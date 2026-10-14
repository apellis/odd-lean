/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanBubbles

/-!
# Move diagrams and the cap block

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11 (reduction of diagrams modulo diagrams
with fewer crossings). The template is the elimination of caps in the proof of KL III
Proposition 3.11: every diagram is, modulo diagrams with fewer crossings and diagrams factoring
through shorter sequences, a combination of diagrams without caps followed by bubbles.

## Letters of both orientations

A letter `l` is `up i` (the 1-morphism `Eᵢ`) or `dn i` (`Fᵢ`); `flipL l` is the letter of the
other orientation. In the extended diagram language of `OddMath.SKM.SpanLower` (with `η'` and
`ε'` as crossingless layers) we use, for letters of either orientation:

* `xDotL l`: a dot on `l` (the downward dot is the mate (2.3) of the upward dot);
* `xCrL l₁ l₂ : l₁ l₂ → l₂ l₁`: the crossing of two strands: the upward crossing `τ`, the leftward
  crossing (2.6), the rightward crossing `σ` (1.11) or the downward crossing (2.1); each has one
  crossing;
* `xCupL l : 1 → l l*`: the rightward cup `η` (`l = dn i`) or the leftward cup `η'` (`l = up i`);
* `xCapL l : l* l → 1`: the rightward cap `ε` (`l = dn i`) or the leftward cap `ε'` (`l = up i`).

## Moves and move diagrams

A move (`Mv`) is a dot, a crossing of two adjacent strands or a cup, placed between strands; a
move diagram is a composite of moves (a diagram without caps). `MvSp μ w₀ v c` is the span of the
move diagrams `E_{w₀} 1_μ → E_v 1_μ` with at most `c` crossings followed by a product of bubbles
in the rightmost region (`bubAt`); `thruShort μ w₀ v` is the span of the 2-morphisms factoring
through a sequence shorter than `w₀`, and `CapTarget = MvSp ⊔ thruShort` is the target of the
elimination of caps. Move diagrams compose (`mvSp_comp`): products of bubbles in the rightmost
region supercommute with all diagrams (`comp_bubAt`).

## The cap block

`capBlk S l d : l* S l → S`: the strand `B = l` moves left across the strands `S` (`lmLc`), `d`
dots on `A = l*`, and the cap joining `A` and `B`. The elimination of caps pushes this block down
through a move diagram.

## Main results

* `xev_exists_mem`: extended diagrams are homogeneous.
* `xev_interchange`, `xev_ichg`: the super interchange law for two blocks of extended layers side
  by side, up to sign.
* `Mv`, `MvChain`, `mvLay`, `MvSp`, `thruShort`, `CapTarget` and their closure properties.
* `lmLc`, `lmRc`, `capBlk`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## Extended layers: chains and weights -/

theorem XChain.split {s t : List (Letter I)} {L M : List (XLayer I)} (h : XChain s (L ++ M) t) :
    ∃ r, XChain s L r ∧ XChain r M t := by
  induction L generalizing s with
  | nil => exact ⟨s, rfl, h⟩
  | cons x L ih =>
    obtain ⟨r, h₁, h₂⟩ := ih h.2
    exact ⟨r, ⟨h.1, h₁⟩, h₂⟩

theorem XChain.eq_target {s t t' : List (Letter I)} {L : List (XLayer I)} (h : XChain s L t)
    (h' : XChain s L t') : t = t' := by
  induction L generalizing s with
  | nil => exact h.symm.trans h'
  | cons x L ih => exact ih h.2 h'.2

theorem XShape.wt_dom_eq_wt_cod (ν : X) (g : XShape I) : wt D ν g.dom = wt D ν g.cod := by
  cases g with
  | gen g => exact Shape.wt_dom_eq_wt_cod D ν g
  | lcup i => simp [XShape.dom, XShape.cod, sh]
  | lcap i => simp [XShape.dom, XShape.cod, sh]

theorem XChain.wt_eq (ν : X) {s t : List (Letter I)} {L : List (XLayer I)} (h : XChain s L t) :
    wt D ν s = wt D ν t := by
  induction L generalizing s with
  | nil => exact congrArg _ h
  | cons x L ih =>
    obtain ⟨rfl, h⟩ := h
    rw [← ih h, wt_append, wt_append, wt_append, wt_append, XShape.wt_dom_eq_wt_cod]

@[simp] theorem xwhL_comp_xwhL (u v u' v' : List (Letter I)) :
    xwhL u' v' ∘ xwhL u v = xwhL (I := I) (u' ++ u) (v ++ v') := by
  funext x; obtain ⟨a, g, b⟩ := x; simp [xwhL, List.append_assoc]

theorem map_xwhL_xwhL (u v u' v' : List (Letter I)) (L : List (XLayer I)) :
    (L.map (xwhL u v)).map (xwhL u' v') = L.map (xwhL (u' ++ u) (v ++ v')) := by
  rw [List.map_map, xwhL_comp_xwhL]

@[simp] theorem map_xwhL_nil_nil (L : List (XLayer I)) : L.map (xwhL [] []) = L := by
  induction L with
  | nil => rfl
  | cons x L ih => obtain ⟨a, g, b⟩ := x; simp [xwhL, ih]

theorem xcnt_replicate_flatten (L : List (XLayer I)) (d : ℕ) :
    xcnt (List.replicate d L).flatten = d * xcnt L := by
  induction d with
  | zero => simp
  | succ d ih => rw [List.replicate_succ, List.flatten_cons, xcnt_append, ih]; ring

/-! ## Homogeneity of extended diagrams -/

theorem xlay_exists_mem (ν : X) (x : XLayer I) :
    ∃ p, xlay cs ν x ∈ homPar D Sc ν (x.1 ++ x.2.1.dom ++ x.2.2) (x.1 ++ x.2.1.cod ++ x.2.2) p := by
  obtain ⟨a, g, b⟩ := x
  cases g with
  | gen g => exact ⟨_, cl_mem_homPar' ν _ _ [(a, g, b)]⟩
  | lcup i => exact ⟨_, plcL_mem ν a b (etaP_mem cs i (wt D ν b))⟩
  | lcap i => exact ⟨_, plcL_mem ν a b (epsP_mem cs i (wt D ν b))⟩

/-- **Extended diagrams are homogeneous.** -/
theorem xev_exists_mem (ν : X) (s t : List (Letter I)) (L : List (XLayer I)) :
    ∃ p, xev cs ν s t L ∈ homPar D Sc ν s t p := by
  induction L generalizing s with
  | nil => exact ⟨_, cl_mem_homPar' ν s t []⟩
  | cons x L ih =>
    obtain ⟨p, hp⟩ := ih (x.1 ++ x.2.1.cod ++ x.2.2)
    obtain ⟨q, hq⟩ := xlay_exists_mem cs ν x
    exact ⟨_, comp_mem_homPar (cl_mem_homPar' ν s _ []) (comp_mem_homPar hq hp)⟩

/-! ## The super interchange law for extended blocks -/

theorem xev_plcL_right (ν : X) (u : List (Letter I)) {t t' : List (Letter I)}
    (B : List (XLayer I)) :
    plcRight ν u t t' (xev cs ν t t' B) = xev cs ν (u ++ t) (u ++ t') (B.map (xwhL u [])) := by
  dsimp only [plcRight, LinearMap.comp_apply]
  have h := plcL_xev cs ν u [] (s := t) (t := t') B
  erw [h]
  exact wordCast_xev cs ν _ _ _

/-- **Super interchange of two extended blocks**: a block `A` on the left and a block `B` on the
right can be exchanged, up to a sign. -/
theorem xev_interchange (ν : X) {s s' t t' : List (Letter I)} {A B : List (XLayer I)}
    (hA : XChain s A s') (hB : XChain t B t') :
    ∃ p, xev cs ν (s ++ t) (s' ++ t') (A.map (xwhL [] t) ++ B.map (xwhL s' [])) =
      zsign k p • xev cs ν (s ++ t) (s' ++ t') (B.map (xwhL s []) ++ A.map (xwhL [] t')) := by
  obtain ⟨p, hp⟩ := xev_exists_mem cs (wt D ν t) s s' A
  obtain ⟨q, hq⟩ := xev_exists_mem cs ν t t' B
  have hw : wt D ν t = wt D ν t' := hB.wt_eq ν
  have E := plcL_interchange_hom (D := D) (Sc := Sc) ν hw hp hq
  have e₁ := plcL_xev cs ν [] t (s := s) (t := s') A
  have e₂ := plcL_xev cs ν [] t' (s := s) (t := s') A
  rw [regionCast_family (f := fun ν => xev cs ν s s' A), e₁, e₂, xev_plcL_right,
    xev_plcL_right] at E
  refine ⟨p * q, ?_⟩
  have hA' : XChain (s ++ t) (A.map (xwhL [] t)) (s' ++ t) := by simpa using hA.whisk [] t
  have hB' : XChain (s ++ t) (B.map (xwhL s [])) (s ++ t') := by simpa using hB.whisk s []
  rw [xev_append cs _ hA', xev_append cs _ hB']
  exact E

/-- **Super interchange of two extended blocks in context**, up to a sign. -/
theorem xev_ichg (μ : X) {S T : List (Letter I)} (pre post : List (XLayer I))
    (P Q : List (Letter I)) {s s' t t' : List (Letter I)} {A B : List (XLayer I)}
    (hA : XChain s A s') (hB : XChain t B t') (hpre : XChain S pre (P ++ (s ++ t) ++ Q)) :
    ∃ p, xev cs μ S T (pre ++ A.map (xwhL P (t ++ Q)) ++ B.map (xwhL (P ++ s') Q) ++ post) =
      zsign k p •
        xev cs μ S T (pre ++ B.map (xwhL (P ++ s) Q) ++ A.map (xwhL P (t' ++ Q)) ++ post) := by
  obtain ⟨p, hp⟩ := xev_interchange cs (wt D μ Q) hA hB
  have hA' : XChain (s ++ t) (A.map (xwhL [] t) ++ B.map (xwhL s' [])) (s' ++ t') :=
    XChain.append (by simpa using hA.whisk [] t) (by simpa using hB.whisk s' [])
  have hB' : XChain (s ++ t) (B.map (xwhL s []) ++ A.map (xwhL [] t')) (s' ++ t') :=
    XChain.append (by simpa using hB.whisk s []) (by simpa using hA.whisk [] t')
  refine ⟨p, ?_⟩
  have e₁ : pre ++ A.map (xwhL P (t ++ Q)) ++ B.map (xwhL (P ++ s') Q) ++ post =
      pre ++ (A.map (xwhL [] t) ++ B.map (xwhL s' [])).map (xwhL P Q) ++ post := by
    simp only [List.map_append, map_xwhL_xwhL, List.append_nil, List.nil_append, List.append_assoc]
  have e₂ : pre ++ B.map (xwhL (P ++ s) Q) ++ A.map (xwhL P (t' ++ Q)) ++ post =
      pre ++ (B.map (xwhL s []) ++ A.map (xwhL [] t')).map (xwhL P Q) ++ post := by
    simp only [List.map_append, map_xwhL_xwhL, List.append_nil, List.nil_append, List.append_assoc]
  rw [e₁, e₂, xev_ctx cs μ pre post P Q hpre hA', xev_ctx cs μ pre post P Q hpre hB', hp,
    map_smul, Linear.smul_comp, Linear.comp_smul]

/-! ## Letters of both orientations -/

/-- A dot on the strand `l`: the upward dot, or the downward dot (the mate (2.3)). -/
def xDotL : Letter I → List (XLayer I)
  | (true, i) => [([], .gen (.dot i), [])]
  | (false, i) => (ddotL i).map ofL

/-- The crossing `l₁ l₂ → l₂ l₁`: the upward crossing `τ`, the leftward crossing (2.6), the
rightward crossing `σ` (1.11) or the downward crossing (2.1). -/
def xCrL : Letter I → Letter I → List (XLayer I)
  | (true, i), (true, j) => [([], .gen (.cross i j), [])]
  | (false, i), (true, j) => [([], .gen (.lcross i j), [])]
  | (true, j), (false, i) => (sigmaL i j).map ofL
  | (false, i), (false, j) => (dcrossL i j).map ofL

/-- The cup `1 → l l*`: the rightward cup `η` for `l = dn i`, the leftward cup `η'` for
`l = up i`. -/
def xCupL : Letter I → List (XLayer I)
  | (true, i) => [([], .lcup i, [])]
  | (false, i) => [([], .gen (.cup i), [])]

/-- The cap `l* l → 1`: the rightward cap `ε` for `l = dn i`, the leftward cap `ε'` for
`l = up i`. -/
def xCapL : Letter I → List (XLayer I)
  | (true, i) => [([], .lcap i, [])]
  | (false, i) => [([], .gen (.cap i), [])]

theorem xChain_xDotL (l : Letter I) : XChain [l] (xDotL l) [l] := by
  obtain ⟨_ | _, i⟩ := l
  · exact XChain.of_sChain (sChain_mateL i (sChain_dotsL [] i [] 1))
  · exact ⟨rfl, rfl⟩

theorem xChain_xCrL (l₁ l₂ : Letter I) : XChain [l₁, l₂] (xCrL l₁ l₂) [l₂, l₁] := by
  obtain ⟨_ | _, i⟩ := l₁ <;> obtain ⟨_ | _, j⟩ := l₂
  · exact XChain.of_sChain (sChain_dcrossL i j)
  · exact ⟨rfl, rfl⟩
  · exact XChain.of_sChain (sChain_sigmaL j i)
  · exact ⟨rfl, rfl⟩

theorem xChain_xCupL (l : Letter I) : XChain [] (xCupL l) [l, flipL l] := by
  obtain ⟨_ | _, i⟩ := l <;> exact ⟨rfl, rfl⟩

theorem xChain_xCapL (l : Letter I) : XChain [flipL l, l] (xCapL l) [] := by
  obtain ⟨_ | _, i⟩ := l <;> exact ⟨rfl, rfl⟩

@[simp] theorem xcnt_xDotL (l : Letter I) : xcnt (xDotL l) = 0 := by
  obtain ⟨_ | _, i⟩ := l
  · simp [xDotL, ccnt_ddotL]
  · simp [xDotL, XShape.isCross, Shape.isCross]

@[simp] theorem xcnt_xCrL (l₁ l₂ : Letter I) : xcnt (xCrL l₁ l₂) = 1 := by
  obtain ⟨_ | _, i⟩ := l₁ <;> obtain ⟨_ | _, j⟩ := l₂
  · rw [xCrL, xcnt_map_ofL]; simp [dcrossL, ccnt_map_whL, Shape.isCross]
  · simp [xCrL, XShape.isCross, Shape.isCross]
  · rw [xCrL, xcnt_map_ofL, ccnt_sigmaL]
  · simp [xCrL, XShape.isCross, Shape.isCross]

@[simp] theorem xcnt_xCupL (l : Letter I) : xcnt (xCupL l) = 0 := by
  obtain ⟨_ | _, i⟩ := l <;> simp [xCupL, XShape.isCross, Shape.isCross]

@[simp] theorem xcnt_xCapL (l : Letter I) : xcnt (xCapL l) = 0 := by
  obtain ⟨_ | _, i⟩ := l <;> simp [xCapL, XShape.isCross, Shape.isCross]

theorem xDotL_ne_nil (l : Letter I) : xDotL l ≠ [] := by
  obtain ⟨_ | _, i⟩ := l <;> simp [xDotL, ddotL, mateL]

theorem xCrL_ne_nil (l₁ l₂ : Letter I) : xCrL l₁ l₂ ≠ [] := by
  obtain ⟨_ | _, i⟩ := l₁ <;> obtain ⟨_ | _, j⟩ := l₂ <;> simp [xCrL, dcrossL, sigmaL]

/-- `d` dots on the strand `l`. -/
def xDotsL (l : Letter I) (d : ℕ) : List (XLayer I) := (List.replicate d (xDotL l)).flatten

theorem xChain_xDotsL (l : Letter I) (d : ℕ) : XChain [l] (xDotsL l d) [l] := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [xDotsL, List.replicate_succ, List.flatten_cons]
    exact (xChain_xDotL l).append ih

@[simp] theorem xcnt_xDotsL (l : Letter I) (d : ℕ) : xcnt (xDotsL l d) = 0 := by
  simp [xDotsL, xcnt_replicate_flatten]

/-! ## Moves -/

/-- A move: a dot, a crossing of two adjacent strands, or a cup, between the strands `u` and
`v`. -/
inductive Mv (I : Type u)
  | dot (u : List (Letter I)) (l : Letter I) (v : List (Letter I))
  | cross (u : List (Letter I)) (l₁ l₂ : Letter I) (v : List (Letter I))
  | cup (u : List (Letter I)) (l : Letter I) (v : List (Letter I))

namespace Mv

/-- The local layers of a move. -/
def loc : Mv I → List (XLayer I)
  | dot _ l _ => xDotL l
  | cross _ l₁ l₂ _ => xCrL l₁ l₂
  | cup _ l _ => xCupL l

/-- The local bottom boundary of a move. -/
def lsrc : Mv I → List (Letter I)
  | dot _ l _ => [l]
  | cross _ l₁ l₂ _ => [l₁, l₂]
  | cup _ _ _ => []

/-- The local top boundary of a move. -/
def ltgt : Mv I → List (Letter I)
  | dot _ l _ => [l]
  | cross _ l₁ l₂ _ => [l₂, l₁]
  | cup _ l _ => [l, flipL l]

/-- The strands to the left of a move. -/
def pre : Mv I → List (Letter I)
  | dot u _ _ => u
  | cross u _ _ _ => u
  | cup u _ _ => u

/-- The strands to the right of a move. -/
def post : Mv I → List (Letter I)
  | dot _ _ v => v
  | cross _ _ _ v => v
  | cup _ _ v => v

/-- The same move between other strands. -/
def reCtx : Mv I → List (Letter I) → List (Letter I) → Mv I
  | dot _ l _, u, v => dot u l v
  | cross _ l₁ l₂ _, u, v => cross u l₁ l₂ v
  | cup _ l _, u, v => cup u l v

/-- The layers of a move. -/
def lay (m : Mv I) : List (XLayer I) := m.loc.map (xwhL m.pre m.post)

/-- The bottom boundary of a move. -/
def src (m : Mv I) : List (Letter I) := m.pre ++ m.lsrc ++ m.post

/-- The top boundary of a move. -/
def tgt (m : Mv I) : List (Letter I) := m.pre ++ m.ltgt ++ m.post

theorem xChain_loc (m : Mv I) : XChain m.lsrc m.loc m.ltgt := by
  cases m with
  | dot u l v => exact xChain_xDotL l
  | cross u l₁ l₂ v => exact xChain_xCrL l₁ l₂
  | cup u l v => exact xChain_xCupL l

theorem xChain_lay (m : Mv I) : XChain m.src m.lay m.tgt := m.xChain_loc.whisk m.pre m.post

@[simp] theorem reCtx_pre (m : Mv I) (u v : List (Letter I)) : (m.reCtx u v).pre = u := by
  cases m <;> rfl
@[simp] theorem reCtx_post (m : Mv I) (u v : List (Letter I)) : (m.reCtx u v).post = v := by
  cases m <;> rfl
@[simp] theorem reCtx_loc (m : Mv I) (u v : List (Letter I)) : (m.reCtx u v).loc = m.loc := by
  cases m <;> rfl
@[simp] theorem reCtx_lsrc (m : Mv I) (u v : List (Letter I)) : (m.reCtx u v).lsrc = m.lsrc := by
  cases m <;> rfl
@[simp] theorem reCtx_ltgt (m : Mv I) (u v : List (Letter I)) : (m.reCtx u v).ltgt = m.ltgt := by
  cases m <;> rfl

@[simp] theorem xcnt_lay (m : Mv I) : xcnt m.lay = xcnt m.loc := by
  rw [lay, xcnt_map_xwhL]

theorem xcnt_loc (m : Mv I) : xcnt m.loc = match m with | cross .. => 1 | _ => 0 := by
  cases m <;> simp [loc]

end Mv

/-- The layers of a list of moves. -/
def mvLay (ms : List (Mv I)) : List (XLayer I) := (ms.map Mv.lay).flatten

@[simp] theorem mvLay_nil : mvLay ([] : List (Mv I)) = [] := rfl

@[simp] theorem mvLay_append (ms ns : List (Mv I)) : mvLay (ms ++ ns) = mvLay ms ++ mvLay ns := by
  simp [mvLay]

theorem mvLay_singleton (m : Mv I) : mvLay [m] = m.lay := by simp [mvLay]

theorem mvLay_cons (m : Mv I) (ms : List (Mv I)) : mvLay (m :: ms) = m.lay ++ mvLay ms := by
  simp [mvLay]

/-- A chain of moves from `s` to `t`. -/
def MvChain : List (Letter I) → List (Mv I) → List (Letter I) → Prop
  | s, [], t => s = t
  | s, m :: ms, t => s = m.src ∧ MvChain m.tgt ms t

theorem MvChain.xChain : ∀ {s t : List (Letter I)} {ms : List (Mv I)}, MvChain s ms t →
    XChain s (mvLay ms) t
  | _, _, [], h => h
  | _, _, m :: ms, ⟨rfl, h⟩ => by
    rw [mvLay_cons]; exact m.xChain_lay.append h.xChain

theorem MvChain.snoc {s : List (Letter I)} {ms : List (Mv I)} {m : Mv I}
    (h : MvChain s ms m.src) : MvChain s (ms ++ [m]) m.tgt := by
  induction ms generalizing s with
  | nil => exact ⟨h, rfl⟩
  | cons m' ms ih => exact ⟨h.1, ih h.2⟩

theorem MvChain.of_snoc {s t : List (Letter I)} {ms : List (Mv I)} {m : Mv I}
    (h : MvChain s (ms ++ [m]) t) : MvChain s ms m.src ∧ m.tgt = t := by
  induction ms generalizing s with
  | nil => exact ⟨h.1, h.2⟩
  | cons m' ms ih => obtain ⟨h₁, h₂⟩ := ih h.2; exact ⟨⟨h.1, h₁⟩, h₂⟩

theorem MvChain.append : ∀ {s m t : List (Letter I)} {ms ns : List (Mv I)},
    MvChain s ms m → MvChain m ns t → MvChain s (ms ++ ns) t
  | _, _, _, [], _, h₁, h₂ => by subst h₁; exact h₂
  | _, _, _, _ :: _, _, ⟨h, h₁⟩, h₂ => ⟨h, MvChain.append h₁ h₂⟩

/-- Whiskering a list of moves. -/
def mvWh (P Q : List (Letter I)) (ms : List (Mv I)) : List (Mv I) :=
  ms.map fun m => m.reCtx (P ++ m.pre) (m.post ++ Q)

theorem mvLay_mvWh (P Q : List (Letter I)) (ms : List (Mv I)) :
    mvLay (mvWh P Q ms) = (mvLay ms).map (xwhL P Q) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [mvWh, List.map_cons] at ih ⊢
    rw [mvLay_cons, mvLay_cons, ih, List.map_append, Mv.lay, Mv.lay, Mv.reCtx_loc, Mv.reCtx_pre,
      Mv.reCtx_post, map_xwhL_xwhL]

theorem MvChain.wh (P Q : List (Letter I)) : ∀ {s t : List (Letter I)} {ms : List (Mv I)},
    MvChain s ms t → MvChain (P ++ s ++ Q) (mvWh P Q ms) (P ++ t ++ Q)
  | _, _, [], h => by subst h; rfl
  | _, _, m :: ms, ⟨rfl, h⟩ => by
    refine ⟨?_, ?_⟩
    · simp [Mv.src]
    · have := MvChain.wh P Q h
      simpa [mvWh, Mv.tgt] using this

@[simp] theorem xcnt_mvLay_mvWh (P Q : List (Letter I)) (ms : List (Mv I)) :
    xcnt (mvLay (mvWh P Q ms)) = xcnt (mvLay ms) := by
  rw [mvLay_mvWh, xcnt_map_xwhL]

/-- The moves of a strand moving left across `S`. -/
def lmMv : List (Letter I) → Letter I → List (Mv I)
  | [], _ => []
  | s :: S, b => mvWh [s] [] (lmMv S b) ++ [Mv.cross [] s b S]

/-- The moves of a strand moving right across `S`. -/
def rmMv (a : Letter I) : List (Letter I) → List (Mv I)
  | [] => []
  | s :: S => [Mv.cross [] a s S] ++ mvWh [s] [] (rmMv a S)

/-- `d` dots on the strand `l` as moves. -/
def dotMv (d : ℕ) (u : List (Letter I)) (l : Letter I) (v : List (Letter I)) : List (Mv I) :=
  List.replicate d (Mv.dot u l v)

theorem mvChain_lmMv : ∀ (S : List (Letter I)) (b : Letter I),
    MvChain (S ++ [b]) (lmMv S b) (b :: S)
  | [], _ => rfl
  | s :: S, b => by
    rw [lmMv]
    refine MvChain.append (m := [s] ++ (b :: S) ++ []) ?_ ?_
    · simpa using (mvChain_lmMv S b).wh [s] []
    · exact ⟨by simp [Mv.src, Mv.pre, Mv.lsrc, Mv.post], by simp [Mv.tgt, Mv.pre, Mv.ltgt,
        Mv.post, MvChain]⟩

theorem mvChain_rmMv (a : Letter I) : ∀ S : List (Letter I),
    MvChain (a :: S) (rmMv a S) (S ++ [a])
  | [] => rfl
  | s :: S => by
    rw [rmMv]
    refine MvChain.append (m := [s] ++ (a :: S) ++ []) ?_ ?_
    · exact ⟨by simp [Mv.src, Mv.pre, Mv.lsrc, Mv.post], by simp [Mv.tgt, Mv.pre, Mv.ltgt,
        Mv.post, MvChain]⟩
    · simpa using (mvChain_rmMv a S).wh [s] []

theorem mvChain_dotMv (d : ℕ) (u : List (Letter I)) (l : Letter I) (v : List (Letter I)) :
    MvChain (u ++ [l] ++ v) (dotMv d u l v) (u ++ [l] ++ v) := by
  induction d with
  | zero => rfl
  | succ d ih => exact ⟨rfl, ih⟩

@[simp] theorem xcnt_mvLay_dotMv (d : ℕ) (u : List (Letter I)) (l : Letter I)
    (v : List (Letter I)) : xcnt (mvLay (dotMv d u l v)) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [dotMv, List.replicate_succ, mvLay_cons, xcnt_append, ← dotMv, ih, Mv.xcnt_lay]
    simp [Mv.loc]

@[simp] theorem xcnt_mvLay_lmMv : ∀ (S : List (Letter I)) (b : Letter I),
    xcnt (mvLay (lmMv S b)) = S.length
  | [], _ => rfl
  | s :: S, b => by
    rw [lmMv, mvLay_append, xcnt_append, xcnt_mvLay_mvWh, xcnt_mvLay_lmMv S b, mvLay_singleton,
      Mv.xcnt_lay]
    simp [Mv.loc]

@[simp] theorem xcnt_mvLay_rmMv (a : Letter I) : ∀ S : List (Letter I),
    xcnt (mvLay (rmMv a S)) = S.length
  | [] => rfl
  | s :: S => by
    rw [rmMv, mvLay_append, xcnt_append, xcnt_mvLay_mvWh, xcnt_mvLay_rmMv a S, mvLay_singleton,
      Mv.xcnt_lay]
    simp [Mv.loc]; omega

/-! ## Move diagrams followed by bubbles -/

variable (D Sc) in
/-- Move diagrams `E_{w₀} 1_μ → E_v 1_μ` with at most `c` crossings, followed by a product of
bubbles in the rightmost region. -/
def MvSp (μ : X) (w₀ v : List (Letter I)) (c : ℕ) :
    Submodule k ((pres D Sc).obj (ob D μ w₀) ⟶ (pres D Sc).obj (ob D μ v)) :=
  Submodule.span k {f | ∃ (ms : List (Mv I))
    (β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])),
    MvChain w₀ ms v ∧ xcnt (mvLay ms) ≤ c ∧ IsBubbleProd cs μ β ∧
      f = xev cs μ w₀ v (mvLay ms) ≫ bubAt D Sc μ v β}

variable (D Sc) in
/-- 2-morphisms `E_{w₀} 1_μ → E_v 1_μ` factoring through a sequence shorter than `w₀`. -/
def thruShort (μ : X) (w₀ v : List (Letter I)) :
    Submodule k ((pres D Sc).obj (ob D μ w₀) ⟶ (pres D Sc).obj (ob D μ v)) :=
  Submodule.span k {f | ∃ (u : List (Letter I)) (g : (pres D Sc).obj (ob D μ w₀) ⟶
    (pres D Sc).obj (ob D μ u)) (h : (pres D Sc).obj (ob D μ u) ⟶ (pres D Sc).obj (ob D μ v)),
      u.length < w₀.length ∧ f = g ≫ h}

variable (D Sc) in
/-- The target of the elimination of caps: move diagrams followed by bubbles in the rightmost
region, modulo 2-morphisms factoring through shorter sequences. -/
def CapTarget (μ : X) (w₀ v : List (Letter I)) (c : ℕ) :
    Submodule k ((pres D Sc).obj (ob D μ w₀) ⟶ (pres D Sc).obj (ob D μ v)) :=
  MvSp D Sc cs μ w₀ v c ⊔ thruShort D Sc μ w₀ v

section Closure

variable {μ : X} {w₀ : List (Letter I)}

theorem mvSp_mono {v : List (Letter I)} {c c' : ℕ} (h : c ≤ c') :
    MvSp D Sc cs μ w₀ v c ≤ MvSp D Sc cs μ w₀ v c' :=
  Submodule.span_mono fun _ ⟨ms, β, h₁, h₂, h₃, e⟩ => ⟨ms, β, h₁, h₂.trans h, h₃, e⟩

theorem capTarget_mono {v : List (Letter I)} {c c' : ℕ} (h : c ≤ c') :
    CapTarget D Sc cs μ w₀ v c ≤ CapTarget D Sc cs μ w₀ v c' :=
  sup_le_sup_right (mvSp_mono cs h) _

theorem thruShort_comp {v v' : List (Letter I)} {f} (hf : f ∈ thruShort D Sc μ w₀ v)
    (h : (pres D Sc).obj (ob D μ v) ⟶ (pres D Sc).obj (ob D μ v')) :
    f ≫ h ∈ thruShort D Sc μ w₀ v' := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, g, h', hu, rfl⟩ := hf
    exact Submodule.subset_span ⟨u, g, h' ≫ h, hu, by rw [Category.assoc]⟩
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

theorem xev_mvLay_mem_mvSp {v : List (Letter I)} {c : ℕ} {ms : List (Mv I)}
    (hc : MvChain w₀ ms v) (hcc : xcnt (mvLay ms) ≤ c) :
    xev cs μ w₀ v (mvLay ms) ∈ MvSp D Sc cs μ w₀ v c :=
  Submodule.subset_span ⟨ms, 𝟙 _, hc, hcc, .id, by rw [bubAt_id, Category.comp_id]⟩

theorem xev_mem_thruShort {v u : List (Letter I)} (L M : List (XLayer I))
    (hu : u.length < w₀.length) :
    xev cs μ w₀ u L ≫ xev cs μ u v M ∈ thruShort D Sc μ w₀ v :=
  Submodule.subset_span ⟨u, _, _, hu, rfl⟩

/-- A product of bubbles in the rightmost region moves past an extended diagram, up to a sign. -/
theorem bubAt_comp_xev {s t : List (Letter I)} (L : List (XLayer I))
    {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}
    (hβ : IsBubbleProd cs μ β) :
    ∃ p, bubAt D Sc μ s β ≫ xev cs μ s t L = zsign k p • (xev cs μ s t L ≫ bubAt D Sc μ t β) := by
  obtain ⟨p, hp⟩ := xev_exists_mem cs μ s t L
  obtain ⟨q, hq⟩ := hβ.exists_mem
  refine ⟨p * q, ?_⟩
  rw [comp_bubAt hp hq, smul_smul, zsign_mul_self', one_smul]

/-- **Move diagrams compose**: crossings add up and the bubbles collect in the rightmost
region. -/
theorem mvSp_comp {v v' : List (Letter I)} {c c' : ℕ} {f g}
    (hf : f ∈ MvSp D Sc cs μ w₀ v c) (hg : g ∈ MvSp D Sc cs μ v v' c') :
    f ≫ g ∈ MvSp D Sc cs μ w₀ v' (c + c') := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ms, β, hms, hc, hβ, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨ns, γ, hns, hc', hγ, rfl⟩ := hg
      obtain ⟨p, hp⟩ := bubAt_comp_xev cs (s := v) (t := v') (mvLay ns) hβ
      have e : (xev cs μ w₀ v (mvLay ms) ≫ bubAt D Sc μ v β) ≫
          xev cs μ v v' (mvLay ns) ≫ bubAt D Sc μ v' γ =
          zsign k p • (xev cs μ w₀ v' (mvLay (ms ++ ns)) ≫ bubAt D Sc μ v' (β ≫ γ)) := by
        rw [Category.assoc, ← Category.assoc (bubAt D Sc μ v β), hp, Linear.smul_comp,
          Linear.comp_smul, mvLay_append, xev_append cs _ hms.xChain, bubAt_comp]
        simp only [Category.assoc]
      rw [e]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨ms ++ ns, β ≫ γ, hms.append hns,
        ?_, hβ.comp hγ, rfl⟩)
      rw [mvLay_append, xcnt_append]; omega
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ a hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ a hx

theorem capTarget_comp_mvSp {v v' : List (Letter I)} {c c' : ℕ} {f g}
    (hf : f ∈ CapTarget D Sc cs μ w₀ v c) (hg : g ∈ MvSp D Sc cs μ v v' c') :
    f ≫ g ∈ CapTarget D Sc cs μ w₀ v' (c + c') := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
  rw [Preadditive.add_comp]
  exact Submodule.add_mem_sup (mvSp_comp cs ha hg) (thruShort_comp hb _)

theorem capTarget_comp_mvs {c : ℕ} {ns : List (Mv I)} {v v' : List (Letter I)} {f}
    (hf : f ∈ CapTarget D Sc cs μ w₀ v c) (h : MvChain v ns v') :
    f ≫ xev cs μ v v' (mvLay ns) ∈ CapTarget D Sc cs μ w₀ v' (c + xcnt (mvLay ns)) :=
  capTarget_comp_mvSp cs hf (xev_mvLay_mem_mvSp cs h le_rfl)

theorem capTarget_comp_mv {v : List (Letter I)} {c : ℕ} {f} (hf : f ∈ CapTarget D Sc cs μ w₀ v c)
    (m : Mv I) (hm : m.src = v) :
    f ≫ xev cs μ v m.tgt m.lay ∈ CapTarget D Sc cs μ w₀ m.tgt (c + xcnt m.lay) := by
  subst hm
  have := capTarget_comp_mvs cs hf (ns := [m]) ⟨rfl, rfl⟩
  rwa [mvLay_singleton] at this

theorem capTarget_comp_bubAt {v : List (Letter I)} {c : ℕ} {f}
    (hf : f ∈ CapTarget D Sc cs μ w₀ v c)
    {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])} (hβ : IsBubbleProd cs μ β) :
    f ≫ bubAt D Sc μ v β ∈ CapTarget D Sc cs μ w₀ v c := by
  have h : bubAt D Sc μ v β ∈ MvSp D Sc cs μ v v 0 :=
    Submodule.subset_span ⟨[], β, rfl, le_rfl, hβ, by rw [mvLay_nil, xev_nil, cl_nil,
      Category.id_comp]⟩
  simpa using capTarget_comp_mvSp cs hf h

end Closure

/-! ## A strand moving across a block of strands -/

/-- The strand `b` moving left across the strands `S`: `S b → b S`. -/
def lmLc : List (Letter I) → Letter I → List (XLayer I)
  | [], _ => []
  | s :: S, b => (lmLc S b).map (xwhL [s] []) ++ (xCrL s b).map (xwhL [] S)

/-- The strand `a` moving right across the strands `S`: `a S → S a`. -/
def lmRc (a : Letter I) : List (Letter I) → List (XLayer I)
  | [] => []
  | s :: S => (xCrL a s).map (xwhL [] S) ++ (lmRc a S).map (xwhL [s] [])

theorem mvLay_lmMv : ∀ (S : List (Letter I)) (b : Letter I), mvLay (lmMv S b) = lmLc S b
  | [], _ => rfl
  | s :: S, b => by
    rw [lmMv, mvLay_append, mvLay_mvWh, mvLay_lmMv S b, mvLay_singleton, lmLc]
    rfl

theorem mvLay_rmMv (a : Letter I) : ∀ S : List (Letter I), mvLay (rmMv a S) = lmRc a S
  | [] => rfl
  | s :: S => by
    rw [rmMv, mvLay_append, mvLay_mvWh, mvLay_rmMv a S, mvLay_singleton, lmRc]
    rfl

theorem xChain_lmLc (S : List (Letter I)) (b : Letter I) : XChain (S ++ [b]) (lmLc S b) (b :: S) :=
  mvLay_lmMv S b ▸ (mvChain_lmMv S b).xChain

theorem xChain_lmRc (a : Letter I) (S : List (Letter I)) : XChain (a :: S) (lmRc a S) (S ++ [a]) :=
  mvLay_rmMv a S ▸ (mvChain_rmMv a S).xChain

@[simp] theorem xcnt_lmLc (S : List (Letter I)) (b : Letter I) : xcnt (lmLc S b) = S.length := by
  rw [← mvLay_lmMv, xcnt_mvLay_lmMv]

@[simp] theorem xcnt_lmRc (a : Letter I) (S : List (Letter I)) : xcnt (lmRc a S) = S.length := by
  rw [← mvLay_rmMv, xcnt_mvLay_rmMv]

/-! ## The cap block -/

/-- The cap `l* l → 1` joining the strands `A = l*` and `B = l`, with `d` dots on `A`, over which
the strands `S` pass: `B` moves left across `S`, then `d` dots on `A`, then the cap. From
`l* S l` to `S`. -/
def capBlk (S : List (Letter I)) (l : Letter I) (d : ℕ) : List (XLayer I) :=
  (lmLc S l).map (xwhL [flipL l] []) ++ (xDotsL (flipL l) d).map (xwhL [] (l :: S)) ++
    (xCapL l).map (xwhL [] S)

theorem xChain_capBlk (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    XChain ([flipL l] ++ S ++ [l]) (capBlk S l d) S := by
  unfold capBlk
  have h1 : XChain ([flipL l] ++ S ++ [l]) ((lmLc S l).map (xwhL [flipL l] []))
      (flipL l :: l :: S) := by
    simpa using (xChain_lmLc S l).whisk [flipL l] []
  have h2 : XChain (flipL l :: l :: S) ((xDotsL (flipL l) d).map (xwhL [] (l :: S)))
      (flipL l :: l :: S) := by
    simpa using (xChain_xDotsL (flipL l) d).whisk [] (l :: S)
  have h3 : XChain (flipL l :: l :: S) ((xCapL l).map (xwhL [] S)) S := by
    simpa using (xChain_xCapL l).whisk [] S
  exact (h1.append h2).append h3

@[simp] theorem xcnt_capBlk (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    xcnt (capBlk S l d) = S.length := by
  simp [capBlk]

theorem capBlk_nil (l : Letter I) : capBlk [] l 0 = xCapL l := by
  simp [capBlk, lmLc, xDotsL]

end OddMath.SKM
