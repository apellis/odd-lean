/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanOneSided
import OddMath.SKM.SpanR3
import OddMath.SKM.ChordReduced

/-!
# The spanning set of Theorem 8.1 for any choice of reduced matchings (empty bottom boundary)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 8.1, whose
proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification of quantum
`sl(n)`*, arXiv:0807.3250v1, Proposition 3.11.

## Unconditional canonical spanning sets

The local relations `R3Rel`, `CapCurlRel`, `CupCurlRel` are proved (`r3Rel`, `capCurlRel`,
`cupCurlRel`), so the canonical spanning sets hold without hypotheses:

* `diagBubSpan_canonDiagrams_eq_top'`: the canonical chord diagrams with dots at the left ends of
  their arcs, followed by the image of `β_μ` in the rightmost region, span `Hom(1_μ, E_v 1_μ)`;
* `diagBubSpan_bendL_canonDiagrams_eq_top`: their bent forms span `Hom(E_s 1_μ, E_t 1_μ)`. The
  bent canonical diagrams have the pairings of the `st`-matchings but are not reduced matchings
  (a strand gets an extra maximum and minimum), so this is not yet the two-sided Theorem 8.1.

## Theorem 8.1 for an empty bottom boundary

An `∅v`-matching is modelled by a diagram of cups and crossings `E : List (Move (Letter I))`
(`IsNilMatching v E`): reading from the bottom, a cup creates a strand, a crossing crosses two
adjacent strands. Every strand has exactly one critical point (its minimum); the pairing of the
top endpoints is `run flipL E` up to relabelling (`Chord.Iso`), and `E` is reduced
(`Chord.Reduced`) if no strand crosses itself and two strands cross at most once. A decorated
matching is a list of moves and dots (`DMove`), evaluated by `dmLay`. A strand is named by its
left top endpoint `j` (`leftEnds`); a distinguished point of it is a height `h` (the number of
moves below the point) and a position at that height on the strand (`OnStrand`). For counts
`n : ℕ → ℕ`, `Decorates E q n ds` says that `ds` is `E` with `n j` dots at the distinguished point
`q j` of the strand `j`, in any order.

* `theorem_8_1_nil_bottom`: **[BE2] Theorem 8.1 for `a = ∅`, for any choice of representatives
  and distinguished points**.
* `eq_top_of_canon_dots_mem`: the triangular induction on crossings, for any submodule of
  `Hom(1_μ, E_v 1_μ)` (also used for a general bottom boundary, `theorem_8_1_of_pairings`).

The proof follows KL III: by induction on the number of crossings, every diagram is a combination
of chord diagrams with dots followed by bubbles (`capElim_full`, `mv_to_chord`); a chord diagram
is a lower term or, up to sign, the canonical diagram of its pairing (`chordLay_normal_form`).
For a canonical diagram, the dots move to the left ends of their arcs (`arc_dot`) modulo lower
terms and terms with fewer dots; the canonical diagram is, up to sign modulo lower terms, the
chosen reduced representative of its pairing, since a reduced diagram is equivalent to the
canonical one (`equiv_canon_of_reduced`, `equiv_sound`), with the same number of crossings
(`reduced_iff`: reduced diagrams have the minimal number of crossings); finally the dots move
down their strands to the distinguished points (`dmLay_push`). This is triangular: the error terms
have fewer crossings, or as many crossings and fewer dots.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation
open StringDiagrams.Chord (Move Fits canon run Valid Lettered Same Iso idAt Reduced)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {cs : CScalars Sc}

/-! ## The canonical spanning sets, unconditionally -/

section Canonical

variable (cs) in
/-- **[BE2] Theorem 8.1, spanning part, for an empty bottom boundary and the canonical choice of
reduced matchings and distinguished points**: the canonical chord diagrams of the pairings of `v`,
with dots at the left ends of their arcs, followed by the image of `β_μ` in the rightmost region,
span `Hom(1_μ, E_v 1_μ)`. -/
theorem diagBubSpan_canonDiagrams_eq_top' (μ : X) (v : List (Letter I)) :
    diagBubSpan D Sc cs μ [] v (canonDiagrams v) = ⊤ :=
  diagBubSpan_canonDiagrams_eq_top (r3Rel cs) (capCurlRel cs) (cupCurlRel cs) μ v

variable (cs) in
/-- **The bent canonical diagrams span `Hom(E_s 1_μ, E_t 1_μ)`** as a right `SYM`-module (via
`β_μ` in the rightmost region): the canonical one-sided diagrams of the pairings of `s* t`, bent
back by nested caps (`bendL`). These diagrams realise every pairing of an `st`-matching, but they
are not reduced matchings. -/
theorem diagBubSpan_bendL_canonDiagrams_eq_top (μ : X) (s t : List (Letter I)) :
    diagBubSpan D Sc cs μ s t (bendL s t '' canonDiagrams (dualW s ++ t)) = ⊤ :=
  diagBubSpan_bendL_eq_top cs μ (diagBubSpan_canonDiagrams_eq_top' cs μ _)

end Canonical

/-! ## Decorated chord diagrams -/

section Decorated

/-- A move of a decorated chord diagram: a move of a chord diagram (a cup or a crossing), or a dot
on the strand at a position. -/
inductive DMove (I : Type u)
  /-- A cup or a crossing. -/
  | mv (m : Move (Letter I))
  /-- A dot on the strand at position `i`. -/
  | dot (i : ℕ)

namespace DMove

/-- The underlying chord diagram. -/
def moves : List (DMove I) → List (Move (Letter I))
  | [] => []
  | mv m :: ds => m :: moves ds
  | dot _ :: ds => moves ds

/-- The dots, as pairs (height, position); the height is the number of moves below the dot. -/
def dotPts : List (DMove I) → List (ℕ × ℕ)
  | [] => []
  | mv _ :: ds => (dotPts ds).map fun q => (q.1 + 1, q.2)
  | dot i :: ds => (0, i) :: dotPts ds

end DMove

open DMove

/-- The layers of a decorated chord diagram, starting from the letters `l`. -/
def dmLay : List (Letter I) → List (DMove I) → List (XLayer I)
  | _, [] => []
  | l, mv m :: ds => moveLay l m ++ dmLay (chStep l m) ds
  | l, dot i :: ds => dotOn l i ++ dmLay l ds

/-- The position reached from the position `i` by following its strand up through the moves. -/
def fpos (M : List (Move (Letter I))) (i : ℕ) : ℕ := M.foldl (fun j m => movePos m j) i

@[simp] theorem fpos_nil (i : ℕ) : fpos ([] : List (Move (Letter I))) i = i := rfl

@[simp] theorem fpos_cons (m : Move (Letter I)) (M : List (Move (Letter I))) (i : ℕ) :
    fpos (m :: M) i = fpos M (movePos m i) := rfl

/-- The top positions reached by the dots of a decorated chord diagram, moved up their strands. -/
def pushed : List (DMove I) → List ℕ
  | [] => []
  | mv _ :: ds => pushed ds
  | dot i :: ds => fpos (moves ds) i :: pushed ds

/-- The moves and dots of a decorated chord diagram apply to the strands present. -/
def DOk : List (Letter I) → List (DMove I) → Prop
  | _, [] => True
  | l, mv m :: ds => m.Ok l.length ∧ DOk (chStep l m) ds
  | l, dot i :: ds => i < l.length ∧ DOk l ds

theorem movePos_lt {l : List (Letter I)} {m : Move (Letter I)} (hm : m.Ok l.length) {i : ℕ}
    (hi : i < l.length) : movePos m i < (chStep l m).length := by
  rw [Chord.length_lstep]
  cases m with
  | cup g a => simp only [movePos, Chord.Move.len]; split_ifs <;> omega
  | cross p =>
    simp only [Chord.Move.Ok] at hm
    simp only [movePos, Chord.Move.len, Chord.tau]; split_ifs <;> omega

theorem fpos_lt : ∀ {l : List (Letter I)} {M : List (Move (Letter I))}, Fits l.length M →
    ∀ {i : ℕ}, i < l.length → fpos M i < (M.foldl chStep l).length
  | _, [], _, _, hi => hi
  | _, _ :: _, h, _, hi => fpos_lt (fits_chStep h) (movePos_lt h.1 hi)

theorem fits_moves : ∀ {l : List (Letter I)} {ds : List (DMove I)}, DOk l ds →
    Fits l.length (moves ds)
  | _, [], _ => trivial
  | l, mv m :: ds, h => ⟨h.1, by rw [← Chord.length_lstep]; exact fits_moves h.2⟩
  | _, dot _ :: ds, h => by rw [moves]; exact fits_moves (ds := ds) h.2

variable {ν : X} {s₀ t₀ : List (Letter I)}

/-- **A dot passes a chord diagram** (moving up its strand), up to sign modulo lower terms. -/
theorem dot_chord : ∀ {l : List (Letter I)} {M : List (Move (Letter I))}, Fits l.length M →
    ∀ {i : ℕ}, i < l.length → ∀ (P Q : List (XLayer I)), XChain s₀ P l →
    XLt cs ν s₀ t₀ (xcnt P + ncr M + xcnt Q) (P ++ dotOn l i ++ chordLay l M ++ Q)
      (P ++ chordLay l M ++ dotOn (M.foldl chStep l) (fpos M i) ++ Q)
  | l, [], _, i, _, P, Q, _ => by simpa [chordLay] using XLt.refl _
  | l, m :: M, h, i, hi, P, Q, hP => by
    have hm := h.1
    have hM := fits_chStep h
    have h1 := dot_move (cs := cs) (ν := ν) (t₀ := t₀) hm hi P (chordLay (chStep l m) M ++ Q) hP
    have h2 := dot_chord hM (movePos_lt hm hi) (P ++ moveLay l m) Q
      (hP.append (xChain_moveLay hm))
    rw [xcnt_append, xcnt_chordLay hM] at h1
    rw [xcnt_append, xcnt_moveLay hm] at h2
    simp only [chordLay, fpos_cons, List.foldl_cons, List.append_assoc] at h1 h2 ⊢
    have e : ncr (m :: M) = ncr [m] + ncr M := by rw [← ncr_append]; rfl
    rw [e]
    exact (h1.mono (by omega)).trans (h2.mono (by omega))

/-- **The dots of a decorated chord diagram move up their strands to the top**, up to sign modulo
lower terms. -/
theorem dmLay_push : ∀ {l : List (Letter I)} {ds : List (DMove I)}, DOk l ds →
    ∀ (P Q : List (XLayer I)), XChain s₀ P l →
    XLt cs ν s₀ t₀ (xcnt P + ncr (moves ds) + xcnt Q) (P ++ dmLay l ds ++ Q)
      (P ++ chordLay l (moves ds) ++ dotsOn ((moves ds).foldl chStep l) (pushed ds) ++ Q)
  | l, [], _, P, Q, _ => by simpa [dmLay, chordLay, moves, pushed] using XLt.refl _
  | l, mv m :: ds, h, P, Q, hP => by
    have := dmLay_push h.2 (P ++ moveLay l m) Q (hP.append (xChain_moveLay h.1))
    rw [xcnt_append, xcnt_moveLay h.1] at this
    simp only [dmLay, moves, pushed, chordLay, List.foldl_cons, List.append_assoc] at this ⊢
    have e : ncr (m :: moves ds) = ncr [m] + ncr (moves ds) := by rw [← ncr_append]; rfl
    rw [e]
    exact this.mono (by omega)
  | l, dot i :: ds, h, P, Q, hP => by
    have h1 := dmLay_push h.2 (P ++ dotOn l i) Q (hP.append (xChain_dotOn h.1))
    have h2 := dot_chord (cs := cs) (ν := ν) (t₀ := t₀) (fits_moves h.2) h.1 P
      (dotsOn ((moves ds).foldl chStep l) (pushed ds) ++ Q) hP
    rw [xcnt_append, xcnt_dotOn, add_zero] at h1
    rw [xcnt_append, xcnt_dotsOn, zero_add] at h2
    simp only [dmLay, moves, pushed, dotsOn_cons, List.append_assoc] at h1 h2 ⊢
    exact h1.trans h2

theorem dotPts_mem_mv {m : Move (Letter I)} {ds : List (DMove I)} {q : ℕ × ℕ}
    (hq : q ∈ dotPts ds) : (q.1 + 1, q.2) ∈ dotPts (mv m :: ds) := by
  simp only [dotPts, List.mem_map]
  exact ⟨q, hq, rfl⟩

/-- A decorated chord diagram applies when its moves fit and its dots are on strands present. -/
theorem dOk_of : ∀ {l : List (Letter I)} {ds : List (DMove I)}, Fits l.length (moves ds) →
    (∀ q ∈ dotPts ds, q.2 < (((moves ds).take q.1).foldl chStep l).length) → DOk l ds
  | _, [], _, _ => trivial
  | l, mv m :: ds, h, hq => by
    refine ⟨h.1, dOk_of (by rw [Chord.length_lstep]; exact h.2) fun q hmem => ?_⟩
    have := hq _ (dotPts_mem_mv (m := m) hmem)
    simpa [moves] using this
  | l, dot i :: ds, h, hq => by
    refine ⟨by simpa [dotPts] using hq (0, i) (by simp [dotPts]), dOk_of h fun q hmem => ?_⟩
    exact hq q (by simp [dotPts, hmem])

/-- The pushed positions are the dots followed up their strands. -/
theorem pushed_eq : ∀ ds : List (DMove I),
    pushed ds = (dotPts ds).map fun q => fpos ((moves ds).drop q.1) q.2
  | [] => rfl
  | mv m :: ds => by
    rw [pushed, pushed_eq ds]
    simp [dotPts, moves, Function.comp_def]
  | dot i :: ds => by
    rw [pushed, pushed_eq ds]
    simp [dotPts, moves]

end Decorated

/-! ## Strands, left ends and counting -/

section Strands

open DMove

/-- Following a strand up through a move keeps its id. -/
theorem idAt_step_movePos {s : List (ℕ × Letter I)} {m : Move (Letter I)} (hm : m.Ok s.length)
    (i : ℕ) : idAt (Chord.step flipL s m) (movePos m i) = idAt s i := by
  cases m with
  | cup g a =>
    simp only [Chord.Move.Ok] at hm
    exact Chord.idAt_insAt_insIdx hm _ _ _ i
  | cross p =>
    simp only [Chord.Move.Ok] at hm
    show idAt (Chord.swapAt s p) (Chord.tau p i) = idAt s i
    rw [Chord.idAt_swapAt hm, Chord.tau_tau]

/-- **Following a strand up through a diagram keeps its id.** -/
theorem idAt_foldl_fpos : ∀ {s : List (ℕ × Letter I)} {M : List (Move (Letter I))},
    Fits s.length M → ∀ {i : ℕ}, i < s.length →
      idAt (M.foldl (Chord.step flipL) s) (fpos M i) = idAt s i ∧
        fpos M i < (M.foldl (Chord.step flipL) s).length
  | _, [], _, _, hi => ⟨rfl, hi⟩
  | s, m :: M, h, i, hi => by
    have hl : movePos m i < (Chord.step flipL s m).length := by
      rw [Chord.length_step]
      cases m with
      | cup g a => simp only [movePos, Chord.Move.len]; split_ifs <;> omega
      | cross p =>
        have := h.1; simp only [Chord.Move.Ok] at this
        simp only [movePos, Chord.Move.len, Chord.tau]; split_ifs <;> omega
    have := idAt_foldl_fpos (s := Chord.step flipL s m) (M := M)
      (by rw [Chord.length_step]; exact h.2) hl
    rw [idAt_step_movePos h.1 i] at this
    exact this

/-- The position `j` is the left end of its arc: the strands of a pairing are named by their left
endpoints. -/
def IsLeftEnd (s : List (ℕ × Letter I)) (j : ℕ) : Prop :=
  j < s.length ∧ ¬ ∃ j', j' < j ∧ Same s j j'

open scoped Classical in
/-- The strands of a chord diagram, named by their left top endpoints. -/
def leftEnds (E : List (Move (Letter I))) : List ℕ :=
  (List.range (run flipL E).length).filter fun j => decide (IsLeftEnd (run flipL E) j)

theorem mem_leftEnds {E : List (Move (Letter I))} {j : ℕ} :
    j ∈ leftEnds E ↔ IsLeftEnd (run flipL E) j := by
  classical
  simp only [leftEnds, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem nodup_leftEnds (E : List (Move (Letter I))) : (leftEnds E).Nodup :=
  (List.nodup_range).filter _

theorem isLeftEnd_iso {s s' : List (ℕ × Letter I)} (h : Iso s s') {j : ℕ} :
    IsLeftEnd s j ↔ IsLeftEnd s' j := by
  simp only [IsLeftEnd, h.length_eq, h.2]

theorem isLeftEnd_lEnd {s : List (ℕ × Letter I)} (hv : Valid s) {i : ℕ} (hi : i < s.length) :
    IsLeftEnd s (lEnd s i) :=
  ⟨lEnd_lt hi, lEnd_isLeft hv i⟩

/-- The left end of the arc through a position on the arc of a left end `j` is `j`. -/
theorem lEnd_eq_of_isLeftEnd {s : List (ℕ × Letter I)} (hv : Valid s) {j e : ℕ}
    (hj : IsLeftEnd s j) (he : e = j ∨ Same s e j) : lEnd s e = j := by
  rcases he with rfl | he
  · rcases lEnd_spec s e with ⟨h, -⟩ | ⟨hlt, hs⟩
    · exact h
    · exact absurd ⟨_, hlt, hs⟩ hj.2
  · have hje : j < e := by
      rcases lt_trichotomy j e with h | h | h
      · exact h
      · exact absurd h he.ne.symm
      · exact absurd ⟨e, h, he.symm⟩ hj.2
    rcases lEnd_spec s e with ⟨-, h⟩ | ⟨-, hs⟩
    · exact absurd ⟨j, hje, he⟩ h
    · exact hv.unique hs he

/-- Two positions with the same id are equal or on the same arc. -/
theorem eq_or_same_of_idAt {s : List (ℕ × Letter I)} {e j : ℕ} (he : e < s.length)
    (h : idAt s e = idAt s j) : e = j ∨ Same s e j := by
  by_cases hej : e = j
  · exact Or.inl hej
  · exact Or.inr ⟨hej, Chord.idAt_ne_none_iff.2 he, h⟩

/-- A list of elements of a list `K` without repetitions is a permutation of the list with the
same multiplicities, in the order of `K`. -/
theorem perm_flatMap_count {K l : List ℕ} (hK : K.Nodup) (hl : ∀ x ∈ l, x ∈ K) :
    l.Perm (K.flatMap fun j => List.replicate (l.count j) j) := by
  have key : ∀ (K : List ℕ), K.Nodup → ∀ a,
      (K.flatMap fun j => List.replicate (l.count j) j).count a = if a ∈ K then l.count a else 0 := by
    intro K hK a
    induction K with
    | nil => simp
    | cons j K ih =>
      rw [List.flatMap_cons, List.count_append, ih (List.nodup_cons.1 hK).2, List.count_replicate]
      by_cases h : j = a
      · subst h
        simp [(List.nodup_cons.1 hK).1]
      · have h' : a ≠ j := Ne.symm h
        simp [h, h']
  refine List.perm_iff_count.2 fun a => ?_
  rw [key K hK]
  split_ifs with h
  · rfl
  · exact List.count_eq_zero_of_not_mem fun ha => h (hl a ha)

end Strands

/-! ## Theorem 8.1 for an empty bottom boundary -/

section Theorem

open DMove

/-- An **`∅v`-matching**: a diagram of cups and crossings (read from the bottom) whose top letters
are `v`. -/
def IsNilMatching (v : List (Letter I)) (E : List (Move (Letter I))) : Prop :=
  Fits 0 E ∧ E.foldl chStep [] = v

/-- The point `q` (height `q.1`, the number of moves below it, and position `q.2`) lies on the
strand of `E` with top endpoint `j`. -/
def OnStrand (E : List (Move (Letter I))) (j : ℕ) (q : ℕ × ℕ) : Prop :=
  q.2 < (run flipL (E.take q.1)).length ∧
    idAt (run flipL (E.take q.1)) q.2 = idAt (run flipL E) j

/-- **Decorated matchings with dots at the distinguished points**: the decorated diagram `ds` is
`E` with `n j` dots at the distinguished point `q j` of the strand with left top endpoint `j`, for
every strand `j` (the dots at one height in any order). -/
def Decorates (E : List (Move (Letter I))) (q : ℕ → ℕ × ℕ) (n : ℕ → ℕ)
    (ds : List (DMove I)) : Prop :=
  moves ds = E ∧ (dotPts ds).Perm ((leftEnds E).flatMap fun j => List.replicate (n j) (q j))

variable (cs) in
/-- The canonical diagram of the pairing `s` with fewer than `m` dots (anywhere), followed by
products of bubbles. -/
def FewerDots (μ : X) (s : List (ℕ × Letter I)) (m : ℕ) :
    Submodule k ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ (s.map Prod.snd))) :=
  Submodule.span k {f | ∃ (js : List ℕ) (γ : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])),
    (∀ i ∈ js, i < s.length) ∧ js.length < m ∧ IsBubbleProd cs μ γ ∧
      f = xev cs μ [] (s.map Prod.snd) (chordLay [] (canon s) ++ dotsOn (s.map Prod.snd) js) ≫
        bubAt D Sc μ (s.map Prod.snd) γ}

theorem fewerDots_mono (μ : X) (s : List (ℕ × Letter I)) {m m' : ℕ} (h : m ≤ m') :
    FewerDots cs μ s m ≤ FewerDots cs μ s m' :=
  Submodule.span_mono fun _ ⟨js, γ, h1, h2, h3, h4⟩ => ⟨js, γ, h1, by omega, h3, h4⟩

/-- **The dots of a canonical diagram move to the left ends of their arcs**, up to sign modulo
lower terms and terms with fewer dots. -/
theorem dots_to_lEnd (μ : X) {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s) :
    ∀ (is ks : List ℕ), (∀ i ∈ is ++ ks, i < s.length) →
      SignRel (LtL D Sc cs μ [] (s.map Prod.snd) (ncr (canon s)) ⊔
          FewerDots cs μ s (is.length + ks.length))
        (xev cs μ [] (s.map Prod.snd) (chordLay [] (canon s) ++ dotsOn (s.map Prod.snd) (is ++ ks)))
        (xev cs μ [] (s.map Prod.snd)
          (chordLay [] (canon s) ++ dotsOn (s.map Prod.snd) (is.map (lEnd s) ++ ks))) := by
  intro is
  induction is with
  | nil => intro ks _; exact SignRel.refl _
  | cons i is ih =>
    intro ks hb
    set v := s.map Prod.snd with hv'
    have hP := xChain_chordLay_canon hv hl
    have hi : i < s.length := hb i (by simp)
    have hL : lEnd s i < s.length := lEnd_lt hi
    have hb' : ∀ j ∈ is ++ ks, j < s.length := fun j hj => hb j (by simp at hj ⊢; tauto)
    have hS : ∀ {m}, m ≤ (i :: is).length + ks.length →
        LtL D Sc cs μ [] v (ncr (canon s)) ⊔ FewerDots cs μ s m ≤
          LtL D Sc cs μ [] v (ncr (canon s)) ⊔ FewerDots cs μ s ((i :: is).length + ks.length) :=
      fun h => sup_le_sup_left (fewerDots_mono μ s h) _
    -- the first dot moves to the left end of its arc
    have step1 : SignRel (LtL D Sc cs μ [] v (ncr (canon s)) ⊔
          FewerDots cs μ s ((i :: is).length + ks.length))
        (xev cs μ [] v (chordLay [] (canon s) ++ dotOn v i ++ dotsOn v (is ++ ks)))
        (xev cs μ [] v (chordLay [] (canon s) ++ dotOn v (lEnd s i) ++ dotsOn v (is ++ ks))) := by
      rcases lEnd_spec s i with ⟨e, -⟩ | ⟨-, hs⟩
      · rw [e]; exact SignRel.refl _
      · have := arc_dot (cs := cs) μ _ (Nat.lt_succ_self _) hv hl hs.symm (dotsOn v (is ++ ks)) v
        rw [xcnt_dotsOn, add_zero] at this
        refine this.mono (sup_le_sup_left ?_ _)
        refine Submodule.span_le.2 ?_
        rintro _ ⟨β, hβ, rfl⟩
        exact Submodule.subset_span ⟨is ++ ks, β, hb', by simp, hβ, rfl⟩
    -- it joins the dots at the end of the list
    have hperm1 := dotsOn_perm (cs := cs) (ν := μ) (t₀ := v) (n := ncr (canon s)) (t := v)
      (is := lEnd s i :: (is ++ ks)) (js := is ++ (ks ++ [lEnd s i]))
      (by rw [List.perm_iff_count]; intro a
          simp only [List.count_append, List.count_cons, List.count_nil]; omega)
      (by intro j hj; simp only [List.mem_cons] at hj; rcases hj with rfl | hj
          · simpa [v] using hL
          · simpa [v] using hb' j hj)
      (chordLay [] (canon s)) [] hP
    have step2 : SignRel (LtL D Sc cs μ [] v (ncr (canon s)) ⊔
          FewerDots cs μ s ((i :: is).length + ks.length))
        (xev cs μ [] v (chordLay [] (canon s) ++ dotOn v (lEnd s i) ++ dotsOn v (is ++ ks)))
        (xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v (is ++ (ks ++ [lEnd s i])))) := by
      have := (hperm1.signRel).mono (le_sup_left (b := FewerDots cs μ s
        ((i :: is).length + ks.length)))
      simpa only [List.append_nil, dotsOn_cons, List.append_assoc] using this
    have step3 := (ih (ks ++ [lEnd s i]) (by
      intro j hj; simp only [List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | hj | rfl
      · exact hb' j (List.mem_append_left _ hj)
      · exact hb' j (List.mem_append_right _ hj)
      · exact hL)).mono (hS (by simp; omega))
    have hperm2 := dotsOn_perm (cs := cs) (ν := μ) (t₀ := v) (n := ncr (canon s)) (t := v)
      (is := is.map (lEnd s) ++ (ks ++ [lEnd s i])) (js := (i :: is).map (lEnd s) ++ ks)
      (by rw [List.perm_iff_count]; intro a
          simp only [List.count_append, List.count_cons, List.count_nil, List.map_cons]; omega)
      (by
        intro j hj; simp only [List.mem_append, List.mem_map, List.mem_singleton] at hj
        rcases hj with ⟨x, hx, rfl⟩ | hj | rfl
        · simpa [v] using lEnd_lt (by simpa using hb x (by simp [hx]))
        · simpa [v] using hb' j (List.mem_append_right _ hj)
        · simpa [v] using hL)
      (chordLay [] (canon s)) [] hP
    have step4 := (hperm2.signRel).mono (le_sup_left (b := FewerDots cs μ s
      ((i :: is).length + ks.length)))
    simp only [List.append_nil] at step4
    rw [List.cons_append, dotsOn_cons,
      ← List.append_assoc (chordLay [] (canon s)) (dotOn v i) (dotsOn v (is ++ ks))]
    exact step1.trans (step2.trans (step3.trans step4))

/-- The decorated diagrams of a choice: for each chosen matching `E ∈ M` and counts `n`, the
decorated diagram `σ E n`. -/
def decoratedFamily (M : Set (List (Move (Letter I))))
    (σ : List (Move (Letter I)) → (ℕ → ℕ) → List (DMove I)) : Set (List (XLayer I)) :=
  {L | ∃ E ∈ M, ∃ n : ℕ → ℕ, L = dmLay [] (σ E n)}

variable (μ : X) (v : List (Letter I)) (M : Set (List (Move (Letter I))))
  (hM : ∀ E ∈ M, IsNilMatching v E ∧ Reduced flipL E)
  (hrep : ∀ E', IsNilMatching v E' → Reduced flipL E' →
    ∃ E ∈ M, Iso (run flipL E) (run flipL E'))
  (q : List (Move (Letter I)) → ℕ → ℕ × ℕ)
  (hq : ∀ E ∈ M, ∀ j ∈ leftEnds E, OnStrand E j (q E j))
  (σ : List (Move (Letter I)) → (ℕ → ℕ) → List (DMove I))
  (hσ : ∀ E ∈ M, ∀ n, Decorates E (q E) n (σ E n))

include hM hrep hq hσ in
/-- **The canonical diagrams with dots lie in the span of the chosen decorated matchings**, given
that the diagrams with fewer crossings do: induction on the number of dots. -/
theorem canon_dots_mem_decorated (c : ℕ)
    (hlow : LtL D Sc cs μ [] v c ≤ diagBubSpan D Sc cs μ [] v (decoratedFamily M σ)) :
    ∀ (N : ℕ) {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s → s.map Prod.snd = v →
      ncr (canon s) = c → ∀ (is : List ℕ), (∀ i ∈ is, i < s.length) → is.length ≤ N →
      ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}, IsBubbleProd cs μ β →
      xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v is) ≫ bubAt D Sc μ v β ∈
        diagBubSpan D Sc cs μ [] v (decoratedFamily M σ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro s hv hl hsv hc is his hN β hβ
  subst hsv
  set v := s.map Prod.snd with hvdef
  set T := diagBubSpan D Sc cs μ [] v (decoratedFamily M σ)
  -- the chosen representative of the pairing
  obtain ⟨hfc, hrc, -⟩ := Chord.reduced_canon flipL hv hl
  have hcl := canon_letters hv hl
  obtain ⟨E, hEM, hiso⟩ := hrep (canon s) ⟨hfc, hcl.2⟩ hrc
  obtain ⟨⟨hfE, htopE⟩, hredE⟩ := hM E hEM
  have hiso' : Iso (run flipL E) s :=
    hiso.trans (Chord.run_canon (d := flipL) _ (Nat.lt_succ_self _) hv hl).2
  have hlenE : (run flipL E).length = s.length := hiso'.length_eq
  -- its decoration with the multiplicities of the left ends of the dots `is`
  set n : ℕ → ℕ := fun j => (is.map (lEnd s)).count j with hn
  obtain ⟨hmv, hperm⟩ := hσ E hEM n
  set ds := σ E n
  have hpt : ∀ p ∈ dotPts ds, ∃ j ∈ leftEnds E, p = q E j := by
    intro p hp
    obtain ⟨j, hj, hp'⟩ := List.mem_flatMap.1 (hperm.subset hp)
    exact ⟨j, hj, List.eq_of_mem_replicate hp'⟩
  have hlen_take : ∀ h, ((E.take h).foldl chStep []).length = (run flipL (E.take h)).length := by
    intro h; rw [← Chord.snd_run, List.length_map]
  have hdok : DOk [] ds := by
    refine dOk_of (by rw [hmv]; exact hfE) fun p hp => ?_
    obtain ⟨j, hj, rfl⟩ := hpt p hp
    rw [hmv, hlen_take]
    exact (hq E hEM j hj).1
  -- the dots followed up their strands end on the strands of their left ends
  have hF : ∀ j ∈ leftEnds E, fpos (E.drop (q E j).1) (q E j).2 < s.length ∧
      lEnd s (fpos (E.drop (q E j).1) (q E j).2) = j := by
    intro j hj
    obtain ⟨hql, hqid⟩ := hq E hEM j hj
    have hsplit : run flipL E = (E.drop (q E j).1).foldl (Chord.step flipL)
        (run flipL (E.take (q E j).1)) := by
      rw [← Chord.run_append, List.take_append_drop]
    have hfd : Fits (run flipL (E.take (q E j).1)).length (E.drop (q E j).1) := by
      have := (Chord.fits_append 0 (E.take (q E j).1) (E.drop (q E j).1)).1
        (by rw [List.take_append_drop]; exact hfE)
      rw [Chord.run, Chord.length_foldl_step]
      exact this.2
    obtain ⟨hid, hlt⟩ := idAt_foldl_fpos hfd hql
    rw [← hsplit] at hid hlt
    rw [hqid] at hid
    have hjl := (mem_leftEnds.1 hj)
    refine ⟨by rw [← hlenE]; exact hlt, ?_⟩
    refine lEnd_eq_of_isLeftEnd hv ((isLeftEnd_iso hiso').1 hjl) ?_
    rcases eq_or_same_of_idAt hlt hid with h | h
    · exact Or.inl h
    · exact Or.inr ((hiso'.2 _ _).1 h)
  set P := pushed ds with hPdef
  have hPeq : P = (dotPts ds).map fun p => fpos (E.drop p.1) p.2 := by
    rw [hPdef, pushed_eq, hmv]
  have hPb : ∀ e ∈ P, e < s.length := by
    intro e he
    rw [hPeq] at he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    obtain ⟨j, hj, rfl⟩ := hpt p hp
    exact (hF j hj).1
  have hPperm : (P.map (lEnd s)).Perm (is.map (lEnd s)) := by
    have h1 : (P.map (lEnd s)).Perm (((leftEnds E).flatMap fun j =>
        List.replicate (n j) (q E j)).map fun p => lEnd s (fpos (E.drop p.1) p.2)) := by
      rw [hPeq, List.map_map]
      exact hperm.map _
    have h2 : (((leftEnds E).flatMap fun j => List.replicate (n j) (q E j)).map
        fun p => lEnd s (fpos (E.drop p.1) p.2)) =
          (leftEnds E).flatMap fun j => List.replicate (n j) j := by
      rw [List.map_flatMap]
      refine List.flatMap_congr fun j hj => ?_
      rw [List.map_replicate, (hF j hj).2]
    have h3 := perm_flatMap_count (nodup_leftEnds E) (l := is.map (lEnd s)) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact mem_leftEnds.2 ((isLeftEnd_iso hiso').2 (isLeftEnd_lEnd hv (his i hi))))
    rw [h2] at h1
    exact h1.trans h3.symm
  have hPlen : P.length = is.length := by
    simpa using hPperm.length_eq
  -- the chain of moves, up to sign modulo lower terms and terms with fewer dots
  set S := LtL D Sc cs μ [] v c ⊔ FewerDots cs μ s is.length
  have hP := xChain_chordLay_canon hv hl
  have h01 : SignRel S (xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v is))
      (xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v (is.map (lEnd s)))) := by
    have := dots_to_lEnd (cs := cs) μ hv hl is [] (by simpa using his)
    simpa only [List.append_nil, List.length_nil, add_zero, hc] using this
  have h12 : SignRel S (xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v (is.map (lEnd s))))
      (xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v (P.map (lEnd s)))) := by
    have := dotsOn_perm (cs := cs) (ν := μ) (t₀ := v) (n := c) (t := v) hPperm.symm
      (by intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
          simpa [v] using lEnd_lt (his i hi))
      (chordLay [] (canon s)) [] hP
    simpa only [List.append_nil] using this.signRel.mono le_sup_left
  have h23 : SignRel S (xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v (P.map (lEnd s))))
      (xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v P)) := by
    have := dots_to_lEnd (cs := cs) μ hv hl P [] (by simpa using hPb)
    simp only [List.append_nil, List.length_nil, add_zero, hc, hPlen] at this
    exact this.symm
  have hequiv := Chord.equiv_canon_of_reduced flipL hfE hredE
  obtain ⟨hncr, hsound⟩ := equiv_sound (r3Rel cs) hequiv hfE
  rw [Chord.canon_eq_of_iso hiso'] at hncr hsound
  have hE : XChain [] (chordLay [] E) v := by
    have := xChain_chordLay (l := []) hfE; rwa [htopE] at this
  have h34 : SignRel S (xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v P))
      (xev cs μ [] v (chordLay [] E ++ dotsOn v P)) := by
    have := (hsound μ v).append_right (t := v) hE hP (dotsOn v P)
    rw [xcnt_dotsOn, add_zero, hncr, hc] at this
    exact this.symm.signRel.mono le_sup_left
  have h45 : SignRel S (xev cs μ [] v (chordLay [] E ++ dotsOn v P))
      (xev cs μ [] v (dmLay [] ds)) := by
    have := dmLay_push (cs := cs) (ν := μ) (t₀ := v) hdok [] [] (s₀ := []) rfl
    rw [hmv, htopE, hncr, hc] at this
    simp only [xcnt_nil, zero_add, add_zero, List.nil_append, List.append_nil] at this
    exact this.symm.signRel.mono le_sup_left
  have hchain := h01.trans (h12.trans (h23.trans (h34.trans h45)))
  refine hchain.comp_mem ?_ (Submodule.subset_span ⟨_, ⟨E, hEM, n, rfl⟩, β, hβ.isBub, rfl⟩)
  have key : ∀ z ∈ FewerDots cs μ s is.length, z ≫ bubAt D Sc μ v β ∈ T := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨js, γ, hjs, hlen, hγ, rfl⟩ := hz
      rw [Category.assoc, ← bubAt_comp]
      exact ihN js.length (by omega) hv hl rfl hc js hjs le_rfl (hγ.comp hβ)
    | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ a hx
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [Preadditive.add_comp]
  exact Submodule.add_mem _ (hlow (ltL_comp_bubAt hy hβ)) (key z hz)

end Theorem

section Triangular

variable (cs) in
/-- **The triangular induction on crossings** (KL III, proof of Proposition 3.11): a submodule of
`Hom(1_μ, E_v 1_μ)` is everything as soon as it contains the canonical chord diagrams with any
dots, followed by products of bubbles, of every crossing number `c` for which it contains the
diagrams with fewer than `c` crossings. -/
theorem eq_top_of_canon_dots_mem (μ : X) (v : List (Letter I))
    (T : Submodule k ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ v)))
    (h : ∀ c, LtL D Sc cs μ [] v c ≤ T → ∀ {s : List (ℕ × Letter I)}, Valid s →
      Lettered flipL s → s.map Prod.snd = v → ncr (canon s) = c → ∀ (is : List ℕ),
      (∀ i ∈ is, i < s.length) →
      ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}, IsBubbleProd cs μ β →
      xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v is) ≫ bubAt D Sc μ v β ∈ T) :
    T = ⊤ := by
  have key : ∀ (c : ℕ) (L : List (XLayer I)), xcnt L ≤ c → xev cs μ [] v L ∈ T := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ihc =>
    intro L hL
    have hlo : ∀ n ≤ c, LtL D Sc cs μ [] v n ≤ T := by
      intro n hn
      refine Submodule.span_le.2 ?_
      rintro _ ⟨L', hL', rfl⟩
      exact ihc (xcnt L') (by omega) L' le_rfl
    have hcap := capElim_full cs μ [] c v L hL
    rw [CapTarget, thruShort_nil, sup_bot_eq, MvSp] at hcap
    generalize xev cs μ [] v L = x at hcap
    induction hcap using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ms, β, hch, hcc, hβ, rfl⟩ := hx
      set n := xcnt (mvLay ms)
      have hlow : ∀ x ∈ LtL D Sc cs μ [] v n, x ≫ bubAt D Sc μ v β ∈ T :=
        fun x hx => hlo n hcc (ltL_comp_bubAt hx hβ)
      obtain ⟨E, is, hE, hlet, hn, his, hdiff⟩ := mv_to_chord (cs := cs) μ ms hch
      refine hdiff.signRel.comp_mem hlow ?_
      have hsD : XChain [] (chordLay [] E) v := by
        have := xChain_chordLay (l := []) hE; rwa [hlet] at this
      rcases chordLay_normal_form (r3Rel cs) (cupCurlRel cs) hE μ v with h' | ⟨hfc, hnc, hdc⟩
      · refine hlow _ ?_
        rw [xev_append cs _ hsD]
        have := ltL_comp_xev (r := v) h' (dotsOn v is)
        rwa [xcnt_dotsOn, add_zero, hn] at this
      · obtain ⟨s, hs⟩ : ∃ s, s = run flipL E := ⟨_, rfl⟩
        rw [← hs] at hfc hnc hdc
        have hvs : Valid s := hs ▸ (Chord.inv_run hE).1
        have hls : Lettered flipL s := hs ▸ Chord.lettered_run flipL_involutive hE
        have hsv : s.map Prod.snd = v := by rw [hs, Chord.snd_run, ← hlet]
        have hsc : XChain [] (chordLay [] (canon s)) v := by
          have := xChain_chordLay_canon hvs hls; rwa [hsv] at this
        have h2 := hdc.append_right (t := v) hsD hsc (dotsOn v is)
        rw [xcnt_dotsOn, add_zero, hn] at h2
        refine h2.signRel.comp_mem hlow ?_
        exact h n (hlo n hcc) hvs hls hsv (by rw [hnc, hn]) is
          (fun i hi => by rw [← hsv] at his; simpa using his i hi) hβ
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  exact eq_top_of_cl_mem fun L _ => by
    rw [← xev_map_ofL cs]
    exact key _ _ le_rfl

end Triangular

section Theorem

open DMove

variable (μ : X) (v : List (Letter I)) (M : Set (List (Move (Letter I))))
  (hM : ∀ E ∈ M, IsNilMatching v E ∧ Reduced flipL E)
  (hrep : ∀ E', IsNilMatching v E' → Reduced flipL E' →
    ∃ E ∈ M, Iso (run flipL E) (run flipL E'))
  (q : List (Move (Letter I)) → ℕ → ℕ × ℕ)
  (hq : ∀ E ∈ M, ∀ j ∈ leftEnds E, OnStrand E j (q E j))
  (σ : List (Move (Letter I)) → (ℕ → ℕ) → List (DMove I))
  (hσ : ∀ E ∈ M, ∀ n, Decorates E (q E) n (σ E n))

include hM hrep hq hσ in
/-- **[BE2] Theorem 8.1 for an empty bottom boundary (`a = ∅`)**, for any choice of
representatives and distinguished points.

Let `M` be a set of reduced `∅v`-matchings (`IsNilMatching v E`, `Reduced flipL E`) containing a
representative of every equivalence class (same pairing, `Iso` of the final states) of reduced
`∅v`-matchings. For each `E ∈ M` let `q E j` be a distinguished point on the strand with left top
endpoint `j` (`OnStrand`), and for counts `n` let `σ E n` be the decorated matching with `n j`
dots at `q E j` (`Decorates`). Then the 2-morphisms `f(σ E n, μ) = xev (dmLay [] (σ E n))`
generate `Hom(1_μ, E_v 1_μ)` as a right `SYM`-module, `SYM` acting through `β_μ` in the
rightmost region (`diagBubSpan`).

Matchings are encoded by generic layerings (a sequence of cups and crossings); every planar
`∅v`-matching has such layerings, and they differ by the super interchange law, i.e. by signs.

Compared with the printed statement: only `a = ∅` is covered (the two-sided case is open); `M`
need not consist of pairwise inequivalent matchings, and for each `E` and `n` any decorated diagram
with the prescribed dots may be chosen, in particular with the dots at one height in any order
(both only make the statement more general); the hypothesis `wt(a) = wt(b)` is not needed. -/
theorem theorem_8_1_nil_bottom :
    diagBubSpan D Sc cs μ [] v (decoratedFamily M σ) = ⊤ :=
  eq_top_of_canon_dots_mem cs μ v _ fun c hlow _ hv hl hsv hc is his _ hβ =>
    canon_dots_mem_decorated μ v M hM hrep q hq σ hσ c hlow is.length hv hl hsv hc is his le_rfl
      hβ

end Theorem

end OddMath.SKM
