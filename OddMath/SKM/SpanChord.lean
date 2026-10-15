/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanCapsPushCup
import StringDiagrams.Chord.Matching

/-!
# Chord diagrams in `𝔘(𝔤)`: the moves hold up to sign modulo lower terms

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, proof of Proposition 3.11 (the relations allow arbitrary
isotopies of diagrams modulo diagrams with fewer crossings), following A. Lauda,
arXiv:0803.3652v3, §8.

A diagram of cups and crossings in the sense of `StringDiagrams.Chord` (`Chord.Move`, letters the
letters `Letter I` of both orientations with the dual letter `flipL`) gives an extended diagram of
`𝔘(𝔤)` (`chordLay`): a cup `cup g a` is the cup `xCupL a : 1 → a a*` (the rightward cup `η` or the
leftward cup `η'`) between the first `g` strands and the others, a crossing `cross p` the crossing
`xCrL` of the strands `p`, `p + 1`. In the super setting the relations hold up to sign: we show
that the generating moves of `Chord.Equiv` hold up to sign modulo diagrams with fewer crossings
(`rw_sound`), and that reducible diagrams are themselves lower terms (`chordLay_mem_of_reducible`):

* moves at disjoint places: exactly up to sign, by the super interchange law (`xev_ichg`);
* the braid move: Reidemeister 3 modulo lower terms, the hypothesis `R3Rel`;
* the pitchfork move: `cupPF` ((2.4), (2.5), Proposition 7.2);
* a double crossing: Reidemeister 2 (`r2_all`); a curl: the hypothesis `CupCurlRel`.

`LtL ν s t n` is the span of the extended diagrams with fewer than `n` crossings and `XLt` the
equality up to sign modulo `LtL` (for `n = 0`, equality up to sign).

## Main results

* `chordLay`, `xChain_chordLay`, `xcnt_chordLay`: the diagram of a chord diagram.
* `step_sound`, `rw_sound`, `equiv_sound`: equivalent chord diagrams agree up to sign in `𝔘(𝔤)`
  modulo lower terms, given `R3Rel`.
* `chordLay_mem_of_reducible`: reducible chord diagrams are lower terms, given `CupCurlRel`.
* `chordLay_normal_form`: every chord diagram is, up to sign modulo lower terms, a lower term or
  the canonical diagram of its pairing, given `R3Rel` and `CupCurlRel`.
-/

noncomputable section

/-! ## Lettered states -/

namespace StringDiagrams.Chord

variable {α : Type*} {d : α → α}

theorem Lettered.symm_of_involutive {s : List (ℕ × α)} (h : Lettered d s)
    (hd : Function.Involutive d) {i j : ℕ} (hij : Same s i j) :
    (s[j]?).map Prod.snd = (s[i]?).map (d ∘ Prod.snd) := by
  rcases lt_or_gt_of_ne hij.ne with hlt | hlt
  · exact h i j hij hlt
  · have := h j i hij.symm hlt
    have hi := hij.lt_left
    have hj := hij.lt_right
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at this ⊢
    simp at this ⊢
    rw [this, hd]

theorem Lettered.swapAt_of_involutive {s : List (ℕ × α)} (h : Lettered d s)
    (hd : Function.Involutive d) {p : ℕ} (hp : p + 1 < s.length) : Lettered d (Chord.swapAt s p) := by
  intro i j hij _
  rw [same_swapAt hp] at hij
  rw [getElem?_swapAt s hp, getElem?_swapAt s hp]
  exact h.symm_of_involutive hd hij

theorem Lettered.insAt {s : List (ℕ × α)} (h : Lettered d s) (hd : Function.Involutive d)
    {g : ℕ} (hg : g ≤ s.length) {k : ℕ} (hk : ∀ x ∈ s, x.1 ≠ k) (a : α) :
    Lettered d (Chord.insAt s g (k, a) (k, d a)) := by
  intro i j hij hlt
  rw [same_insAt_iff hg hk] at hij
  rw [getElem?_insAt s hg, getElem?_insAt s hg]
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, h3, h4, h5⟩
  · simp
  · omega
  · have := h.symm_of_involutive hd h5
    simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
    split_ifs at this ⊢ <;> exact this

theorem Inv.lettered_step {s : List (ℕ × α)} (hs : Inv s) (hl : Lettered d s)
    (hd : Function.Involutive d) {m : Move α} (hm : m.Ok s.length) :
    Lettered d (Chord.step d s m) := by
  cases m with
  | cup g a => exact hl.insAt hd hm (fun x hx => (hs.2 x hx).ne) a
  | cross p => exact hl.swapAt_of_involutive hd hm

/-- The states reached by diagrams are lettered (for an involution `d`). -/
theorem lettered_run (hd : Function.Involutive d) : ∀ {D : List (Move α)}, Fits 0 D →
    Lettered d (run d D) := by
  intro D
  induction D using List.reverseRecOn with
  | nil => intro _ i j hij; have := hij.lt_left; simp [run] at this
  | append_singleton D m ih =>
    intro h
    rw [fits_snoc (d := d)] at h
    rw [run_append]
    exact (inv_run h.1).lettered_step (ih h.1) hd h.2

end StringDiagrams.Chord

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation
open StringDiagrams.Chord (Move Step Rw Fits lstep canon run)

universe u v w

/-! ## The number of crossings of a chord diagram -/

section Count

variable {α : Type*}

/-- The number of crossings of a chord diagram. -/
def ncr (D : List (Move α)) : ℕ := D.countP fun m => match m with
  | .cross _ => true
  | .cup _ _ => false

@[simp] theorem ncr_nil : ncr ([] : List (Move α)) = 0 := rfl

theorem ncr_append (D E : List (Move α)) : ncr (D ++ E) = ncr D + ncr E := by
  simp [ncr, List.countP_append]

@[simp] theorem ncr_cons_cross (p : ℕ) (D : List (Move α)) : ncr (.cross p :: D) = ncr D + 1 := by
  simp [ncr]

@[simp] theorem ncr_cons_cup (g : ℕ) (a : α) (D : List (Move α)) : ncr (.cup g a :: D) = ncr D := by
  simp [ncr]

theorem ncr_step {L R : List (Move α)} (hs : Step L R) : ncr L = ncr R := by
  cases hs <;> simp [ncr]

end Count

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## The diagram of a chord diagram -/

section Layers

/-- The effect of a move on the letters: `cup g a` inserts `a, a*` at `g`, `cross p` exchanges
the letters at `p` and `p + 1`. -/
abbrev chStep (l : List (Letter I)) (m : Move (Letter I)) : List (Letter I) := lstep flipL l m

/-- The layers of a move applied to the letters `l`: the cup `xCupL a : 1 → a a*` or the crossing
`xCrL` of two adjacent strands, placed between the other strands. -/
def moveLay (l : List (Letter I)) : Move (Letter I) → List (XLayer I)
  | .cup g a => (xCupL a).map (xwhL (l.take g) (l.drop g))
  | .cross p => match l.drop p with
    | x :: y :: r => (xCrL x y).map (xwhL (l.take p) r)
    | _ => []

/-- **The layers of a chord diagram** (moves read from the bottom) starting from the letters
`l`. -/
def chordLay : List (Letter I) → List (Move (Letter I)) → List (XLayer I)
  | _, [] => []
  | l, m :: D => moveLay l m ++ chordLay (chStep l m) D

theorem flipL_involutive : Function.Involutive (flipL (I := I)) := flipL_flipL

theorem swapAt_mid {β : Type*} (u w : List β) (x y : β) :
    Chord.swapAt (u ++ x :: y :: w) u.length = u ++ y :: x :: w := by
  have hp : u.length + 1 < (u ++ x :: y :: w).length := by simp
  apply List.ext_getElem?; intro i
  rw [Chord.getElem?_swapAt _ hp]
  rcases (show i < u.length ∨ i = u.length ∨ i = u.length + 1 ∨ u.length + 1 < i by omega) with
    h | rfl | rfl | h
  · rw [Chord.tau_of_ne (by omega) (by omega), List.getElem?_append_left h,
      List.getElem?_append_left h]
  · simp [Chord.tau_left]
  · simp [Chord.tau_right]
  · rw [Chord.tau_of_ne (by omega) (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, i = u.length + 2 + m := ⟨i - u.length - 2, by omega⟩
    simp [show u.length + 2 + m - u.length = m + 2 by omega]

@[simp] theorem moveLay_cup (u w : List (Letter I)) (a : Letter I) :
    moveLay (u ++ w) (.cup u.length a) = (xCupL a).map (xwhL u w) := by
  simp [moveLay]

@[simp] theorem moveLay_cross (u w : List (Letter I)) (x y : Letter I) :
    moveLay (u ++ x :: y :: w) (.cross u.length) = (xCrL x y).map (xwhL u w) := by
  simp [moveLay]

@[simp] theorem chStep_cup (u w : List (Letter I)) (a : Letter I) :
    chStep (u ++ w) (.cup u.length a) = u ++ a :: flipL a :: w := by
  simp [chStep, lstep, Chord.insAt]

@[simp] theorem chStep_cross (u w : List (Letter I)) (x y : Letter I) :
    chStep (u ++ x :: y :: w) (.cross u.length) = u ++ y :: x :: w := by
  simp only [chStep, lstep]; exact swapAt_mid u w x y

theorem moveLay_cup_eq {l u w : List (Letter I)} {g : ℕ} (a : Letter I) (hl : l = u ++ w)
    (hg : g = u.length) : moveLay l (.cup g a) = (xCupL a).map (xwhL u w) := by
  subst hl hg; exact moveLay_cup u w a

theorem chStep_cup_eq {l u w : List (Letter I)} {g : ℕ} (a : Letter I) (hl : l = u ++ w)
    (hg : g = u.length) : chStep l (.cup g a) = u ++ a :: flipL a :: w := by
  subst hl hg; exact chStep_cup u w a

theorem moveLay_cross_eq {l u w : List (Letter I)} {x y : Letter I} {p : ℕ}
    (hl : l = u ++ x :: y :: w) (hp : p = u.length) :
    moveLay l (.cross p) = (xCrL x y).map (xwhL u w) := by
  subst hl hp; exact moveLay_cross u w x y

theorem chStep_cross_eq {l u w : List (Letter I)} {x y : Letter I} {p : ℕ}
    (hl : l = u ++ x :: y :: w) (hp : p = u.length) : chStep l (.cross p) = u ++ y :: x :: w := by
  subst hl hp; exact chStep_cross u w x y

theorem exists_split_cup {β : Type*} {l : List β} {g : ℕ} (h : g ≤ l.length) :
    ∃ u w, l = u ++ w ∧ u.length = g :=
  ⟨l.take g, l.drop g, (List.take_append_drop g l).symm, by simp; omega⟩

theorem exists_split_cross {β : Type*} {l : List β} {p : ℕ} (h : p + 1 < l.length) :
    ∃ u x y w, l = u ++ x :: y :: w ∧ u.length = p := by
  obtain ⟨u, w', rfl, hu⟩ := exists_split_cup (l := l) (g := p) (by omega)
  match w', h with
  | x :: y :: w, _ => exact ⟨u, x, y, w, rfl, hu⟩
  | [], h => simp at h; omega
  | [x], h => simp at h; omega

theorem xChain_moveLay {l : List (Letter I)} {m : Move (Letter I)} (h : m.Ok l.length) :
    XChain l (moveLay l m) (chStep l m) := by
  cases m with
  | cup g a =>
    obtain ⟨u, w, rfl, rfl⟩ := exists_split_cup (l := l) h
    rw [moveLay_cup, chStep_cup]
    simpa using (xChain_xCupL a).whisk u w
  | cross p =>
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) h
    rw [moveLay_cross, chStep_cross]
    simpa using (xChain_xCrL x y).whisk u w

theorem xcnt_moveLay {l : List (Letter I)} {m : Move (Letter I)} (h : m.Ok l.length) :
    xcnt (moveLay l m) = ncr [m] := by
  cases m with
  | cup g a =>
    obtain ⟨u, w, rfl, rfl⟩ := exists_split_cup (l := l) h
    rw [moveLay_cup]; simp
  | cross p =>
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) h
    rw [moveLay_cross]; simp

theorem chordLay_append : ∀ (l : List (Letter I)) (D E : List (Move (Letter I))),
    chordLay l (D ++ E) = chordLay l D ++ chordLay (D.foldl chStep l) E
  | l, [], E => rfl
  | l, m :: D, E => by
    simp only [List.cons_append, chordLay, List.foldl_cons, chordLay_append _ D E,
      List.append_assoc]

theorem fits_chStep {l : List (Letter I)} {m : Move (Letter I)} {D : List (Move (Letter I))}
    (h : Fits l.length (m :: D)) : Fits (chStep l m).length D := by
  rw [Chord.length_lstep]; exact h.2

theorem xChain_chordLay : ∀ {l : List (Letter I)} {D : List (Move (Letter I))},
    Fits l.length D → XChain l (chordLay l D) (D.foldl chStep l)
  | _, [], _ => rfl
  | _, _ :: _, h => (xChain_moveLay h.1).append (xChain_chordLay (fits_chStep h))

theorem xcnt_chordLay : ∀ {l : List (Letter I)} {D : List (Move (Letter I))},
    Fits l.length D → xcnt (chordLay l D) = ncr D
  | _, [], _ => rfl
  | l, m :: D, h => by
    rw [chordLay, xcnt_append, xcnt_moveLay h.1, xcnt_chordLay (fits_chStep h), ← ncr_append]
    rfl

theorem chordLay_pair (l : List (Letter I)) (m₁ m₂ : Move (Letter I)) :
    chordLay l [m₁, m₂] = moveLay l m₁ ++ moveLay (chStep l m₁) m₂ := by
  simp [chordLay]

theorem chordLay_triple (l : List (Letter I)) (m₁ m₂ m₃ : Move (Letter I)) :
    chordLay l [m₁, m₂, m₃] =
      moveLay l m₁ ++ moveLay (chStep l m₁) m₂ ++ moveLay (chStep (chStep l m₁) m₂) m₃ := by
  simp [chordLay]

theorem foldl_len_eq (l : List (Letter I)) (D : List (Move (Letter I))) :
    D.foldl Move.len l.length = (D.foldl chStep l).length :=
  (Chord.foldl_lstep_len l D).symm

theorem chordLay_mid (A L B : List (Move (Letter I))) :
    chordLay [] (A ++ L ++ B) = chordLay [] A ++ chordLay (A.foldl chStep []) L ++
      chordLay (L.foldl chStep (A.foldl chStep [])) B := by
  rw [chordLay_append, chordLay_append, List.foldl_append, List.append_assoc]

theorem fits_parts {A L B : List (Move (Letter I))} (h : Fits 0 (A ++ L ++ B)) :
    Fits 0 A ∧ Fits (A.foldl chStep []).length L ∧
      Fits (L.foldl chStep (A.foldl chStep [])).length B := by
  have h' := h
  rw [Chord.fits_append, Chord.fits_append] at h'
  refine ⟨h'.1.1, ?_, ?_⟩
  · have := h'.1.2
    rwa [show (0 : ℕ) = ([] : List (Letter I)).length from rfl, foldl_len_eq] at this
  · have := h'.2
    rwa [List.foldl_append, show (0 : ℕ) = ([] : List (Letter I)).length from rfl, foldl_len_eq,
      foldl_len_eq] at this

theorem xcnt_chordLay_mid {A L B : List (Move (Letter I))} (h : Fits 0 (A ++ L ++ B)) :
    xcnt (chordLay [] A) + ncr L + xcnt (chordLay (L.foldl chStep (A.foldl chStep [])) B) =
      ncr (A ++ L ++ B) := by
  obtain ⟨hA, -, hB⟩ := fits_parts h
  rw [xcnt_chordLay (l := []) hA, xcnt_chordLay hB, ncr_append, ncr_append]

end Layers

/-! ## Equality up to sign modulo diagrams with fewer crossings -/

section Lt

variable (D Sc) in
/-- **Lower terms**: the span of the extended diagrams `E_s 1_ν → E_t 1_ν` with fewer than `n`
crossings (`⊥` for `n = 0`). -/
def LtL (ν : X) (s t : List (Letter I)) (n : ℕ) :
    Submodule k ((pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)) :=
  Submodule.span k {f | ∃ L, xcnt L < n ∧ f = xev cs ν s t L}

/-- The extended diagrams `L` and `L'` from `s` to `t` agree up to a sign modulo diagrams with
fewer than `n` crossings. -/
def XLt (ν : X) (s t : List (Letter I)) (n : ℕ) (L L' : List (XLayer I)) : Prop :=
  ∃ p : ZMod 2, xev cs ν s t L - zsign k p • xev cs ν s t L' ∈ LtL D Sc cs ν s t n

variable {cs} {ν : X} {s t : List (Letter I)}

theorem xev_mem_ltL {n : ℕ} {L : List (XLayer I)} (h : xcnt L < n) :
    xev cs ν s t L ∈ LtL D Sc cs ν s t n :=
  Submodule.subset_span ⟨L, h, rfl⟩

theorem leL_le_ltL {c n : ℕ} (h : c < n) : LeL D Sc cs ν s t c ≤ LtL D Sc cs ν s t n :=
  Submodule.span_le.2 fun _ ⟨L, hL, e⟩ => Submodule.subset_span ⟨L, by omega, e⟩

theorem ltL_le_leL {c n : ℕ} (h : n ≤ c + 1) : LtL D Sc cs ν s t n ≤ LeL D Sc cs ν s t c :=
  Submodule.span_le.2 fun _ ⟨L, hL, e⟩ => Submodule.subset_span ⟨L, by omega, e⟩

theorem ltL_mono {n n' : ℕ} (h : n ≤ n') : LtL D Sc cs ν s t n ≤ LtL D Sc cs ν s t n' :=
  Submodule.span_mono fun _ ⟨L, hL, e⟩ => ⟨L, by omega, e⟩

theorem ltL_sub_trans {n : ℕ} {a b d : (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)}
    (h₁ : a - b ∈ LtL D Sc cs ν s t n) (h₂ : b - d ∈ LtL D Sc cs ν s t n) :
    a - d ∈ LtL D Sc cs ν s t n := by
  have := Submodule.add_mem _ h₁ h₂; rwa [sub_add_sub_cancel] at this

namespace XLt

variable {n n' : ℕ} {L L' L'' : List (XLayer I)}

theorem refl (L : List (XLayer I)) : XLt cs ν s t n L L :=
  ⟨0, by rw [zsign_zero, one_smul, sub_self]; exact Submodule.zero_mem _⟩

theorem of_smul (p : ZMod 2) (h : xev cs ν s t L = zsign k p • xev cs ν s t L') :
    XLt cs ν s t n L L' :=
  ⟨p, by rw [h, sub_self]; exact Submodule.zero_mem _⟩

theorem of_xeq {c : ℕ} (h : XEq cs ν s t c L L') (hc : c < n) : XLt cs ν s t n L L' := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, leL_le_ltL hc hp⟩

theorem to_xeq {c : ℕ} (h : XLt cs ν s t n L L') (hc : n ≤ c + 1) : XEq cs ν s t c L L' := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, ltL_le_leL hc hp⟩

theorem symm (h : XLt cs ν s t n L L') : XLt cs ν s t n L' L := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p, ?_⟩
  have e : xev cs ν s t L' - zsign k p • xev cs ν s t L =
      (-zsign k p) • (xev cs ν s t L - zsign k p • xev cs ν s t L') := by
    rw [smul_sub, smul_smul, neg_mul, zsign_mul_self', neg_smul, neg_smul, one_smul]; abel
  rw [e]; exact Submodule.smul_mem _ _ hp

theorem trans (h₁ : XLt cs ν s t n L L') (h₂ : XLt cs ν s t n L' L'') : XLt cs ν s t n L L'' := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  refine ⟨p + q, ?_⟩
  have := Submodule.add_mem _ hp (Submodule.smul_mem _ (zsign k p) hq)
  rwa [smul_sub, smul_smul, ← zsign_add, sub_add_sub_cancel] at this

theorem mono (h : XLt cs ν s t n L L') (hn : n ≤ n') : XLt cs ν s t n' L L' := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, ltL_mono hn hp⟩

theorem congr {L₁ L₂ L₁' L₂' : List (XLayer I)} (hL : L₁ = L₂) (hL' : L₁' = L₂')
    (E : XLt cs ν s t n L₂ L₂') : XLt cs ν s t n L₁ L₁' :=
  hL ▸ hL' ▸ E

theorem low (h : XLt cs ν s t n L L') (h' : xev cs ν s t L' ∈ LtL D Sc cs ν s t n) :
    xev cs ν s t L ∈ LtL D Sc cs ν s t n := by
  obtain ⟨p, hp⟩ := h
  have := Submodule.add_mem _ hp (Submodule.smul_mem _ (zsign k p) h')
  rwa [sub_add_cancel] at this

/-- **The super interchange law** as an equality up to sign, with the diagrams given up to
equality. -/
theorem ichg {S T : List (Letter I)} (pre post : List (XLayer I)) (P Q : List (Letter I))
    {s s' t t' : List (Letter I)} {A B : List (XLayer I)} (hA : XChain s A s') (hB : XChain t B t')
    (hpre : XChain S pre (P ++ (s ++ t) ++ Q))
    (hL : L = pre ++ A.map (xwhL P (t ++ Q)) ++ B.map (xwhL (P ++ s') Q) ++ post)
    (hL' : L' = pre ++ B.map (xwhL (P ++ s) Q) ++ A.map (xwhL P (t' ++ Q)) ++ post) :
    XLt cs ν S T n L L' := by
  subst hL hL'
  obtain ⟨p, hp⟩ := xev_ichg cs ν (T := T) pre post P Q hA hB hpre
  exact XLt.of_smul p hp

/-- **A local relation modulo lower terms in context.** -/
theorem «at» {s₀ t₀ : List (Letter I)} (pre post : List (XLayer I)) (u v : List (Letter I))
    {A B : List (XLayer I)} {c₀ : ℕ} (E : XEq cs (wt D ν v) s t c₀ A B)
    (hpre : XChain s₀ pre (u ++ s ++ v)) (hA : XChain s A t) (hB : XChain s B t)
    (hL : L = pre ++ A.map (xwhL u v) ++ post) (hL' : L' = pre ++ B.map (xwhL u v) ++ post)
    (hc : xcnt pre + c₀ + xcnt post < n) : XLt cs ν s₀ t₀ n L L' :=
  of_xeq (XEq.at pre post u v E hpre hA hB hL hL' le_rfl) hc

end XLt

theorem xev_mem_ltL_at {s₀ t₀ : List (Letter I)} {n c₀ : ℕ} {L : List (XLayer I)}
    (pre post : List (XLayer I)) (u v : List (Letter I)) {A : List (XLayer I)}
    (E : xev cs (wt D ν v) s t A ∈ LeL D Sc cs (wt D ν v) s t c₀)
    (hpre : XChain s₀ pre (u ++ s ++ v)) (hA : XChain s A t)
    (hL : L = pre ++ A.map (xwhL u v) ++ post) (hc : xcnt pre + c₀ + xcnt post < n) :
    xev cs ν s₀ t₀ L ∈ LtL D Sc cs ν s₀ t₀ n :=
  leL_le_ltL hc (xev_low_at cs pre post u v E hpre hA hL le_rfl)

end Lt

/-! ## The moves hold up to sign modulo lower terms -/

section Sound

theorem xChain_r3L (a b c : Letter I) : XChain [a, b, c] (r3L a b c) [c, b, a] := by
  have h1 : XChain [a, b, c] ((xCrL a b).map (xwhL [] [c])) [b, a, c] := by
    simpa using (xChain_xCrL a b).whisk [] [c]
  have h2 : XChain [b, a, c] ((xCrL a c).map (xwhL [b] [])) [b, c, a] := by
    simpa using (xChain_xCrL a c).whisk [b] []
  have h3 : XChain [b, c, a] ((xCrL b c).map (xwhL [] [a])) [c, b, a] := by
    simpa using (xChain_xCrL b c).whisk [] [a]
  exact (h1.append h2).append h3

theorem xChain_r3R (a b c : Letter I) : XChain [a, b, c] (r3R a b c) [c, b, a] := by
  have h1 : XChain [a, b, c] ((xCrL b c).map (xwhL [a] [])) [a, c, b] := by
    simpa using (xChain_xCrL b c).whisk [a] []
  have h2 : XChain [a, c, b] ((xCrL a c).map (xwhL [] [b])) [c, a, b] := by
    simpa using (xChain_xCrL a c).whisk [] [b]
  have h3 : XChain [c, a, b] ((xCrL a b).map (xwhL [c] [])) [c, b, a] := by
    simpa using (xChain_xCrL a b).whisk [c] []
  exact (h1.append h2).append h3

variable {cs}

/-- **Each generating move of chord diagrams holds in `𝔘(𝔤)` up to sign modulo lower terms**, in
any context, given Reidemeister 3 (`R3Rel`). -/
theorem step_sound (hR : R3Rel D Sc cs) {L R : List (Move (Letter I))} (hs : Step L R)
    (l : List (Letter I)) (hL : Fits l.length L) {ν : X} {s₀ t₀ : List (Letter I)}
    (pre post : List (XLayer I)) (hpre : XChain s₀ pre l) :
    XLt cs ν s₀ t₀ (xcnt pre + ncr L + xcnt post) (pre ++ chordLay l L ++ post)
      (pre ++ chordLay l R ++ post) := by
  cases hs with
  | @xx p p' h =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) hL.1
    obtain ⟨M, x', y', w', rfl, hM⟩ := exists_split_cross (l := w) (p := p' - u.length - 2)
      (by simp at hL; omega)
    have hB : XChain (M ++ [x', y']) ((xCrL x' y').map (xwhL M [])) (M ++ [y', x']) := by
      simpa using (xChain_xCrL x' y').whisk M []
    have e1 : chordLay (u ++ x :: y :: (M ++ x' :: y' :: w')) [.cross u.length, .cross p'] =
        (xCrL x y).map (xwhL u (M ++ x' :: y' :: w')) ++
          (xCrL x' y').map (xwhL (u ++ y :: x :: M) w') := by
      rw [chordLay_pair, moveLay_cross, chStep_cross,
        moveLay_cross_eq (u := u ++ y :: x :: M) (x := x') (y := y') (w := w') (by simp)
        (by simp; omega)]
    have e2 : chordLay (u ++ x :: y :: (M ++ x' :: y' :: w')) [.cross p', .cross u.length] =
        (xCrL x' y').map (xwhL (u ++ x :: y :: M) w') ++
          (xCrL x y).map (xwhL u (M ++ y' :: x' :: w')) := by
      rw [chordLay_pair, moveLay_cross_eq (u := u ++ x :: y :: M) (x := x') (y := y') (w := w')
          (by simp) (by simp; omega),
        chStep_cross_eq (u := u ++ x :: y :: M) (x := x') (y := y') (w := w') (by simp)
          (by simp; omega),
        moveLay_cross_eq (u := u) (x := x) (y := y) (w := M ++ y' :: x' :: w') (by simp) rfl]
    rw [e1, e2]
    exact XLt.ichg pre post u w' (xChain_xCrL x y) hB (hpre.cast rfl (by simp))
      (by simp) (by simp)
  | @xuL p g a h =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) hL.1
    obtain ⟨M, w', rfl, hM⟩ := exists_split_cup (l := w) (g := g - u.length - 2)
      (by simp at hL; omega)
    have hB : XChain M ((xCupL a).map (xwhL M [])) (M ++ [a, flipL a]) := by
      simpa using (xChain_xCupL a).whisk M []
    have e1 : chordLay (u ++ x :: y :: (M ++ w')) [.cross u.length, .cup g a] =
        (xCrL x y).map (xwhL u (M ++ w')) ++ (xCupL a).map (xwhL (u ++ y :: x :: M) w') := by
      rw [chordLay_pair, moveLay_cross, chStep_cross,
        moveLay_cup_eq (u := u ++ y :: x :: M) (w := w') a (by simp) (by simp; omega)]
    have e2 : chordLay (u ++ x :: y :: (M ++ w')) [.cup g a, .cross u.length] =
        (xCupL a).map (xwhL (u ++ x :: y :: M) w') ++
          (xCrL x y).map (xwhL u (M ++ a :: flipL a :: w')) := by
      rw [chordLay_pair, moveLay_cup_eq (u := u ++ x :: y :: M) (w := w') a (by simp)
          (by simp; omega),
        chStep_cup_eq (u := u ++ x :: y :: M) (w := w') a (by simp) (by simp; omega),
        moveLay_cross_eq (u := u) (x := x) (y := y) (w := M ++ a :: flipL a :: w') (by simp) rfl]
    rw [e1, e2]
    exact XLt.ichg pre post u w' (xChain_xCrL x y) hB (hpre.cast rfl (by simp))
      (by simp) (by simp)
  | @xuR p g a h =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, w0, rfl, rfl⟩ := exists_split_cup (l := l) (g := g) (by omega)
    obtain ⟨M, x, y, w, rfl, hM⟩ := exists_split_cross (l := w0) (p := p - u.length)
      (by simp at hL; omega)
    have hB : XChain (M ++ [x, y]) ((xCrL x y).map (xwhL M [])) (M ++ [y, x]) := by
      simpa using (xChain_xCrL x y).whisk M []
    have e1 : chordLay (u ++ (M ++ x :: y :: w)) [.cross p, .cup u.length a] =
        (xCrL x y).map (xwhL (u ++ M) w) ++ (xCupL a).map (xwhL u (M ++ y :: x :: w)) := by
      rw [chordLay_pair, moveLay_cross_eq (u := u ++ M) (x := x) (y := y) (w := w) (by simp)
          (by simp; omega),
        chStep_cross_eq (u := u ++ M) (x := x) (y := y) (w := w) (by simp) (by simp; omega),
        moveLay_cup_eq (u := u) (w := M ++ y :: x :: w) a (by simp) rfl]
    have e2 : chordLay (u ++ (M ++ x :: y :: w)) [.cup u.length a, .cross (p + 2)] =
        (xCupL a).map (xwhL u (M ++ x :: y :: w)) ++
          (xCrL x y).map (xwhL (u ++ a :: flipL a :: M) w) := by
      rw [chordLay_pair, moveLay_cup, chStep_cup,
        moveLay_cross_eq (u := u ++ a :: flipL a :: M) (x := x) (y := y) (w := w) (by simp)
          (by simp; omega)]
    rw [e1, e2]
    exact (XLt.ichg pre post u w (xChain_xCupL a) hB (hpre.cast rfl (by simp))
      (by simp) (by simp)).symm
  | @uu g g' a b h =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, w0, rfl, rfl⟩ := exists_split_cup (l := l) (g := g') (by omega)
    obtain ⟨M, w, rfl, hM⟩ := exists_split_cup (l := w0) (g := g - u.length)
      (by simp at hL; omega)
    have hB : XChain M ((xCupL a).map (xwhL M [])) (M ++ [a, flipL a]) := by
      simpa using (xChain_xCupL a).whisk M []
    have e1 : chordLay (u ++ (M ++ w)) [.cup g a, .cup u.length b] =
        (xCupL a).map (xwhL (u ++ M) w) ++ (xCupL b).map (xwhL u (M ++ a :: flipL a :: w)) := by
      rw [chordLay_pair, moveLay_cup_eq (u := u ++ M) (w := w) a (by simp) (by simp; omega),
        chStep_cup_eq (u := u ++ M) (w := w) a (by simp) (by simp; omega),
        moveLay_cup_eq (u := u) (w := M ++ a :: flipL a :: w) b (by simp) rfl]
    have e2 : chordLay (u ++ (M ++ w)) [.cup u.length b, .cup (g + 2) a] =
        (xCupL b).map (xwhL u (M ++ w)) ++ (xCupL a).map (xwhL (u ++ b :: flipL b :: M) w) := by
      rw [chordLay_pair, moveLay_cup, chStep_cup,
        moveLay_cup_eq (u := u ++ b :: flipL b :: M) (w := w) a (by simp) (by simp; omega)]
    rw [e1, e2]
    exact (XLt.ichg pre post u w (xChain_xCupL b) hB (hpre.cast rfl (by simp))
      (by simp) (by simp)).symm
  | braid p =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) (p := p) (by omega)
    obtain ⟨z, Q, rfl⟩ : ∃ z Q, w = z :: Q := by
      match w, hL with
      | z :: Q, _ => exact ⟨z, Q, rfl⟩
      | [], hL => simp at hL
    have e1 : chordLay (u ++ x :: y :: z :: Q) [.cross u.length, .cross (u.length + 1),
        .cross u.length] = (r3L x y z).map (xwhL u Q) := by
      rw [chordLay_triple, moveLay_cross, chStep_cross,
        moveLay_cross_eq (u := u ++ [y]) (x := x) (y := z) (w := Q) (by simp) (by simp),
        chStep_cross_eq (u := u ++ [y]) (x := x) (y := z) (w := Q) (by simp) (by simp),
        moveLay_cross_eq (u := u) (x := y) (y := z) (w := x :: Q) (by simp) rfl]
      simp [r3L]
    have e2 : chordLay (u ++ x :: y :: z :: Q) [.cross (u.length + 1), .cross u.length,
        .cross (u.length + 1)] = (r3R x y z).map (xwhL u Q) := by
      rw [chordLay_triple,
        moveLay_cross_eq (u := u ++ [x]) (x := y) (y := z) (w := Q) (by simp) (by simp),
        chStep_cross_eq (u := u ++ [x]) (x := y) (y := z) (w := Q) (by simp) (by simp),
        moveLay_cross_eq (u := u) (x := x) (y := z) (w := y :: Q) (by simp) rfl,
        chStep_cross_eq (u := u) (x := x) (y := z) (w := y :: Q) (by simp) rfl,
        moveLay_cross_eq (u := u ++ [z]) (x := x) (y := y) (w := Q) (by simp) (by simp)]
      simp [r3R]
    rw [e1, e2]
    exact XLt.at pre post u Q (hR _ x y z) (hpre.cast rfl (by simp)) (xChain_r3L x y z)
      (xChain_r3R x y z) rfl rfl (by simp [ncr])
  | pitch g a =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, w, rfl, rfl⟩ := exists_split_cup (l := l) (g := g) (by omega)
    obtain ⟨m, Q, rfl⟩ : ∃ m Q, w = m :: Q := by
      match w, hL with
      | m :: Q, _ => exact ⟨m, Q, rfl⟩
      | [], hL => simp at hL
    have e1 : chordLay (u ++ m :: Q) [.cup u.length a, .cross (u.length + 1)] =
        ((xCupL a).map (xwhL [] [m]) ++ (xCrL (flipL a) m).map (xwhL [a] [])).map
          (xwhL u Q) := by
      rw [chordLay_pair, moveLay_cup, chStep_cup,
        moveLay_cross_eq (u := u ++ [a]) (x := flipL a) (y := m) (w := Q) (by simp) (by simp)]
      simp
    have e2 : chordLay (u ++ m :: Q) [.cup (u.length + 1) a, .cross u.length] =
        ((xCupL a).map (xwhL [m] []) ++ (xCrL m a).map (xwhL [] [flipL a])).map
          (xwhL u Q) := by
      rw [chordLay_pair, moveLay_cup_eq (u := u ++ [m]) (w := Q) a (by simp) (by simp),
        chStep_cup_eq (u := u ++ [m]) (w := Q) a (by simp) (by simp),
        moveLay_cross_eq (u := u) (x := m) (y := a) (w := flipL a :: Q) (by simp) rfl]
      simp
    rw [e1, e2]
    refine XLt.at pre post u Q (cupPF cs _ a m) (hpre.cast rfl (by simp)) ?_ ?_ rfl rfl
      (by simp [ncr])
    · exact ((xChain_xCupL a).whisk [] [m]).app ((xChain_xCrL (flipL a) m).whisk [a] [])
        (by simp) |>.cast (by simp) (by simp)
    · exact ((xChain_xCupL a).whisk [m] []).app ((xChain_xCrL m a).whisk [] [flipL a])
        (by simp) |>.cast (by simp) (by simp)

/-- **A generating move in context holds in `𝔘(𝔤)` up to sign modulo lower terms.** -/
theorem rw_sound (hR : R3Rel D Sc cs) {D₁ D₂ : List (Move (Letter I))} (h : Rw D₁ D₂)
    (hf : Fits 0 D₁) (ν : X) (v : List (Letter I)) :
    ncr D₁ = ncr D₂ ∧ XLt cs ν [] v (ncr D₁) (chordLay [] D₁) (chordLay [] D₂) := by
  obtain ⟨A, B, L, R, hs, rfl, rfl⟩ := h
  refine ⟨by rw [ncr_append, ncr_append, ncr_append, ncr_append, ncr_step hs], ?_⟩
  obtain ⟨hA, hL, -⟩ := fits_parts hf
  have hlet := (hs.fits_letters (d := flipL) (A.foldl chStep [])).2 hL
  rw [chordLay_mid, chordLay_mid, ← hlet, ← xcnt_chordLay_mid hf]
  exact step_sound hR hs _ hL _ _ (xChain_chordLay (l := []) hA)

/-- **Equivalent chord diagrams agree in `𝔘(𝔤)` up to sign modulo lower terms.** -/
theorem equiv_sound (hR : R3Rel D Sc cs) {D₁ D₂ : List (Move (Letter I))}
    (h : Chord.Equiv D₁ D₂) (hf : Fits 0 D₁) :
    ncr D₁ = ncr D₂ ∧ ∀ (ν : X) (v : List (Letter I)),
      XLt cs ν [] v (ncr D₁) (chordLay [] D₁) (chordLay [] D₂) := by
  induction h with
  | rel D₁ D₂ h => exact ⟨(rw_sound (ν := 0) hR h hf []).1, fun ν v => (rw_sound hR h hf ν v).2⟩
  | refl D₁ => exact ⟨rfl, fun _ _ => XLt.refl _⟩
  | symm D₁ D₂ h ih =>
    have hf' : Fits 0 D₁ := ((Chord.Equiv.fits_letters (d := flipL) h []).1).2 hf
    obtain ⟨e, ih⟩ := ih hf'
    exact ⟨e.symm, fun ν v => by rw [← e]; exact (ih ν v).symm⟩
  | trans D₁ D₂ D₃ h h' ih ih' =>
    have hf' : Fits 0 D₂ := ((Chord.Equiv.fits_letters (d := flipL) h []).1).1 hf
    obtain ⟨e, ih⟩ := ih hf
    obtain ⟨e', ih'⟩ := ih' hf'
    exact ⟨e.trans e', fun ν v => (ih ν v).trans (by rw [e]; exact ih' ν v)⟩

/-- **Reducible chord diagrams are lower terms**: a double crossing by Reidemeister 2
(`r2_all`), a curl by the hypothesis `CupCurlRel`; given `R3Rel` for the moves. -/
theorem chordLay_mem_of_reducible (hR : R3Rel D Sc cs) (hU : CupCurlRel D Sc cs)
    {D₁ : List (Move (Letter I))} (h : Chord.Reducible D₁) (hf : Fits 0 D₁) (ν : X)
    (v : List (Letter I)) :
    xev cs ν [] v (chordLay [] D₁) ∈ LtL D Sc cs ν [] v (ncr D₁) := by
  obtain ⟨A, B, p, h⟩ := h
  suffices H : ∀ E, Chord.Equiv D₁ E → (Fits 0 E →
      xev cs ν [] v (chordLay [] E) ∈ LtL D Sc cs ν [] v (ncr E)) →
      xev cs ν [] v (chordLay [] D₁) ∈ LtL D Sc cs ν [] v (ncr D₁) by
    rcases h with h | ⟨a, h⟩
    · refine H _ h fun hE => ?_
      obtain ⟨hA, hL, -⟩ := fits_parts hE
      simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
      obtain ⟨u, x, y, Q, hl, rfl⟩ := exists_split_cross (l := A.foldl chStep []) (p := p)
        (by omega)
      rw [chordLay_mid, ← xcnt_chordLay_mid hE, hl]
      have e : chordLay (u ++ x :: y :: Q) [.cross u.length, .cross u.length] =
          (xCrL x y ++ xCrL y x).map (xwhL u Q) := by
        rw [chordLay_pair, moveLay_cross, chStep_cross, moveLay_cross, List.map_append]
      rw [e]
      refine xev_mem_ltL_at (chordLay [] A) _ u Q (r2_all cs _ x y)
        (by simpa [hl] using xChain_chordLay (l := []) hA)
        ((xChain_xCrL x y).append (xChain_xCrL y x)) rfl (by simp [ncr])
    · refine H _ h fun hE => ?_
      obtain ⟨hA, hL, -⟩ := fits_parts hE
      simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
      obtain ⟨u, Q, hl, rfl⟩ := exists_split_cup (l := A.foldl chStep []) (g := p) (by omega)
      rw [chordLay_mid, ← xcnt_chordLay_mid hE, hl]
      have e : chordLay (u ++ Q) [.cup u.length a, .cross u.length] =
          (xCupL a ++ xCrL a (flipL a)).map (xwhL u Q) := by
        rw [chordLay_pair, moveLay_cup, chStep_cup, moveLay_cross, List.map_append]
      rw [e]
      have hc : xev cs (wt D ν Q) [] [flipL a, a] (xCupL a ++ xCrL a (flipL a)) ∈
          LeL D Sc cs (wt D ν Q) [] [flipL a, a] 0 := by
        have := hU (wt D ν Q) (flipL a)
        rwa [flipL_flipL] at this
      refine xev_mem_ltL_at (chordLay [] A) _ u Q hc
        (by simpa [hl] using xChain_chordLay (l := []) hA)
        ((xChain_xCupL a).append (xChain_xCrL a (flipL a))) rfl (by simp [ncr])
  intro E hDE hE
  have hfE : Fits 0 E := ((Chord.Equiv.fits_letters (d := flipL) hDE []).1).1 hf
  obtain ⟨e, hs⟩ := equiv_sound hR hDE hf
  exact (hs ν v).low (e ▸ hE hfE)

/-- **Normal form of chord diagrams in `𝔘(𝔤)`**, given `R3Rel` and `CupCurlRel`: a chord diagram
is, modulo diagrams with fewer crossings, either `0` or, up to sign, the canonical diagram of its
final pairing (which has as many crossings). -/
theorem chordLay_normal_form (hR : R3Rel D Sc cs) (hU : CupCurlRel D Sc cs)
    {D₁ : List (Move (Letter I))} (hf : Fits 0 D₁) (ν : X) (v : List (Letter I)) :
    xev cs ν [] v (chordLay [] D₁) ∈ LtL D Sc cs ν [] v (ncr D₁) ∨
      (Fits 0 (canon (run flipL D₁)) ∧ ncr (canon (run flipL D₁)) = ncr D₁ ∧
        XLt cs ν [] v (ncr D₁) (chordLay [] D₁) (chordLay [] (canon (run flipL D₁)))) := by
  rcases Chord.equiv_canon_or_reducible (d := flipL) hf with h | h
  · exact Or.inl (chordLay_mem_of_reducible hR hU h hf ν v)
  · obtain ⟨e, hs⟩ := equiv_sound hR h hf
    exact Or.inr ⟨((Chord.Equiv.fits_letters (d := flipL) h []).1).1 hf, e.symm, hs ν v⟩

end Sound

end OddMath.SKM
