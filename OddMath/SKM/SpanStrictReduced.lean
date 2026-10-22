/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanReducedMatchings

/-!
# Strictly reduced matchings ([BE2] §8, Theorem 8.1)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8. A matching is
*reduced* in the sense of the paper if no strand crosses itself, two strands cross at most once,
and every strand has at most one critical point (a cup or a cap). `Reduced₂` records the first two
conditions; `StrictReduced₂` adds the third, the critical points being recorded, like the
crossings, by the ids of their strands (renamed along later caps).

The paper remarks that every matching is equivalent to a reduced one. We prove this in the form
needed for Theorem 8.1: every pairing of `a* b` is the pairing of a strictly reduced
`(a, b)`-matching (`exists_strictReduced_matching`). The matching is built from the top down, as
a canonical diagram: the last move is a cup if two adjacent upper endpoints are joined, and a
crossing if two adjacent strands interleave; when neither applies, all strands are bent strands of
`a` in nested order, and a pair of bottom endpoints joined by the pairing is split into two bent
strands capped together (choosing the pair with the leftmost endpoint, and placing the cap so that
no strand crosses both legs). So bottom–bottom strands consist of one cap, top–top strands of one
cup, through strands have no critical point, and every crossing joins two strands that interleave
in the end and have not crossed before.

## Main results

* `StrictReduced₂`: strictly reduced matchings.
* `exists_strictReduced_matching`: **every pairing of `a* b` is the pairing of a strictly reduced
  `(a, b)`-matching**, so every matching is equivalent to a strictly reduced one
  (`exists_strictReduced_equiv`).
* `exists_strictReduced_matching_shape`: the matching may be chosen to pass through a word with
  two letters fewer than `a` if the pairing joins two bottom endpoints, and to consist of
  crossings between sorted words if it joins no two endpoints on the same edge and `a`, `b` are
  sorted (used in the proof of [BE2] Theorem 11.7).
* `theorem_8_1`: **[BE2] Theorem 8.1** with the hypotheses of the paper.
-/

namespace StringDiagrams.Chord

variable {α : Type*} (d : α → α)

/-! ## Critical points of a two-sided matching -/

/-- The critical points after one more move, each recorded by the id of its strand: a cup adds its
(fresh) strand, a cap adds the joined strand, renaming the records of its right leg. -/
def critStep (k : ℕ) (T : TState α) (cl : List ℕ) : TMove α → List ℕ
  | .mv (.cup _ _) => cl ++ [T.nxt]
  | .mv (.cross _) => cl
  | .cap g => cl.map (rlId (idD T.st (k + g + 1)) (idD T.st (k + g))) ++ [idD T.st (k + g)]

/-- The critical points of a two-sided matching, each recorded by the id of its strand. -/
def tCrit (k : ℕ) : TState α → List ℕ → List (TMove α) → List ℕ
  | _, cl, [] => cl
  | T, cl, m :: R => tCrit k (tStep d k T m) (critStep k T cl m) R

variable {d}

theorem tCrit_snoc (k : ℕ) (m : TMove α) : ∀ (R : List (TMove α)) (T : TState α) (cl : List ℕ),
    tCrit d k T cl (R ++ [m]) = critStep k (tRun d k T R) (tCrit d k T cl R) m
  | [], _, _ => rfl
  | m' :: R, T, cl => tCrit_snoc k m R (tStep d k T m') (critStep k T cl m')

theorem tRun_snoc' (k : ℕ) (T : TState α) (R : List (TMove α)) (m : TMove α) :
    tRun d k T (R ++ [m]) = tStep d k (tRun d k T R) m := by
  simp [tRun, List.foldl_append]

theorem tFits_snoc (k : ℕ) (m : TMove α) : ∀ (T : TState α) (R : List (TMove α)),
    TFits d k T (R ++ [m]) ↔ TFits d k T R ∧ m.Ok d k (tRun d k T R).st
  | _, [] => by simp [TFits, tRun]
  | T, m' :: R => by
    simp only [List.cons_append, TFits, tFits_snoc k m _ R, and_assoc]
    rfl

/-- The strand with id `c` joins a position left of `k` (a bent lower endpoint) to a position
right of it. -/
def IsThrough (k : ℕ) (s : List (ℕ × α)) (c : ℕ) : Prop :=
  ∃ u v, u < k ∧ k ≤ v ∧ idAt s u = some c ∧ idAt s v = some c

/-- The invariant of the critical points: they lie on distinct strands with ids below `nxt`, none of
them a through strand (joining a bent lower endpoint to the strands on the right). -/
structure CritInv (k : ℕ) (T : TState α) (cl : List ℕ) : Prop where
  nodup : cl.Nodup
  lt : ∀ c ∈ cl, c < T.nxt
  notQA : ∀ c ∈ cl, ¬ IsThrough k T.st c

/-- No strand crosses itself and two strands cross at most once. -/
def CrossOnce (T : TState α) : Prop := T.xs.Nodup ∧ ∀ z ∈ T.xs, ¬ z.IsDiag

theorem lt_nxt_of_idAt {T : TState α} (I : TInv T) {u c : ℕ} (h : idAt T.st u = some c) :
    c < T.nxt := by
  simp only [idAt, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  exact I.fresh e (List.mem_of_getElem? he)

theorem critInv_cup {k : ℕ} {T : TState α} (I : TInv T) {cl : List ℕ} (C : CritInv k T cl)
    {g : ℕ} {a : α} (hg : k + g ≤ T.st.length) :
    CritInv k (tStep d k T (.mv (.cup g a))) (critStep k T cl (.mv (.cup g a))) := by
  have hid := idAt_insAt (s := T.st) hg T.nxt a (d a)
  refine ⟨C.nodup.append (List.nodup_singleton _) (fun c hc hc' => ?_), fun c hc => ?_,
    fun c hc hq => ?_⟩
  · rw [List.mem_singleton] at hc'; have := C.lt c hc; omega
  · simp only [critStep, List.mem_append, List.mem_singleton] at hc
    show c < T.nxt + 1
    rcases hc with hc | rfl
    · have := C.lt c hc; omega
    · omega
  · obtain ⟨u, v, hu, hv, h1, h2⟩ := hq
    simp only [tStep] at h1 h2
    rw [hid] at h1 h2
    simp only [show u < k + g by omega, ↓reduceIte] at h1
    simp only [critStep, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · have hlt := C.lt c hc
      split_ifs at h2 with h3 h4 h5
      · exact C.notQA c hc ⟨u, v, hu, hv, h1, h2⟩
      · simp at h2; omega
      · simp at h2; omega
      · exact C.notQA c hc ⟨u, v - 2, hu, by omega, h1, h2⟩
    · have := lt_nxt_of_idAt I h1; omega

theorem critInv_cross {k : ℕ} {T : TState α} {cl : List ℕ} (C : CritInv k T cl) {p : ℕ}
    (hp : k + p + 1 < T.st.length) :
    CritInv k (tStep d k T (.mv (.cross p))) (critStep k T cl (.mv (.cross p))) := by
  refine ⟨C.nodup, C.lt, fun c hc hq => C.notQA c hc ?_⟩
  obtain ⟨u, v, hu, hv, h1, h2⟩ := hq
  simp only [tStep] at h1 h2
  rw [idAt_swapAt hp] at h1 h2
  refine ⟨u, tau (k + p) v, hu, by unfold tau; split_ifs <;> omega, ?_, h2⟩
  rwa [show tau (k + p) u = u by unfold tau; split_ifs <;> omega] at h1

theorem idAt_jn' {s : List (ℕ × α)} {r : ℕ} (hr : r + 1 < s.length) (i : ℕ) :
    idAt (jn s r) i = (idAt s (rmIdx r i)).map (rlId (idD s (r + 1)) (idD s r)) :=
  idAt_jn hr (idAt_eq_idD (by omega)) (idAt_eq_idD hr) i

/-- **A cap joining two through strands** keeps the invariant of the critical points. -/
theorem critInv_cap {k : ℕ} {T : TState α} (I : TInv T) {cl : List ℕ} (C : CritInv k T cl)
    {g p q : ℕ} (hr : k + g + 1 < T.st.length) (hp : Same T.st (k + g) p)
    (hq : Same T.st (k + g + 1) q) (hpk : p < k) (hqk : q < k) :
    CritInv k (tStep d k T (.cap g)) (critStep k T cl (.cap g)) := by
  set r := k + g
  set x := idD T.st r
  set y := idD T.st (r + 1)
  have hx := idAt_eq_idD (s := T.st) (i := r) (by omega)
  have hy := idAt_eq_idD (s := T.st) (i := r + 1) hr
  have hpx : idAt T.st p = some x := by rw [← hp.2.2, hx]
  have hqy : idAt T.st q = some y := by rw [← hq.2.2, hy]
  have hxcl : x ∉ cl := fun h => C.notQA x h ⟨p, r, hpk, by omega, hpx, hx⟩
  have hycl : y ∉ cl := fun h => C.notQA y h ⟨q, r + 1, hqk, by omega, hqy, hy⟩
  have hmap : cl.map (rlId y x) = cl := by
    conv_rhs => rw [← List.map_id cl]
    refine List.map_congr_left fun c hc => ?_
    simp only [rlId, id]
    split_ifs with h
    · exact absurd (h ▸ hc) hycl
    · rfl
  have e : critStep k T cl (.cap g) = cl ++ [x] := by
    simp only [critStep]; rw [hmap]
  rw [e]
  refine ⟨C.nodup.append (List.nodup_singleton _) (fun c hc hc' => ?_), fun c hc => ?_,
    fun c hc hQ => ?_⟩
  · rw [List.mem_singleton] at hc'; exact hxcl (hc' ▸ hc)
  · show c < T.nxt
    rcases List.mem_append.1 hc with hc | hc
    · exact C.lt c hc
    · rw [List.mem_singleton] at hc; subst hc; exact lt_nxt_of_idAt I hx
  · obtain ⟨u, v, hu, hv, h1, h2⟩ := hQ
    simp only [tStep] at h1 h2
    rw [idAt_jn' hr] at h1 h2
    have hur : rmIdx r u = u := by unfold rmIdx; split_ifs <;> omega
    have hvr := rmIdx_ne r v
    have hvk : k ≤ rmIdx r v := by unfold rmIdx; split_ifs <;> omega
    rw [hur] at h1
    obtain ⟨c₁, hc₁, e₁⟩ := Option.map_eq_some_iff.1 h1
    obtain ⟨c₂, hc₂, e₂⟩ := Option.map_eq_some_iff.1 h2
    rcases List.mem_append.1 hc with hc | hc
    · have hcx : c ≠ x := fun h => hxcl (h ▸ hc)
      have f : ∀ c', rlId y x c' = c → c' = c := fun c' h => by
        simp only [rlId] at h; split_ifs at h <;> [exact absurd h.symm hcx; exact h]
      exact C.notQA c hc ⟨u, rmIdx r v, hu, hvk, by rw [hc₁, f _ e₁], by rw [hc₂, f _ e₂]⟩
    · rw [List.mem_singleton] at hc
      subst hc
      have f : ∀ c', rlId y x c' = x → c' = x ∨ c' = y := fun c' h => by
        simp only [rlId] at h; split_ifs at h with h' <;> [exact Or.inr h'; exact Or.inl h]
      rcases f _ e₂ with e | e <;> rw [e] at hc₂
      · rcases Valid.pos_of_id I.valid hx hpx hc₂ (by omega) with e' | e' <;> omega
      · rcases Valid.pos_of_id I.valid hy hqy hc₂ (by omega) with e' | e' <;> omega

/-! ## Crossings of distinct strands that have not crossed -/

theorem mem_xs_iff {T : TState α} (I : TInv T) (hR : CrossOnce T) {a b : ℕ} (hab : a ≠ b) :
    s(a, b) ∈ T.xs ↔ Ilv2 T.st a b := by
  rw [I.parity a b hab]
  constructor
  · intro h
    rw [List.count_eq_one_of_mem hR.1 h]; exact odd_one
  · intro h
    exact List.count_pos_iff.1 (Nat.pos_of_ne_zero fun e => by rw [e] at h; simp at h)

/-- **A crossing of two strands that do not interleave** keeps a matching reduced. -/
theorem crossOnce_cross {k : ℕ} {T : TState α} (I : TInv T) (hR : CrossOnce T) {p : ℕ}
    (hne : idD T.st (k + p) ≠ idD T.st (k + p + 1))
    (hil : ¬ Ilv2 T.st (idD T.st (k + p)) (idD T.st (k + p + 1))) :
    CrossOnce (tStep d k T (.mv (.cross p))) := by
  refine ⟨hR.1.append (List.nodup_singleton _) (fun z hz hz' => ?_), fun z hz => ?_⟩
  · rw [List.mem_singleton] at hz'; subst hz'
    exact hil ((mem_xs_iff I hR hne).1 hz)
  · rcases List.mem_append.1 hz with hz | hz
    · exact hR.2 z hz
    · rw [List.mem_singleton] at hz; subst hz
      exact fun h => hne (Sym2.mk_isDiag_iff.1 h)

/-- **A cap joining two strands that do not interleave, and do not both interleave a third
strand**, keeps a matching reduced. -/
theorem crossOnce_cap {k : ℕ} {T : TState α} (I : TInv T) (hR : CrossOnce T) {g : ℕ}
    (hxy : ¬ Ilv2 T.st (idD T.st (k + g)) (idD T.st (k + g + 1)))
    (hb : ∀ b, b ≠ idD T.st (k + g) → b ≠ idD T.st (k + g + 1) →
      ¬ (Ilv2 T.st (idD T.st (k + g)) b ∧ Ilv2 T.st (idD T.st (k + g + 1)) b)) :
    CrossOnce (tStep d k T (.cap g)) := by
  set x := idD T.st (k + g)
  set y := idD T.st (k + g + 1)
  set f := rlId y x
  have key : ∀ z ∈ T.xs, Sym2.map f z = z ∨
      ∃ b, z = s(y, b) ∧ b ≠ x ∧ b ≠ y ∧ Sym2.map f z = s(x, b) ∧ s(x, b) ∉ T.xs := by
    intro z hz
    induction z using Sym2.ind with
    | h u v =>
      have huv : u ≠ v := fun e => hR.2 _ hz (Sym2.mk_isDiag_iff.2 e)
      have gen : ∀ u v, s(u, v) ∈ T.xs → u ≠ v → u = y →
          ∃ b, s(u, v) = s(y, b) ∧ b ≠ x ∧ b ≠ y ∧ Sym2.map f s(u, v) = s(x, b) ∧
            s(x, b) ∉ T.xs := by
        intro u v hz huv hu
        subst hu
        have hvx : v ≠ x := fun e => by
          subst e; exact hxy (ilv2_comm.1 ((mem_xs_iff I hR huv).1 hz))
        refine ⟨v, rfl, hvx, huv.symm, ?_, fun h => hb v hvx huv.symm
          ⟨(mem_xs_iff I hR hvx.symm).1 h, (mem_xs_iff I hR huv).1 hz⟩⟩
        simp [f, rlId, huv.symm]
      by_cases hu : u = y
      · exact Or.inr (gen u v hz huv hu)
      by_cases hv : v = y
      · rw [Sym2.eq_swap] at hz ⊢
        exact Or.inr (gen v u hz huv.symm hv)
      · left; simp [f, rlId, hu, hv]
  refine ⟨hR.1.map_on fun z₁ h₁ z₂ h₂ e => ?_, fun z hz => ?_⟩
  · rcases key z₁ h₁ with e₁ | ⟨b₁, rfl, hb₁, -, e₁, n₁⟩ <;>
      rcases key z₂ h₂ with e₂ | ⟨b₂, rfl, hb₂, -, e₂, n₂⟩
    · rw [← e₁, ← e₂]; exact e
    · rw [e₁, e₂] at e; subst e; exact absurd h₁ n₂
    · rw [e₁, e₂] at e; subst e; exact absurd h₂ n₁
    · rw [e₁, e₂, Sym2.eq_iff] at e
      rcases e with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact absurd rfl hb₁
  · obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hz
    rcases key z' hz' with e | ⟨b, -, hbx, -, e, -⟩
    · rw [e]; exact hR.2 z' hz'
    · rw [e]; exact fun h => hbx (Sym2.mk_isDiag_iff.1 h).symm

/-! ## Relabelling ids by a permutation of the positions -/

theorem same_of_idAt_comp {s t : List (ℕ × α)} (π : Equiv.Perm ℕ)
    (h : ∀ j, idAt s j = idAt t (π j)) {u v : ℕ} : Same s u v ↔ Same t (π u) (π v) := by
  simp only [Same, h, ne_eq, π.injective.eq_iff]

theorem valid_of_idAt_comp {s t : List (ℕ × α)} (π : Equiv.Perm ℕ)
    (h : ∀ j, idAt s j = idAt t (π j)) (ht : Valid t) : Valid s := by
  intro j hj
  have hj' : π j < t.length := idAt_ne_none_iff.1 (by rw [← h]; exact idAt_ne_none_iff.2 hj)
  obtain ⟨k, hk, hu⟩ := ht (π j) hj'
  refine ⟨π.symm k, (same_of_idAt_comp π h).2 (by simpa using hk), fun k' hk' => ?_⟩
  rw [← hu _ ((same_of_idAt_comp π h).1 hk')]; simp

/-- **A cap keeps a state lettered**: the joined strand has dual letters at its two ends. -/
theorem Lettered.jn {s : List (ℕ × α)} (h : Lettered d s) (hd : Function.Involutive d) {r : ℕ}
    (hr : r + 1 < s.length) (hlet : (s[r]'(by omega)).2 = d (s[r + 1]'hr).2) :
    Lettered d (Chord.jn s r) := by
  have L : ∀ x : ℕ, ((Chord.jn s r)[x]?).map Prod.snd = (s[rmIdx r x]?).map Prod.snd := fun x => by
    rw [← List.getElem?_map, map_snd_jn s r hr, List.getElem?_map, getElem?_rmAt s (by omega)]
  have e1 : (s[r]?).map Prod.snd = some (d (s[r + 1]'hr).2) := by
    rw [List.getElem?_eq_getElem (by omega)]; simp [hlet]
  have e2 : (s[r + 1]?).map Prod.snd = some (d (s[r]'(by omega)).2) := by
    rw [List.getElem?_eq_getElem hr]; simp [hlet, hd _]
  have hsym : ∀ x y, Same s x y →
      (s[y]?).map Prod.snd = ((s[x]?).map Prod.snd).map d := fun x y hxy => by
    rw [h.symm_of_involutive hd hxy, Option.map_map]
  intro i j hij _
  rw [same_jn_iff hr] at hij
  obtain ⟨-, -, -, hij⟩ := hij
  rw [L, ← Option.map_map, L]
  rcases hij with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hsym _ _ h1
  · rw [hsym _ _ h2.symm, hsym _ _ h1.symm, e1, e2]; simp [hd _, hlet]
  · rw [hsym _ _ h2.symm, hsym _ _ h1.symm, e1, e2]; simp [hd _, hlet]

theorem ilv_iff_of_iso {s s' : List (ℕ × α)} (h : Iso s s') (q : ℕ) : Ilv s q ↔ Ilv s' q := by
  simp only [Ilv, Cr4, h.2]

end StringDiagrams.Chord

noncomputable section

namespace OddMath.SKM

open StringDiagrams Presentation
open StringDiagrams.Chord (Move TMove TState tStep tRun TFits TInv idD idAt Same Valid Lettered
  Iso insAt swapAt rmAt rmIdx tau jn Ilv Ilv2 Btw cr CrossOnce CritInv tCrit)

universe u

variable {I : Type u}

/-! ## Strictly reduced matchings -/

/-- The critical points (cups and caps) of an `(a, b)`-matching, each recorded by the id of its
strand at the end (`Chord.tCrit`); the bent lower endpoints `a` are not critical points. -/
def critPts₂ (a : List (Letter I)) (R : List (TMove (Letter I))) : List ℕ :=
  tCrit flipL a.length (tStart a) [] R

/-- **Reduced matchings in the sense of [BE2] §8**: no strand crosses itself, two strands cross
at most once (`Reduced₂`), and every strand has at most one critical point. -/
def StrictReduced₂ (a : List (Letter I)) (R : List (TMove (Letter I))) : Prop :=
  Reduced₂ a R ∧ (critPts₂ a R).Nodup

/-! ## Bent pairings realized by strictly reduced matchings -/

/-- A word is sorted if no upward letter follows a downward one. -/
def LSorted (w : List (Letter I)) : Prop :=
  ∀ i j : ℕ, i < j → ∀ x y : Letter I, w[i]? = some x → w[j]? = some y → x.1 = false → y.1 = false

theorem lSorted_dualW {a : List (Letter I)} (h : LSorted a) : LSorted (dualW a) := by
  intro i j hij x y hx hy hx1
  have hjl : j < a.length := by
    by_contra c; rw [List.getElem?_eq_none (by simp [dualW]; omega)] at hy; cases hy
  simp only [dualW] at hx hy
  rw [List.getElem?_reverse (by simp; omega)] at hx hy
  simp only [List.length_map, List.getElem?_map] at hx hy
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.1 hy
  have hx1' : x'.1 = true := by simpa [flipL] using hx1
  simp only [flipL]
  cases c : y'.1
  · have := h _ _ (show a.length - 1 - j < a.length - 1 - i by omega) y' x' hy' hx' c
    rw [hx1'] at this; cases this
  · rfl

section BentPairings

variable (a : List (Letter I))

/-- A pairing whose first `a.length` positions carry the letters `a*` (the bent lower endpoints). -/
structure BentPairing (s : List (ℕ × Letter I)) : Prop where
  valid : Valid s
  lettered : Lettered flipL s
  pre : ∀ i < a.length, (s[i]?).map Prod.snd = (dualW a)[i]?
  len : a.length ≤ s.length

/-- The pairing `s` joins two bent lower endpoints (an arc with both ends on the bottom edge). -/
def BotArc (s : List (ℕ × Letter I)) : Prop :=
  ∃ i j, i < a.length ∧ j < a.length ∧ Same s i j

/-- The pairing `s` joins two upper endpoints (an arc with both ends on the top edge). -/
def TopArc (s : List (ℕ × Letter I)) : Prop :=
  ∃ r t, a.length ≤ r ∧ a.length ≤ t ∧ Same s r t

/-- The letters right of the bent lower endpoints are sorted (`LSorted`). -/
def TopSorted (s : List (ℕ × Letter I)) : Prop := LSorted ((s.map Prod.snd).drop a.length)

/-- The shape of a matching `R` realizing `s`: if `s` has an arc on the bottom edge, then `R`
passes through a height with at least two strands fewer than `a`; if `s` has no arc on either
edge, then `R` consists of crossings only, and if moreover the letters of `a* b` are sorted
(upward before downward letters in `a*` and in `b`), then so are those at every height. -/
def MatchShape (s : List (ℕ × Letter I)) (R : List (TMove (Letter I))) : Prop :=
  (BotArc a s → ∃ R₀ R₁, R = R₀ ++ R₁ ∧
    (tRun flipL a.length (tStart a) R₀).st.length + 2 ≤ 2 * a.length) ∧
  (¬ BotArc a s → ¬ TopArc a s → (∀ m ∈ R, ∃ p, m = .mv (.cross p)) ∧
    (LSorted (dualW a) → TopSorted a s → ∀ R₀ R₁, R = R₀ ++ R₁ →
      TopSorted a (tRun flipL a.length (tStart a) R₀).st))

/-- The pairing `s` is realized from the bent lower endpoints by a reduced matching (`CrossOnce`)
satisfying the invariant of the critical points (`CritInv`), of the shape `MatchShape`. -/
def Realized (s : List (ℕ × Letter I)) : Prop :=
  ∃ R, TFits flipL a.length (tStart a) R ∧ Iso (tRun flipL a.length (tStart a) R).st s ∧
    CrossOnce (tRun flipL a.length (tStart a) R) ∧
    CritInv a.length (tRun flipL a.length (tStart a) R) (tCrit flipL a.length (tStart a) [] R) ∧
    MatchShape a s R

/-- No cup and no crossing can be peeled off the top of `s`. -/
def NoTopMove (s : List (ℕ × Letter I)) : Prop :=
  (∀ r, a.length ≤ r → ¬ Same s r (r + 1)) ∧ ∀ q, a.length ≤ q → ¬ Ilv s q

/-- `s` and `s₀` have the same arcs among the first `a.length` positions. -/
def SameBottomArcs (s s₀ : List (ℕ × Letter I)) : Prop :=
  ∀ i j, i < a.length → j < a.length → (Same s i j ↔ Same s₀ i j)

variable {a}

theorem tInv_tStart (a : List (Letter I)) : TInv (tStart a) := by
  obtain ⟨hf₀, hn₀, -, -⟩ := cupMoves_spec (dualW a)
  exact Chord.tInv_start hf₀ hn₀

/-- Arcs on the bottom edge are unchanged by a relabelling of positions fixing the bottom edge. -/
theorem botArc_iff_of_fix {s s' : List (ℕ × Letter I)} (f : ℕ → ℕ) (hf : ∀ i < a.length, f i = i)
    (h : ∀ i j, Same s' i j ↔ Same s (f i) (f j)) : BotArc a s' ↔ BotArc a s := by
  constructor
  · rintro ⟨i, j, hi, hj, hS⟩
    exact ⟨i, j, hi, hj, by rw [← hf i hi, ← hf j hj]; exact (h i j).1 hS⟩
  · rintro ⟨i, j, hi, hj, hS⟩
    exact ⟨i, j, hi, hj, (h i j).2 (by rw [hf i hi, hf j hj]; exact hS)⟩

/-- No arc on the top edge appears under a relabelling of positions preserving the top edge. -/
theorem not_topArc_of_map {s s' : List (ℕ × Letter I)} (f : ℕ → ℕ)
    (hf : ∀ i, a.length ≤ i → a.length ≤ f i) (h : ∀ i j, Same s' i j → Same s (f i) (f j))
    (ht : ¬ TopArc a s) : ¬ TopArc a s' := by
  rintro ⟨r, t, hr, ht', hS⟩
  exact ht ⟨f r, f t, hf r hr, hf t ht', h r t hS⟩

theorem TopSorted.of_iso {s s' : List (ℕ × Letter I)} (h : TopSorted a s') (e : Iso s s') :
    TopSorted a s := by
  unfold TopSorted; rw [e.1]; exact h

theorem MatchShape.of_iso {s s' : List (ℕ × Letter I)} {R : List (TMove (Letter I))} (h : MatchShape a s R)
    (e : Iso s s') : MatchShape a s' R := by
  have hb : BotArc a s' ↔ BotArc a s := botArc_iff_of_fix id (fun _ _ => rfl) fun i j => (e.2 i j).symm
  refine ⟨fun h' => h.1 (hb.1 h'), fun h1 h2 => ?_⟩
  obtain ⟨h3, h4⟩ := h.2 (fun h' => h1 (hb.2 h'))
    (not_topArc_of_map id (fun _ h => h) (fun i j hS => (e.2 i j).1 hS) h2)
  exact ⟨h3, fun hd ht => h4 hd (ht.of_iso e)⟩

/-- In a pairing without arcs on the top edge whose bent lower endpoints are sorted, two adjacent
upper endpoints carrying an upward and then a downward letter do not interleave. -/
theorem not_ilv_up_dn {s : List (ℕ × Letter I)} (hs : BentPairing a s) {q : ℕ} (hqn : a.length ≤ q)
    (h2 : ¬ TopArc a s) (hd : LSorted (dualW a)) {x y : Letter I}
    (hx : (s[q]?).map Prod.snd = some x) (hy : (s[q + 1]?).map Prod.snd = some y)
    (hx1 : x.1 = true) (hy1 : y.1 = false) : ¬ Ilv s q := by
  have hqL : q + 1 < s.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hy; cases hy
  obtain ⟨u, hu⟩ := hs.valid.exists (show q < s.length by omega)
  obtain ⟨w, hw⟩ := hs.valid.exists hqL
  have hua : u < a.length := by
    by_contra h; exact h2 ⟨q, u, hqn, by omega, hu⟩
  have hwa : w < a.length := by
    by_contra h; exact h2 ⟨q + 1, w, by omega, by omega, hw⟩
  have hlet : ∀ {p v : ℕ} {z : Letter I}, Same s v p → v < p → v < a.length →
      (s[p]?).map Prod.snd = some z → (dualW a)[v]? = some (flipL z) := by
    intro p v z hS hvp hva hz
    have hl := hs.lettered v p hS hvp
    have hvL : v < s.length := hS.lt_left
    rw [hz, List.getElem?_eq_getElem hvL] at hl
    rw [← hs.pre v hva, List.getElem?_eq_getElem hvL]
    simp only [Option.map_some, Option.some_inj, Function.comp_apply] at hl ⊢
    rw [hl, flipL_flipL]
  have hu' := hlet hu.symm (by omega) hua hx
  have hw' := hlet hw.symm (by omega) hwa hy
  have hwu : w < u := by
    rcases lt_trichotomy w u with h | h | h
    · exact h
    · subst h; have := hs.valid.unique hu.symm hw.symm; omega
    · have := hd u w h _ _ hu' hw' (by simp [flipL, hx1]); simp [flipL, hy1] at this
  rw [Chord.ilv_iff hs.valid hu hw]
  omega

theorem getElem?_drop_map_swapAt {s : List (ℕ × Letter I)} {q : ℕ}
    (hql : q + 1 < s.length) (i : ℕ) :
    (((swapAt s q).map Prod.snd).drop a.length)[i]? = (s[tau q (a.length + i)]?).map Prod.snd := by
  rw [List.getElem?_drop, List.getElem?_map, Chord.getElem?_swapAt s hql]

/-- Peeling a crossing keeps the upper letters sorted. -/
theorem TopSorted.swapAt {s : List (ℕ × Letter I)} (hs : BentPairing a s) {q : ℕ} (hq : Ilv s q)
    (hqn : a.length ≤ q) (h2 : ¬ TopArc a s) (hd : LSorted (dualW a)) (ht : TopSorted a s) :
    TopSorted a (swapAt s q) := by
  have hql := hq.lt
  unfold TopSorted LSorted
  intro i j hij x y hx hy hx1
  rw [getElem?_drop_map_swapAt hql] at hx hy
  by_cases e : a.length + i = q ∧ a.length + j = q + 1
  · rw [e.1, show tau q q = q + 1 by simp [tau]] at hx
    rw [e.2, show tau q (q + 1) = q by simp [tau]] at hy
    by_contra hy1
    exact not_ilv_up_dn hs hqn h2 hd hy hx (by simpa using hy1) hx1 hq
  · have hlt : tau q (a.length + i) < tau q (a.length + j) :=
      (Chord.tau_lt_iff q e (by omega)).2 (by omega)
    have hge : a.length ≤ tau q (a.length + i) := by unfold tau; split_ifs <;> omega
    refine ht (tau q (a.length + i) - a.length) (tau q (a.length + j) - a.length) (by omega) x y ?_ ?_ hx1
    · rw [List.getElem?_drop, List.getElem?_map, Nat.add_sub_cancel' hge]; exact hx
    · rw [List.getElem?_drop, List.getElem?_map, Nat.add_sub_cancel' (by omega)]; exact hy

theorem Realized.of_iso {s s' : List (ℕ × Letter I)} (h : Realized a s) (e : Iso s s') : Realized a s' := by
  obtain ⟨R, h1, h2, h3, h4, h5⟩ := h
  exact ⟨R, h1, h2.trans e, h3, h4, h5.of_iso e⟩

/-- **Peeling a cup** off the top. -/
theorem realized_cup {s : List (ℕ × Letter I)} (hs : BentPairing a s) {r : ℕ} (hr : Same s r (r + 1))
    (hrn : a.length ≤ r) (h : Realized a (rmAt s r)) : Realized a s := by
  obtain ⟨R, hfit, hiso, hR, hC, hsh⟩ := h
  set T := tRun flipL a.length (tStart a) R
  have hI := (tInv_tStart a).run hfit
  have hl2 : r + 2 ≤ s.length := hr.lt_right
  have hlen : T.st.length = s.length - 2 := by rw [hiso.length_eq, Chord.length_rmAt s hl2]
  have hg : a.length + (r - a.length) ≤ T.st.length := by omega
  set m : TMove (Letter I) := .mv (.cup (r - a.length) (s[r]'(by omega)).2)
  refine ⟨R ++ [m], (Chord.tFits_snoc _ m _ R).2 ⟨hfit, hg⟩, ?_, ?_, ?_, ?_⟩
  · rw [Chord.tRun_snoc']
    show Iso (insAt T.st (a.length + (r - a.length)) _ _) s
    rw [show a.length + (r - a.length) = r by omega]
    have e1 := Chord.insAt_rmAt s (show r + 1 < s.length by omega)
    have eid : (s[r + 1]'(by omega)).1 = (s[r]'(by omega)).1 := by
      have := hr.2.2
      simp only [idAt, List.getElem?_eq_getElem (show r < s.length by omega),
        List.getElem?_eq_getElem (show r + 1 < s.length by omega)] at this
      simpa using this.symm
    have elt : (s[r + 1]'(by omega)).2 = flipL (s[r]'(by omega)).2 := by
      have := hs.lettered r (r + 1) hr (by omega)
      simp only [List.getElem?_eq_getElem (show r < s.length by omega),
        List.getElem?_eq_getElem (show r + 1 < s.length by omega)] at this
      simpa using this
    have e2 : s[r + 1]'(by omega) = ((s[r]'(by omega)).1, flipL (s[r]'(by omega)).2) :=
      Prod.ext eid elt
    conv_rhs => rw [← e1, e2]
    exact hiso.insAt (by omega) (fun x hx => (hI.fresh x hx).ne)
      (fun x hx => Chord.ne_id_of_mem_rmAt hs.valid hr hx) _ _
  · rw [Chord.tRun_snoc']; exact hR
  · rw [Chord.tRun_snoc', Chord.tCrit_snoc]; exact Chord.critInv_cup hI hC hg
  · refine ⟨fun hb => ?_, fun _ ht => absurd ⟨r, r + 1, hrn, by omega, hr⟩ ht⟩
    have hb' : BotArc a (rmAt s r) := (botArc_iff_of_fix (rmIdx r)
      (fun i hi => by unfold rmIdx; split_ifs <;> omega)
      fun i j => Chord.same_rmAt hl2).2 hb
    obtain ⟨R₀, R₁, e, hl⟩ := hsh.1 hb'
    exact ⟨R₀, R₁ ++ [m], by rw [e, List.append_assoc], hl⟩

/-- **Peeling a crossing** of two interleaving strands off the top. -/
theorem realized_cross {s : List (ℕ × Letter I)} (hs : BentPairing a s) {q : ℕ} (hq : Ilv s q)
    (hqn : a.length ≤ q) (h : Realized a (swapAt s q)) : Realized a s := by
  obtain ⟨R, hfit, hiso, hR, hC, hsh⟩ := h
  set T := tRun flipL a.length (tStart a) R
  have hI := (tInv_tStart a).run hfit
  have hql := hq.lt
  have hlen : T.st.length = s.length := by rw [hiso.length_eq, Chord.length_swapAt]
  have hp : a.length + (q - a.length) + 1 < T.st.length := by omega
  have hns := hq.not_same hs.valid
  set m : TMove (Letter I) := .mv (.cross (q - a.length))
  have e : a.length + (q - a.length) = q := by omega
  have hfin : Iso (tRun flipL a.length (tStart a) (R ++ [m])).st s := by
    rw [Chord.tRun_snoc']
    show Iso (swapAt T.st (a.length + (q - a.length))) s
    rw [e]
    have := hiso.swapAt q
    rwa [Chord.swapAt_swapAt] at this
  refine ⟨R ++ [m], (Chord.tFits_snoc _ m _ R).2 ⟨hfit, hp⟩, hfin, ?_, ?_, ?_⟩
  · rw [Chord.tRun_snoc']
    have ha := Chord.idAt_eq_idD (s := T.st) (i := a.length + (q - a.length)) (by omega)
    have hb := Chord.idAt_eq_idD (s := T.st) (i := a.length + (q - a.length) + 1) hp
    rw [e] at ha hb
    have hne : idD T.st q ≠ idD T.st (q + 1) := by
      intro h'
      have hS : Same T.st q (q + 1) := ⟨by omega, by rw [ha]; simp, by rw [ha, hb, h']⟩
      rw [hiso.2, Chord.same_swapAt (by simpa using hql)] at hS
      exact hns (by simpa [Chord.tau] using hS.symm)
    refine Chord.crossOnce_cross hI hR (by rw [e]; exact hne) (by
      rw [e]; intro hil
      rw [Chord.ilv2_iff_ilv hI.valid ha hb, Chord.ilv_iff_of_iso hiso,
        Chord.ilv_swapAt_iff hs.valid hql hns] at hil
      exact hil hq)
  · rw [Chord.tRun_snoc', Chord.tCrit_snoc]; exact Chord.critInv_cross hC hp
  · have hS : ∀ i j, Same (swapAt s q) i j ↔ Same s (tau q i) (tau q j) :=
      fun i j => Chord.same_swapAt hql
    have hb := botArc_iff_of_fix (a := a) (tau q) (fun i hi => by unfold tau; split_ifs <;> omega) hS
    refine ⟨fun h' => ?_, fun h1 h2 => ?_⟩
    · obtain ⟨R₀, R₁, e', hl⟩ := hsh.1 (hb.2 h')
      exact ⟨R₀, R₁ ++ [m], by rw [e', List.append_assoc], hl⟩
    · obtain ⟨h3, h4⟩ := hsh.2 (fun h' => h1 (hb.1 h'))
        (not_topArc_of_map (a := a) (tau q) (fun i hi => by unfold tau; split_ifs <;> omega)
          (fun i j h' => (hS i j).1 h') h2)
      refine ⟨fun m' hm' => ?_, fun hd ht R₀ R₁ e' => ?_⟩
      · rcases List.mem_append.1 hm' with hm' | hm'
        · exact h3 m' hm'
        · rw [List.mem_singleton.1 hm']; exact ⟨_, rfl⟩
      · rcases List.eq_nil_or_concat R₁ with rfl | ⟨R₁', m', rfl⟩
        · rw [List.append_nil] at e'
          rw [← e']; exact ht.of_iso hfin
        · rw [List.concat_eq_append, ← List.append_assoc] at e'
          exact h4 hd (ht.swapAt hs hq hqn h2 hd) R₀ R₁' (List.append_inj_left' e' rfl)

/-- **Peeling cups and crossings** off the top until neither applies. -/
theorem realized_of_noTopMove (s₀ : List (ℕ × Letter I))
    (H : ∀ s, BentPairing a s → NoTopMove a s → SameBottomArcs a s s₀ → Realized a s) :
    ∀ N s, s.length + cr s < N → BentPairing a s → SameBottomArcs a s s₀ → Realized a s := by
  intro N
  induction N with
  | zero => intro s h; omega
  | succ N ih =>
    intro s hN hs hQ
    by_cases h1 : ∃ r, a.length ≤ r ∧ Same s r (r + 1)
    · obtain ⟨r, hrn, hr⟩ := h1
      have hl2 : r + 2 ≤ s.length := hr.lt_right
      have hpre : ∀ i < a.length, rmIdx r i = i := fun i hi => by
        unfold rmIdx; split_ifs <;> omega
      refine realized_cup hs hr hrn (ih _ ?_ ⟨hs.valid.rmAt hr, hs.lettered.rmAt hl2, fun i hi => ?_,
        ?_⟩ fun i j hi hj => ?_)
      · rw [Chord.length_rmAt s hl2]; have := Chord.cr_rmAt_le hl2; omega
      · rw [Chord.getElem?_rmAt s hl2, hpre i hi]; exact hs.pre i hi
      · rw [Chord.length_rmAt s hl2]; omega
      · rw [Chord.same_rmAt hl2, hpre i hi, hpre j hj]; exact hQ i j hi hj
    by_cases h2 : ∃ q, a.length ≤ q ∧ Ilv s q
    · obtain ⟨q, hqn, hq⟩ := h2
      have hql := hq.lt
      have hpre : ∀ i < a.length, tau q i = i := fun i hi => by
        unfold tau; split_ifs <;> omega
      refine realized_cross hs hq hqn (ih _ ?_ ⟨hs.valid.swapAt hql,
        hs.lettered.swapAt hql (hq.not_same hs.valid), fun i hi => ?_, ?_⟩ fun i j hi hj => ?_)
      · rw [Chord.length_swapAt]; have := Chord.cr_swapAt_lt hs.valid hq; omega
      · rw [Chord.getElem?_swapAt s hql, hpre i hi]; exact hs.pre i hi
      · rw [Chord.length_swapAt]; exact hs.len
      · rw [Chord.same_swapAt hql, hpre i hi, hpre j hj]; exact hQ i j hi hj
    exact H s hs ⟨fun r hr h => h1 ⟨r, hr, h⟩, fun q hq h => h2 ⟨q, hq, h⟩⟩ hQ

/-! ## Terminal states -/

/-- In a terminal state, every strand on the right of the bent lower endpoints ends among them. -/
theorem NoTopMove.lt {s : List (ℕ × Letter I)} (hs : BentPairing a s) (ht : NoTopMove a s) {x w : ℕ}
    (hx : a.length ≤ x) (h : Same s x w) : w < a.length := by
  classical
  by_contra hw
  rw [not_lt] at hw
  have key : ∀ lo hi, a.length ≤ lo → lo < hi → Same s lo hi → False := by
    intro lo hi hlo hlh hS
    have hex : ∃ c, lo < c ∧ Chord.Cls s c := ⟨hi, hlh, lo, hlh, hS.symm⟩
    obtain ⟨hc1, hc2⟩ := Nat.find_spec hex
    have ho : Chord.Opn s (Nat.find hex - 1) := by
      by_cases e : Nat.find hex - 1 = lo
      · rw [e]; exact ⟨hi, hlh, hS⟩
      · obtain ⟨j, -, hj⟩ := hc2
        obtain ⟨w', hw'⟩ := hs.valid.exists (show Nat.find hex - 1 < s.length by
          have := hj.lt_left; omega)
        refine ⟨w', ?_, hw'⟩
        by_contra hlt
        have hlt' : w' < Nat.find hex - 1 := lt_of_le_of_ne (not_lt.1 hlt) hw'.ne.symm
        exact Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
          ⟨by omega, w', hlt', hw'⟩
    have hc' : Chord.Cls s (Nat.find hex - 1 + 1) := by
      rw [Nat.sub_add_cancel (by omega)]; exact hc2
    exact ht.2 _ (by omega) (Chord.ilv_of_opn_cls hs.valid (ht.1 _ (by omega)) ho hc')
  rcases lt_or_gt_of_ne h.ne with hl | hl
  · exact key x w hx hl h
  · exact key w x hw hl h.symm

/-- In a terminal state, the strands on the right are bent lower endpoints in nested order. -/
theorem NoTopMove.dec {s : List (ℕ × Letter I)} (hs : BentPairing a s) (ht : NoTopMove a s) {x wx : ℕ}
    (hx : a.length ≤ x) (h1 : Same s x wx) :
    ∀ {y wy : ℕ}, x < y → Same s y wy → wy < wx := by
  intro y
  induction y with
  | zero => intro _ h; omega
  | succ y ih =>
    intro wy hxy h2
    obtain ⟨w', hw'⟩ := hs.valid.exists (show y < s.length by have := h2.lt_left; omega)
    have hadj : wy < w' := by
      have h3 := ht.2 y (by omega)
      rw [Chord.ilv_iff hs.valid hw' h2] at h3
      have := NoTopMove.lt hs ht (by omega) hw'
      have := NoTopMove.lt hs ht (by omega) h2
      have hne : w' ≠ wy := fun e => by
        subst e; have := hs.valid.unique hw'.symm h2.symm; omega
      omega
    rcases Nat.lt_or_ge x y with hxy' | hxy'
    · exact hadj.trans (ih hxy' hw')
    · have : x = y := by omega
      subst this; rw [hs.valid.unique h1 hw']; exact hadj

/-- In a terminal state without arcs among the bent lower endpoints, the strand at `n + j` ends at
`n - 1 - j`. -/
theorem noTopMove_mirror {s : List (ℕ × Letter I)} (hs : BentPairing a s) (ht : NoTopMove a s)
    (hnq : ∀ i j, i < a.length → j < a.length → ¬ Same s i j) :
    ∀ j, a.length + j < s.length → j < a.length ∧ Same s (a.length + j) (a.length - 1 - j) := by
  set n := a.length
  have hub : ∀ j w, n + j < s.length → Same s (n + j) w → w + j < n := by
    intro j
    induction j with
    | zero => intro w _ h; have := NoTopMove.lt hs ht (by omega) h; omega
    | succ j ih =>
      intro w hj h
      obtain ⟨w', hw'⟩ := hs.valid.exists (show n + j < s.length by omega)
      have := ih w' (by omega) hw'
      have := NoTopMove.dec hs ht (by omega) hw' (show n + j < n + (j + 1) by omega) h
      omega
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    obtain ⟨w, hw⟩ := hs.valid.exists hj
    have hwj := hub j w hj hw
    refine ⟨by omega, ?_⟩
    obtain ⟨p, hp⟩ := hs.valid.exists (show n - 1 - j < s.length by omega)
    have hpn : n ≤ p := by
      by_contra h; exact hnq _ _ (by omega) (by omega) hp
    have hp' : Same s (n + (p - n)) (n - 1 - j) := by
      rw [show n + (p - n) = p by omega]; exact hp.symm
    rcases lt_trichotomy (p - n) j with hlt | heq | hgt
    · have := hs.valid.unique hp' (ih _ hlt (by have := hp.lt_right; omega)).2; omega
    · rw [heq] at hp'; exact hp'
    · have := NoTopMove.dec hs ht (by omega) hw (show n + j < n + (p - n) by omega) hp'; omega

theorem same_mirror {α : Type*} {s : List (ℕ × α)} (hv : Valid s) {n : ℕ} (hl : s.length = 2 * n)
    (h : ∀ i < n, Same s i (2 * n - 1 - i)) {i j : ℕ} :
    Same s i j ↔ i < 2 * n ∧ j = 2 * n - 1 - i := by
  constructor
  · intro hs
    have hi : i < 2 * n := hl ▸ hs.lt_left
    refine ⟨hi, ?_⟩
    rcases Nat.lt_or_ge i n with h' | h'
    · exact hv.unique hs (h i h')
    · have := h (2 * n - 1 - i) (by omega)
      rw [show 2 * n - 1 - (2 * n - 1 - i) = i by omega] at this
      exact hv.unique hs this.symm
  · rintro ⟨hi, rfl⟩
    rcases Nat.lt_or_ge i n with h' | h'
    · exact h i h'
    · have := h (2 * n - 1 - i) (by omega)
      rw [show 2 * n - 1 - (2 * n - 1 - i) = i by omega] at this
      exact this.symm

theorem tStart_mirror (a : List (Letter I)) :
    (tStart a).st.length = 2 * a.length ∧
      ∀ i < a.length, Same (tStart a).st i (2 * a.length - 1 - i) := by
  have hS₀ : (tStart a).st = cupLeft (dualW a) ++ (cupLeft (dualW a)).reverse.map flipSnd :=
    run_cupMoves (dualW a)
  have hQl : (cupLeft (dualW a)).length = a.length := by simp [dualW]
  refine ⟨by rw [hS₀]; simp [hQl]; omega, fun i hi => ⟨by omega, ?_, ?_⟩⟩
  · rw [Chord.idAt_ne_none_iff, hS₀]; simp [hQl]; omega
  · rw [hS₀]
    simp only [idAt, List.getElem?_append, hQl, List.getElem?_map, hi, ↓reduceIte,
      show ¬ (2 * a.length - 1 - i < a.length) by omega]
    rw [List.getElem?_reverse (by rw [hQl]; omega), hQl,
      show a.length - 1 - (2 * a.length - 1 - i - a.length) = i by omega]
    cases (cupLeft (dualW a))[i]? <;> rfl

/-- **The base case**: a terminal state without arcs among the bent lower endpoints is the state
of the nested cups. -/
theorem iso_tStart_of_noTopMove {s : List (ℕ × Letter I)} (hs : BentPairing a s) (ht : NoTopMove a s)
    (hnq : ∀ i j, i < a.length → j < a.length → ¬ Same s i j) : Iso (tStart a).st s := by
  have hm := noTopMove_mirror hs ht hnq
  have hlen : s.length = 2 * a.length := by
    have h1 : s.length ≤ 2 * a.length := by
      by_contra h; have := (hm (s.length - a.length - 1) (by omega)).1; omega
    have h2 : 2 * a.length ≤ s.length := by
      rcases Nat.eq_zero_or_pos a.length with h0 | h0
      · omega
      obtain ⟨p, hp⟩ := hs.valid.exists (show 0 < s.length by have := hs.len; omega)
      have hpn : a.length ≤ p := by by_contra h; exact hnq 0 p h0 (by omega) hp
      have := hm (p - a.length) (by have := hp.lt_right; omega)
      rw [show a.length + (p - a.length) = p by omega] at this
      have := hs.valid.unique hp.symm this.2
      have := hp.lt_right; omega
    omega
  have hms : ∀ i < a.length, Same s i (2 * a.length - 1 - i) := fun i hi => by
    have := (hm (a.length - 1 - i) (by omega)).2
    rw [show a.length - 1 - (a.length - 1 - i) = i by omega, show a.length + (a.length - 1 - i) = 2 * a.length - 1 - i by omega]
      at this
    exact this.symm
  obtain ⟨hl0, hm0⟩ := tStart_mirror a
  have hv0 := (tInv_tStart a).valid
  refine ⟨?_, fun i j => by rw [same_mirror hv0 hl0 hm0, same_mirror hs.valid hlen hms]⟩
  rw [tStart_letters]
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_map]
  rcases Nat.lt_or_ge i a.length with hi | hi
  · rw [hs.pre i hi, List.getElem?_append_left (by simp [length_dualW]; omega)]
  rcases Nat.lt_or_ge i (2 * a.length) with hi' | hi'
  · have hS : Same s (2 * a.length - 1 - i) i := by
      have := hms (2 * a.length - 1 - i) (by omega)
      rwa [show 2 * a.length - 1 - (2 * a.length - 1 - i) = i by omega] at this
    have hl := hs.lettered _ _ hS (by omega)
    rw [hl, List.getElem?_append_right (by simp [length_dualW]; omega), length_dualW,
      ← Option.map_map, hs.pre _ (by omega), dualW, List.getElem?_reverse (by simp; omega),
      List.getElem?_map, Option.map_map]
    simp only [List.length_map]
    rw [show a.length - 1 - (2 * a.length - 1 - i) = i - a.length by omega]
    cases a[i - a.length]? <;> simp
  · rw [List.getElem?_eq_none (by simp [length_dualW]; omega), List.getElem?_eq_none (by omega)]
    rfl

/-- In a terminal state with an arc `i, i'` on the bottom edge, the strands on the right end at
distinct bent lower endpoints other than `i, i'`; so there are at most `a.length - 2` of them. -/
theorem NoTopMove.length_le {s : List (ℕ × Letter I)} (hs : BentPairing a s) (ht : NoTopMove a s)
    {i i' : ℕ} (hi : i < a.length) (hi' : i' < a.length) (hS : Same s i i') :
    s.length + 2 ≤ 2 * a.length := by
  classical
  have hlen := hs.len
  let f : ℕ → ℕ := fun x => if h : x < s.length then Classical.choose (hs.valid.exists h) else 0
  have hf : ∀ x (h : x < s.length), Same s x (f x) := fun x h => by
    simp only [f, h, ↓reduceDIte]; exact Classical.choose_spec (hs.valid.exists h)
  have hmaps : ∀ x ∈ Finset.Ico a.length s.length,
      f x ∈ ((Finset.range a.length).erase i).erase i' := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    have h1 := hf x hx.2
    have hlt := NoTopMove.lt hs ht hx.1 h1
    simp only [Finset.mem_erase, Finset.mem_range]
    refine ⟨fun e => ?_, fun e => ?_, hlt⟩
    · rw [e] at h1; have := hs.valid.unique h1.symm hS.symm; omega
    · rw [e] at h1; have := hs.valid.unique h1.symm hS; omega
  have hinj : Set.InjOn f (Finset.Ico a.length s.length : Set ℕ) := by
    intro x hx y hy e
    simp only [Finset.coe_Ico, Set.mem_Ico] at hx hy
    have h1 := hf x hx.2
    have h2 := hf y hy.2
    rw [e] at h1
    exact hs.valid.unique h1.symm h2.symm
  have := Finset.card_le_card_of_injOn f hmaps hinj
  have hne : i ≠ i' := hS.ne
  rw [Nat.card_Ico, Finset.card_erase_of_mem (by simp [Finset.mem_erase]; omega),
    Finset.card_erase_of_mem (by simp; omega), Finset.card_range] at this
  omega

/-! ## Peeling a cap: splitting an arc among the bent lower endpoints -/

/-- **Peeling a cap** off a terminal state: the arc joining the bent lower endpoints `i < i'` (with
`i` leftmost among such arcs) is split into two bent strands, capped together at the position `r`
after the bent strands ending to the right of `i'`. No strand interleaves both legs of the cap. -/
theorem realized_cap {s : List (ℕ × Letter I)} (hs : BentPairing a s) (ht : NoTopMove a s) {i i' : ℕ}
    (hii : i < i') (hi' : i' < a.length) (hS : Same s i i')
    (hmin : ∀ u w, u < i → w < a.length → ¬ Same s u w)
    (H : ∀ s', BentPairing a s' → (∀ u w, u < a.length → w < a.length →
      (Same s' u w ↔ Same s u w ∧ u ≠ i ∧ u ≠ i')) → Realized a s') : Realized a s := by
  classical
  have hlen := hs.len
  have hiL : i' < s.length := hS.lt_right
  -- the position of the cap
  have hex : ∃ x, a.length ≤ x ∧ (x = s.length ∨ ∃ w, Same s x w ∧ w < i') :=
    ⟨s.length, hs.len, Or.inl rfl⟩
  obtain ⟨hrn, hr⟩ := Nat.find_spec hex
  have hrL : Nat.find hex ≤ s.length := Nat.find_min' hex ⟨hs.len, Or.inl rfl⟩
  have hlt : ∀ y w, a.length ≤ y → y < Nat.find hex → Same s y w → i' < w := by
    intro y w hy hyr hyw
    have h1 := Nat.find_min hex hyr
    have hne : w ≠ i' := fun e => by
      subst e; have := hs.valid.unique hyw.symm hS.symm; omega
    by_contra hc; exact h1 ⟨hy, Or.inr ⟨w, hyw, by omega⟩⟩
  have hge : ∀ y w, Nat.find hex ≤ y → Same s y w → w < i' := by
    intro y w hy hyw
    have hyL := hyw.lt_left
    rcases hr with hr | ⟨w0, hw0, hw0'⟩
    · omega
    · rcases eq_or_lt_of_le hy with e | e
      · rw [← e] at hyw; rw [hs.valid.unique hyw hw0]; exact hw0'
      · exact (NoTopMove.dec hs ht hrn hw0 e hyw).trans hw0'
  generalize Nat.find hex = r at hrn hrL hlt hge
  -- the split state
  have hA : idAt s i = some (idD s i) := Chord.idAt_eq_idD (by omega)
  have hA' : idAt s i' = some (idD s i) := by rw [← hS.2.2, hA]
  set idA := idD s i
  set z := (s.map Prod.fst).sum + 1
  have hz : ∀ e ∈ s, e.1 ≠ z := fun e he => by
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := Prod.fst) he); omega
  have hzA : idA ≠ z := by
    have := hz _ (List.getElem_mem (show i' < s.length by omega))
    simp only [idAt, List.getElem?_eq_getElem hiL, Option.map_some, Option.some_inj] at hA'
    rwa [hA'] at this
  set L1 := (s[i']'hiL).2
  set L0 := (s[i]'(by omega)).2
  have hlet : L1 = flipL L0 := by
    have := hs.lettered i i' hS hii
    simp only [List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem (show i < s.length by omega),
      Option.map_some, Option.some_inj, Function.comp_apply] at this
    exact this
  set s₁ := s.set i' (z, L1)
  have hs₁ : s₁.length = s.length := List.length_set ..
  set s' := insAt s₁ r (z, flipL L1) (idA, flipL L0)
  set t := insAt s r (z, flipL L1) (z, flipL L0)
  set π : Equiv.Perm ℕ := Equiv.swap i' (r + 1)
  have hπi' : π i' = r + 1 := Equiv.swap_apply_left _ _
  have hπr1 : π (r + 1) = i' := Equiv.swap_apply_right _ _
  have hπ : ∀ j, j ≠ i' → j ≠ r + 1 → π j = j := fun j h1 h2 => Equiv.swap_apply_of_ne_of_ne h1 h2
  have hget : ∀ j, s'[j]? = if j < r then (if j = i' then some (z, L1) else s[j]?) else
      if j = r then some (z, flipL L1) else if j = r + 1 then some (idA, flipL L0) else
      s[j - 2]? := by
    intro j
    rw [Chord.getElem?_insAt _ (by rw [hs₁]; exact hrL)]
    by_cases h : j < r
    · simp only [h, ↓reduceIte]
      by_cases h' : j = i'
      · subst h'; simp [s₁, hiL]
      · simp only [h', ↓reduceIte, s₁]; rw [List.getElem?_set_ne (Ne.symm h')]
    · simp only [h, ↓reduceIte]
      by_cases h1 : j = r
      · simp [h1]
      by_cases h2 : j = r + 1
      · simp [h2]
      simp only [h1, h2, ↓reduceIte, s₁]
      rw [List.getElem?_set_ne (by omega)]
  have hid : ∀ j, idAt s' j = idAt t (π j) := by
    intro j
    simp only [idAt]
    rw [hget, Chord.getElem?_insAt _ hrL]
    by_cases h1 : j = i'
    · subst h1; rw [hπi']; simp [show j < r by omega]
    by_cases h2 : j = r + 1
    · subst h2; rw [hπr1]; simp [show i' < r by omega, hA'.symm]; simp [idAt]
    rw [hπ j h1 h2]
    by_cases h3 : j < r
    · simp [h3, h1]
    · simp only [h3, ↓reduceIte, h2]
  have hvt : Valid t := hs.valid.insAt hrL hz _ _
  have hv' : Valid s' := Chord.valid_of_idAt_comp π hid hvt
  have hsame : ∀ u v, Same s' u v ↔ Same t (π u) (π v) := fun u v =>
    Chord.same_of_idAt_comp π hid
  have hSt := fun x y => Chord.same_insAt_iff (s := s) hrL hz (flipL L1) (flipL L0) (i := x) (j := y)
  have ha1 : Same s' r i' := by
    rw [hsame, hπ r (by omega) (by omega), hπi', hSt]; left; exact ⟨rfl, rfl⟩
  have ha2 : Same s' (r + 1) i := by
    rw [hsame, hπr1, hπ i (by omega) (by omega), hSt]
    right; right
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    simp only [show i' < r by omega, show i < r by omega, ↓reduceIte]
    exact hS.symm
  have hb : ∀ u v, u ≠ r → u ≠ r + 1 → u ≠ i' → v ≠ r → v ≠ r + 1 → v ≠ i' →
      (Same s' u v ↔ Same s (if u < r then u else u - 2) (if v < r then v else v - 2)) := by
    intro u v h1 h2 h3 h4 h5 h6
    rw [hsame, hπ u h3 h2, hπ v h6 h5, hSt]
    constructor
    · rintro (⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, -, -, h⟩)
      · exact absurd e h1
      · exact absurd e h2
      · exact h
    · intro h; right; right; exact ⟨h1, h2, h4, h5, h⟩
  have hcase : ∀ u v, Same s' u v → (u = r ∧ v = i') ∨ (u = i' ∧ v = r) ∨ (u = r + 1 ∧ v = i) ∨
      (u = i ∧ v = r + 1) ∨ (u ≠ r ∧ u ≠ r + 1 ∧ u ≠ i ∧ u ≠ i' ∧ v ≠ r ∧ v ≠ r + 1 ∧ v ≠ i ∧
        v ≠ i' ∧ Same s (if u < r then u else u - 2) (if v < r then v else v - 2)) := by
    intro u v huv
    by_cases h1 : u = r
    · subst h1; exact Or.inl ⟨rfl, hv'.unique huv ha1⟩
    by_cases h2 : u = i'
    · subst h2; exact Or.inr (Or.inl ⟨rfl, hv'.unique huv ha1.symm⟩)
    by_cases h3 : u = r + 1
    · subst h3; exact Or.inr (Or.inr (Or.inl ⟨rfl, hv'.unique huv ha2⟩))
    by_cases h4 : u = i
    · subst h4; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hv'.unique huv ha2.symm⟩)))
    have n1 : v ≠ r := fun e => h2 (hv'.unique huv.symm (e ▸ ha1))
    have n2 : v ≠ i' := fun e => h1 (hv'.unique huv.symm (e ▸ ha1.symm))
    have n3 : v ≠ r + 1 := fun e => h4 (hv'.unique huv.symm (e ▸ ha2))
    have n4 : v ≠ i := fun e => h3 (hv'.unique huv.symm (e ▸ ha2.symm))
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h3, h4, h2, n1, n3, n4, n2,
      (hb u v h1 h3 h2 n1 n3 n2).1 huv⟩)))
  have hsnd : ∀ j, j ≠ r → j ≠ r + 1 →
      (s'[j]?).map Prod.snd = (s[if j < r then j else j - 2]?).map Prod.snd := by
    intro j h1 h2
    rw [hget]
    by_cases h3 : j < r
    · simp only [h3, ↓reduceIte]
      by_cases h4 : j = i'
      · subst h4; simp [List.getElem?_eq_getElem hiL, L1]
      · simp [h4]
    · simp [h3, h1, h2]
  have hsr : (s'[r]?).map Prod.snd = some (flipL L1) := by rw [hget]; simp
  have hsr1 : (s'[r + 1]?).map Prod.snd = some (flipL L0) := by rw [hget]; simp
  -- the split state is a target with the arcs among the bent lower endpoints other than `i, i'`
  have hT' : BentPairing a s' := by
    refine ⟨hv', fun u v huv huv' => ?_, fun j hj => ?_, by
      rw [Chord.length_insAt _ (by rw [hs₁]; exact hrL), hs₁]; omega⟩
    · rcases hcase u v huv with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2, -, -, h5, h6, -, -, h⟩
      · omega
      · rw [h1, h2, hsr, ← Option.map_map, hsnd i' (by omega) (by omega)]
        simp only [show i' < r by omega, ↓reduceIte, List.getElem?_eq_getElem hiL]
        rfl
      · omega
      · rw [h1, h2, hsr1, ← Option.map_map, hsnd i (by omega) (by omega)]
        simp only [show i < r by omega, ↓reduceIte,
          List.getElem?_eq_getElem (show i < s.length by omega)]
        rfl
      · rw [hsnd v h5 h6, ← Option.map_map, hsnd u h1 h2, Option.map_map,
          hs.lettered _ _ h (by split_ifs <;> omega)]
    · rw [hsnd j (by omega) (by omega)]
      simp only [show j < r by omega, ↓reduceIte]
      exact hs.pre j hj
  have hQ' : ∀ u w, u < a.length → w < a.length → (Same s' u w ↔ Same s u w ∧ u ≠ i ∧ u ≠ i') := by
    intro u w hu hw
    constructor
    · intro h
      rcases hcase u w h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨-, -, h3, h4, -, -, -, -, h⟩
      all_goals first | omega | skip
      simp only [show u < r by omega, show w < r by omega, ↓reduceIte] at h
      exact ⟨h, h3, h4⟩
    · rintro ⟨h, h3, h4⟩
      have n1 : w ≠ i' := fun e => h3 (hs.valid.unique h.symm (e ▸ hS.symm))
      have n2 : w ≠ i := fun e => h4 (hs.valid.unique h.symm (e ▸ hS))
      rw [hb u w (by omega) (by omega) h4 (by omega) (by omega) n1]
      simp only [show u < r by omega, show w < r by omega, ↓reduceIte]
      exact h
  obtain ⟨R, hfit, hiso, hR, hC, -⟩ := H s' hT' hQ'
  -- the cap
  set T := tRun flipL a.length (tStart a) R
  have hI := (tInv_tStart a).run hfit
  have e : a.length + (r - a.length) = r := by omega
  have hST1 : Same T.st r i' := (hiso.2 _ _).2 ha1
  have hST2 : Same T.st (r + 1) i := (hiso.2 _ _).2 ha2
  have hr1 : r + 1 < T.st.length := hST2.lt_left
  have hx := Chord.idAt_eq_idD (s := T.st) (i := r) (by omega)
  have hy := Chord.idAt_eq_idD (s := T.st) (i := r + 1) hr1
  have hxy : idD T.st r ≠ idD T.st (r + 1) := by
    intro h
    have : Same s' r (r + 1) := (hiso.2 _ _).1 ⟨by omega, by rw [hx]; simp, by rw [hx, hy, h]⟩
    rcases hcase _ _ this with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hok : (TMove.cap (r - a.length) : TMove (Letter I)).Ok flipL a.length T.st := by
    rw [show (TMove.cap (r - a.length) : TMove (Letter I)).Ok flipL a.length T.st ↔
      ∃ A B, T.st[a.length + (r - a.length)]? = some A ∧
        T.st[a.length + (r - a.length) + 1]? = some B ∧ A.2 = flipL B.2 ∧ A.1 ≠ B.1 from Iff.rfl, e]
    refine ⟨T.st[r]'(by omega), T.st[r + 1]'hr1, List.getElem?_eq_getElem _,
      List.getElem?_eq_getElem _, ?_, ?_⟩
    · have h1 : (T.st[r]?).map Prod.snd = (s'[r]?).map Prod.snd := by
        rw [← List.getElem?_map, ← List.getElem?_map, hiso.1]
      have h2 : (T.st[r + 1]?).map Prod.snd = (s'[r + 1]?).map Prod.snd := by
        rw [← List.getElem?_map, ← List.getElem?_map, hiso.1]
      rw [hsr, List.getElem?_eq_getElem (by omega)] at h1
      rw [hsr1, List.getElem?_eq_getElem hr1] at h2
      simp only [Option.map_some, Option.some_inj] at h1 h2
      rw [h1, h2, hlet]
    · intro h
      apply hxy
      simp only [idD, idAt, List.getElem?_eq_getElem (show r < T.st.length by omega),
        List.getElem?_eq_getElem hr1, Option.map_some, Option.getD_some, h]
  have hjn : jn s' r = s.map (Chord.rl idA z) := by
    have e1 : s' = s₁.take r ++ [(z, flipL L1), (idA, flipL L0)] ++ s₁.drop r := by
      simp [s', insAt]
    have e2 : (s₁.take r).length = r := by simp [s₁]; omega
    have e3 := Chord.jn_mid (s₁.take r) (s₁.drop r) (z, flipL L1) (idA, flipL L0)
    rw [e2] at e3
    rw [e1, e3, List.take_append_drop]
    refine List.ext_getElem? fun j => ?_
    simp only [List.getElem?_map, s₁]
    by_cases h1 : j = i'
    · subst h1
      rw [List.getElem?_set_self hiL, List.getElem?_eq_getElem hiL]
      simp only [Option.map_some, Option.some_inj]
      simp only [idAt, List.getElem?_eq_getElem hiL, Option.map_some, Option.some_inj] at hA'
      rw [Chord.rl_of_ne (show (z, L1).1 ≠ idA from hzA.symm), Chord.rl_of_eq hA']
    · rw [List.getElem?_set_ne (Ne.symm h1)]
  have hfin : Iso (tRun flipL a.length (tStart a) (R ++ [.cap (r - a.length)])).st s := by
    rw [Chord.tRun_snoc']
    show Iso (jn T.st (a.length + (r - a.length))) s
    rw [e]
    refine (hiso.jn hr1).trans ?_
    rw [hjn]
    refine Chord.iso_map_of_injOn s (Chord.rlId idA z) fun x hx y hy h => ?_
    simp only [Chord.rlId] at h
    have := hz x hx; have := hz y hy
    split_ifs at h <;> omega
  refine ⟨R ++ [.cap (r - a.length)], (Chord.tFits_snoc _ _ _ R).2 ⟨hfit, hok⟩, hfin, ?_, ?_,
    fun _ => ⟨R ++ [.cap (r - a.length)], [], (List.append_nil _).symm, by
      rw [hfin.length_eq]; exact NoTopMove.length_le hs ht (by omega) hi' hS⟩,
    fun hb => absurd ⟨i, i', by omega, hi', hS⟩ hb⟩
  · rw [Chord.tRun_snoc']
    have hAx := Chord.arcAt_of_valid hI.valid hST1 hx
    have hAy := Chord.arcAt_of_valid hI.valid hST2 hy
    have hix : idAt T.st i' = some (idD T.st r) := hAx.id'
    have hiy : idAt T.st i = some (idD T.st (r + 1)) := hAy.id'
    refine Chord.crossOnce_cap hI hR (by
      rw [e, Chord.ilv2_iff_btw hAx hAy hxy]; simp only [Btw]; omega) (by
      rw [e]
      intro b hbx hby ⟨h1, h2⟩
      by_cases hex : ∃ u, idAt T.st u = some b
      · obtain ⟨u, hu⟩ := hex
        obtain ⟨v, hB⟩ := Chord.exists_arcAt hI.valid hu
        rw [Chord.ilv2_iff_btw hAx hB (Ne.symm hbx)] at h1
        rw [Chord.ilv2_iff_btw hAy hB (Ne.symm hby)] at h2
        have hv := hB.id'
        have ne : ∀ {p c}, idAt T.st p = some c → c ≠ b → ∀ q, idAt T.st q = some b → q ≠ p :=
          fun hp hc q hq e' => hc (Option.some.inj (by rw [← hp, ← e', hq]))
        have hu1 := ne hx (Ne.symm hbx) u hu; have hu2 := ne hy (Ne.symm hby) u hu
        have hu3 := ne hix (Ne.symm hbx) u hu; have hu4 := ne hiy (Ne.symm hby) u hu
        have hv1 := ne hx (Ne.symm hbx) v hv; have hv2 := ne hy (Ne.symm hby) v hv
        have hv3 := ne hix (Ne.symm hbx) v hv; have hv4 := ne hiy (Ne.symm hby) v hv
        have hS' := (hb u v hu1 hu2 hu3 hv1 hv2 hv3).1 ((hiso.2 _ _).1 hB.same)
        simp only [Btw] at h1 h2
        rcases Nat.lt_or_ge u a.length with hun | hun <;>
          rcases Nat.lt_or_ge v a.length with hvn | hvn
        · simp only [show u < r by omega, show v < r by omega, ↓reduceIte] at hS'
          rcases (show u < i ∨ v < i by omega) with h | h
          · exact hmin u v h hvn hS'
          · exact hmin v u h hun hS'.symm
        · simp only [show u < r by omega, ↓reduceIte] at hS'
          by_cases hvr : v < r
          · simp only [hvr, ↓reduceIte] at hS'
            have := hlt v u hvn hvr hS'.symm; omega
          · simp only [hvr, ↓reduceIte] at hS'
            have := hge (v - 2) u (by omega) hS'.symm; omega
        · simp only [show v < r by omega, ↓reduceIte] at hS'
          by_cases hur : u < r
          · simp only [hur, ↓reduceIte] at hS'
            have := hlt u v hun hur hS'; omega
          · simp only [hur, ↓reduceIte] at hS'
            have := hge (u - 2) v (by omega) hS'; omega
        · have := NoTopMove.lt hs ht (by split_ifs <;> omega) hS'
          split_ifs at this <;> omega
      · exact Chord.not_ilv2_of_absent' (fun u hu => hex ⟨u, hu⟩) h1)
  · rw [Chord.tRun_snoc', Chord.tCrit_snoc]
    exact Chord.critInv_cap hI hC (by rw [e]; exact hr1) (by rw [e]; exact hST1)
      (by rw [e]; exact hST2) hi' (by omega)

/-! ## Every pairing is realized -/

open scoped Classical in
/-- **Terminal states are realized**, by induction on the number of bent lower endpoints joined
among themselves. -/
theorem realized_noTopMove : ∀ m s, ((Finset.range a.length).filter
    fun i => ∃ j < a.length, Same s i j).card < m → BentPairing a s → NoTopMove a s → Realized a s := by
  intro m
  induction m with
  | zero => intro s h; omega
  | succ m ih =>
    intro s hm hs ht
    by_cases hQ : ∃ i, i < a.length ∧ ∃ j, j < a.length ∧ Same s i j
    · obtain ⟨hi, j, hj, hS⟩ := Nat.find_spec hQ
      have hmin : ∀ u w, u < Nat.find hQ → w < a.length → ¬ Same s u w :=
        fun u w hu hw h => Nat.find_min hQ hu ⟨by omega, w, hw, h⟩
      have hii : Nat.find hQ < j := by
        rcases lt_trichotomy (Nat.find hQ) j with h | h | h
        · exact h
        · exact absurd h hS.ne
        · exact absurd hS.symm (hmin j _ h hi)
      refine realized_cap hs ht hii hj hS hmin fun s' hT' hQ' =>
        realized_of_noTopMove s' (fun s₂ hT₂ ht₂ hq₂ => ih s₂ ?_ hT₂ ht₂) _ s' (Nat.lt_succ_self _) hT'
          fun _ _ _ _ => Iff.rfl
      have e : (Finset.range a.length).filter (fun i => ∃ j < a.length, Same s₂ i j) =
          (Finset.range a.length).filter (fun i => ∃ j < a.length, Same s' i j) := by
        refine Finset.filter_congr fun x hx => ?_
        rw [Finset.mem_range] at hx
        exact exists_congr fun w => and_congr_right fun hw => hq₂ x w hx hw
      have hlt : ((Finset.range a.length).filter fun i => ∃ j < a.length, Same s' i j).card <
          ((Finset.range a.length).filter fun i => ∃ j < a.length, Same s i j).card := by
        refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun x hx => ?_).2
          ⟨Nat.find hQ, ?_, ?_⟩)
        · simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
          obtain ⟨hx, w, hw, h⟩ := hx
          exact ⟨hx, w, hw, ((hQ' x w hx hw).1 h).1⟩
        · simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hi, j, hj, hS⟩
        · simp only [Finset.mem_filter, Finset.mem_range, not_and, not_exists]
          exact fun _ w hw h => ((hQ' _ w hi hw).1 h).2.1 rfl
      rw [e]; omega
    · refine ⟨[], trivial, iso_tStart_of_noTopMove hs ht fun i j hi hj h => hQ ⟨i, hi, j, hj, h⟩,
        ⟨List.nodup_nil, by simp [tRun, tStart]⟩, ⟨List.nodup_nil, by simp [tCrit],
          by simp [tCrit]⟩, fun ⟨i, j, hi, hj, h⟩ => absurd ⟨i, hi, j, hj, h⟩ hQ, fun _ _ => ⟨by simp,
          fun _ hts R₀ R₁ e => by
            obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.1 e.symm
            exact hts.of_iso (iso_tStart_of_noTopMove hs ht fun i j hi hj h => hQ ⟨i, hi, j, hj, h⟩)⟩⟩

/-- **Every bent pairing is realized.** -/
theorem realized_of_bentPairing {s : List (ℕ × Letter I)} (hs : BentPairing a s) : Realized a s :=
  realized_of_noTopMove s (fun s₂ h₁ h₂ _ => realized_noTopMove _ s₂ (Nat.lt_succ_self _) h₁ h₂) _ s
    (Nat.lt_succ_self _) hs fun _ _ _ _ => Iff.rfl

end BentPairings

/-- The letters along a matching. -/
theorem letters_tRun {k : ℕ} {u : List (Letter I)} (hu : u.length = k) :
    ∀ (R : List (TMove (Letter I))) (T : TState (Letter I)) (l : List (Letter I)),
      T.st.map Prod.snd = u ++ l → TFits flipL k T R →
        (tRun flipL k T R).st.map Prod.snd = u ++ R.foldl tLet l
  | [], _, _, h, _ => h
  | m :: R, T, l, h, ⟨hm, hR⟩ => by
    have hlen : T.st.length = k + l.length := by
      have := congrArg List.length h; simp at this; omega
    have h1 : (tStep flipL k T m).st.map Prod.snd = u ++ tLet l m := by
      rw [tStep_shift, (tStep_spec h ((ok_shift k T.st m).1 hm)).1, ← hu]
      refine ((tmLay_shift u fun mm e => ?_).2).symm
      subst e
      rcases mm with ⟨g, x⟩ | p
      · show g ≤ l.length; have : k + g ≤ T.st.length := hm; omega
      · show p + 1 < l.length; have : k + p + 1 < T.st.length := hm; omega
    exact letters_tRun hu R _ _ h1 hR

/-- **Every pairing of `a* b` is the pairing of a strictly reduced `(a, b)`-matching** ([BE2] §8):
no strand crosses itself, two strands cross at most once, and every strand has at most one
critical point. -/
theorem exists_strictReduced_matching {a b : List (Letter I)} {s : List (ℕ × Letter I)}
    (hv : Valid s) (hl : Lettered flipL s) (hs : s.map Prod.snd = dualW a ++ b) :
    ∃ R, IsMatching₂ a b R ∧ StrictReduced₂ a R ∧ Iso (pairing₂ a R) s := by
  have hT : BentPairing a s := ⟨hv, hl, fun i hi => by
    rw [← List.getElem?_map, hs, List.getElem?_append_left (by rw [length_dualW]; exact hi)], by
    have := congrArg List.length hs; simp [length_dualW] at this; omega⟩
  obtain ⟨R, hfit, hiso, hR, hC, -⟩ := realized_of_bentPairing hT
  have hlet := letters_tRun (length_dualW a) R (tStart a) a (tStart_letters a) hfit
  rw [hiso.1, hs] at hlet
  exact ⟨R, ⟨hfit, (List.append_cancel_left hlet).symm⟩, ⟨⟨hR.1, hR.2⟩, hC.nodup⟩, hiso⟩

/-- **The shape of the strictly reduced matching of a pairing**: in `exists_strictReduced_matching`
the matching may be chosen so that, if the pairing joins two bottom endpoints, the diagram passes
through a word with at least two letters fewer than `a` (so it factors through a shorter word),
and, if the pairing joins no two endpoints on the same edge, the matching consists of crossings
only. -/
theorem exists_strictReduced_matching_shape {a b : List (Letter I)} {s : List (ℕ × Letter I)}
    (hv : Valid s) (hl : Lettered flipL s) (hs : s.map Prod.snd = dualW a ++ b) :
    ∃ R, IsMatching₂ a b R ∧ StrictReduced₂ a R ∧ Iso (pairing₂ a R) s ∧
      (BotArc a s → ∃ R₀ R₁, R = R₀ ++ R₁ ∧ (R₀.foldl tLet a).length + 2 ≤ a.length) ∧
      (¬ BotArc a s → ¬ TopArc a s → (∀ m ∈ R, ∃ p, m = .mv (.cross p)) ∧
        (LSorted a → LSorted b → ∀ R₀ R₁, R = R₀ ++ R₁ → LSorted (R₀.foldl tLet a))) := by
  have hT : BentPairing a s := ⟨hv, hl, fun i hi => by
    rw [← List.getElem?_map, hs, List.getElem?_append_left (by rw [length_dualW]; exact hi)], by
    have := congrArg List.length hs; simp [length_dualW] at this; omega⟩
  obtain ⟨R, hfit, hiso, hR, hC, hsh⟩ := realized_of_bentPairing hT
  have hlet := letters_tRun (length_dualW a) R (tStart a) a (tStart_letters a) hfit
  rw [hiso.1, hs] at hlet
  have hpre : ∀ R₀ R₁, R = R₀ ++ R₁ →
      (tRun flipL a.length (tStart a) R₀).st.map Prod.snd = dualW a ++ R₀.foldl tLet a := by
    intro R₀ R₁ e
    rw [e] at hfit
    exact letters_tRun (length_dualW a) R₀ (tStart a) a (tStart_letters a)
      ((tFits_append_at _ _ _ _).1 hfit).1
  refine ⟨R, ⟨hfit, (List.append_cancel_left hlet).symm⟩, ⟨⟨hR.1, hR.2⟩, hC.nodup⟩, hiso,
    fun hb => ?_, fun h1 h2 => ?_⟩
  · obtain ⟨R₀, R₁, e, h⟩ := hsh.1 hb
    refine ⟨R₀, R₁, e, ?_⟩
    have := congrArg List.length (hpre R₀ R₁ e)
    simp only [List.length_map, List.length_append, length_dualW] at this
    omega
  · obtain ⟨h3, h4⟩ := hsh.2 h1 h2
    refine ⟨h3, fun ha hb R₀ R₁ e => ?_⟩
    have h5 := h4 (lSorted_dualW ha) (by
      unfold TopSorted; rw [hs, List.drop_left' (length_dualW a)]; exact hb) R₀ R₁ e
    unfold TopSorted at h5
    rwa [hpre R₀ R₁ e, List.drop_left' (length_dualW a)] at h5

/-! ## Every matching is equivalent to a strictly reduced one -/

/-- The pairing of a matching is lettered. -/
theorem lettered_tRun {k : ℕ} : ∀ (R : List (TMove (Letter I))) (T : TState (Letter I)),
    TInv T → Lettered flipL T.st → TFits flipL k T R → Lettered flipL (tRun flipL k T R).st
  | [], _, _, h, _ => h
  | m :: R, T, hI, h, ⟨hm, hR⟩ => by
    refine lettered_tRun R _ (hI.step hm) ?_ hR
    rcases m with (⟨g, x⟩ | p) | g
    · exact h.insAt flipL_involutive hm (fun e he => (hI.fresh e he).ne) x
    · exact h.swapAt_of_involutive flipL_involutive hm
    · obtain ⟨A, B, hA, hB, hAB, -⟩ := hm
      have hr : k + g + 1 < T.st.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at hB; cases hB
      refine Chord.Lettered.jn h flipL_involutive hr ?_
      rw [List.getElem?_eq_getElem (by omega)] at hA
      rw [List.getElem?_eq_getElem hr] at hB
      rw [Option.some_inj.1 hA, Option.some_inj.1 hB, hAB]

/-- **Every matching is equivalent to a strictly reduced one** (the remark of [BE2] §8 before
Theorem 8.1): equivalent matchings being those with the same pairing of the letters of `a* b`. -/
theorem exists_strictReduced_equiv {a b : List (Letter I)} {R' : List (TMove (Letter I))}
    (hR' : IsMatching₂ a b R') :
    ∃ R, IsMatching₂ a b R ∧ StrictReduced₂ a R ∧ Iso (pairing₂ a R) (pairing₂ a R') := by
  obtain ⟨hf₀, -, -, -⟩ := cupMoves_spec (dualW a)
  refine exists_strictReduced_matching ((tInv_tStart a).run hR'.1).valid
    (lettered_tRun R' _ (tInv_tStart a) (Chord.lettered_run flipL_involutive hf₀) hR'.1) ?_
  rw [pairing₂, letters_tRun (length_dualW a) R' _ a (tStart_letters a) hR'.1, hR'.2]

/-! ## Theorem 8.1 -/

section Theorem

universe v w

variable {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {cs : CScalars Sc}

variable (μ : X) (a b : List (Letter I)) (M : Set (List (TMove (Letter I))))
  (hM : ∀ R ∈ M, IsMatching₂ a b R ∧ StrictReduced₂ a R)
  (hrep : ∀ R', IsMatching₂ a b R' → StrictReduced₂ a R' →
    ∃ R ∈ M, Iso (pairing₂ a R) (pairing₂ a R'))
  (q : List (TMove (Letter I)) → ℕ → ℕ × ℕ)
  (hq : ∀ R ∈ M, ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q R j))
  (σ : List (TMove (Letter I)) → (ℕ → ℕ) → List (DTMove I))
  (hσ : ∀ R ∈ M, ∀ n, Decorates₂ a R (q R) n (σ R n))

include hM hrep hq hσ in
/-- **[BE2] Theorem 8.1.** Let `M` be a set of reduced `(a, b)`-matchings (`IsMatching₂ a b R`,
`StrictReduced₂ a R`: no strand crosses itself, two strands cross at most once, and every strand
has at most one critical point) containing a representative of every equivalence class of reduced
`(a, b)`-matchings, two matchings being equivalent when they define the same pairing of the letters
of `a* b` (`Iso (pairing₂ a R) (pairing₂ a R')`). For each `R ∈ M` let `q R j` be a distinguished
point on the strand with left endpoint `j` (`OnStrand₂`), and for counts `n` let `σ R n` be the
decorated matching with `n j` dots at `q R j` (`Decorates₂`). Then the 2-morphisms
`dLay a (σ R n) : E_a 1_λ → E_b 1_λ` generate `Hom(E_a 1_λ, E_b 1_λ)` as a right `SYM`-module,
`SYM` acting by `β_λ` in the rightmost region (`diagBubSpan`).

Matchings are encoded by generic layerings (sequences of cups, crossings and caps); every planar
matching has such layerings, and they differ by the super interchange law, i.e. by signs. The
remark of [BE2] §8 that every matching is equivalent to a reduced one is
`exists_strictReduced_equiv`; the proof uses that every pairing of `a* b` is the pairing of a
reduced matching (`exists_strictReduced_matching`). Compared with the printed statement, `M` need
not consist of pairwise inequivalent matchings, for each `R` and `n` any decorated matching with
the prescribed dots may be chosen (in particular with the dots at one height in any order), and
`wt(a) = wt(b)` is not assumed; each of these makes the statement more general. -/
theorem theorem_8_1 : diagBubSpan D Sc cs μ a b (decoratedFamily₂ a M σ) = ⊤ :=
  theorem_8_1_of_pairings μ a b M (fun R hR => ⟨(hM R hR).1, (hM R hR).2.1⟩)
    (fun s hv hl hs => by
      obtain ⟨R', hR', hred, hiso⟩ := exists_strictReduced_matching hv hl hs
      obtain ⟨R, hRM, hR⟩ := hrep R' hR' hred
      exact ⟨R, hRM, hR.trans hiso⟩) q hq σ hσ

end Theorem

end OddMath.SKM
