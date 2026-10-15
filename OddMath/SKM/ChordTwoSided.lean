/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChordJoin

/-!
# Two-sided matchings and their crossings

Combinatorics for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
§8 (matchings and reduced matchings before Theorem 8.1). An `(a, b)`-matching is encoded by a
generic layering: reading from the bottom, a sequence of cups, crossings and caps (`TMove`). As in
M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1, its
strands are followed in the bent picture: the lower endpoints `a` are bent up to the left by nested
cups (`cupMoves`), so that the state at each height (`TState.st`) lists the upper endpoints of the
bent strands `a*` followed by the strands crossing that height, with the id of the strand of each.
A cup creates a strand with a fresh id (`TState.nxt`), a crossing swaps two adjacent strands, and a
cap joins two adjacent strands (`Chord.jn`); the final state is the pairing of `a* b`.

Following [BE2] §8, the crossings are recorded as unordered pairs of strand ids (`TState.xs`;
ids are renamed when strands are joined), and the caps as the pairs of ids they join
(`TState.cps`). A matching is *reduced* if no strand crosses itself, two strands cross at most
once, and every strand has at most one critical point; the last condition says that every cap
joins two strands coming from the bottom (`OddMath.SKM.Reduced₂`).

## Main results

* `ilv2_iff_btw`: two arcs interleave when exactly one endpoint of one lies between the endpoints
  of the other.
* `ilv2_jn_of_ne`, `ilv2_jn_left`, `not_ilv2_jn_right`: interleaving after joining two strands.
* `TInv.step`: along a matching, two distinct strands interleave exactly when they have crossed
  an odd number of times.
* `length_xs_le_cr`: **a matching in which no strand crosses itself and two strands cross at most
  once has at most as many crossings as the crossing number of its pairing.**
-/

namespace StringDiagrams.Chord

variable {α : Type*} {s : List (ℕ × α)}

/-! ## Interleaving in terms of positions -/

/-- The position `c` lies strictly between `u` and `v`. -/
def Btw (u v c : ℕ) : Prop := (u < c ∧ c < v) ∨ (v < c ∧ c < u)

theorem btw_comm {u v c : ℕ} : Btw u v c ↔ Btw v u c := Or.comm

/-- The strand with id `a` is the arc joining the positions `u` and `v`. -/
structure ArcAt (s : List (ℕ × α)) (a u v : ℕ) : Prop where
  same : Same s u v
  id : idAt s u = some a
  pos : ∀ i, idAt s i = some a → i = u ∨ i = v

theorem idAt_of_same {u v a : ℕ} (huv : Same s u v) (hu : idAt s u = some a) :
    idAt s v = some a := by rw [← huv.2.2]; exact hu

theorem ArcAt.id' {a u v : ℕ} (h : ArcAt s a u v) : idAt s v = some a := idAt_of_same h.same h.id

theorem ArcAt.symm {a u v : ℕ} (h : ArcAt s a u v) : ArcAt s a v u :=
  ⟨h.same.symm, h.id', fun i hi => (h.pos i hi).symm⟩

theorem arcAt_of_valid (hv : Valid s) {u v a : ℕ} (huv : Same s u v) (hu : idAt s u = some a) :
    ArcAt s a u v := by
  refine ⟨huv, hu, fun i hi => ?_⟩
  by_cases h : i = u
  · exact Or.inl h
  · exact Or.inr (hv.unique huv ⟨Ne.symm h, by rw [hu]; simp, by rw [hu, hi]⟩).symm

/-- A strand of a pairing that occurs somewhere is an arc. -/
theorem exists_arcAt (hv : Valid s) {u a : ℕ} (hu : idAt s u = some a) :
    ∃ v, ArcAt s a u v := by
  have hl : u < s.length := idAt_ne_none_iff.1 (by rw [hu]; simp)
  obtain ⟨v, hv', -⟩ := hv u hl
  exact ⟨v, arcAt_of_valid hv hv' hu⟩

theorem ilv2_of_sorted {p q p' q' a b : ℕ} (hpq : p < q) (hpq' : p' < q') (h1 : Same s p q)
    (h2 : Same s p' q') (ha : idAt s p = some a) (hb : idAt s p' = some b)
    (hd : p ≠ p' ∧ p ≠ q' ∧ q ≠ p' ∧ q ≠ q') (h : Btw p q p' ↔ ¬ Btw p q q') : Ilv2 s a b := by
  rcases (show (p < p' ∧ p' < q ∧ q < q') ∨ (p' < p ∧ p < q' ∧ q' < q) by
      simp only [Btw] at h; omega) with h3 | h3
  · exact Or.inl ⟨p, p', q, q', ⟨h3.1, h3.2.1, h3.2.2, h1, h2⟩, ha, hb⟩
  · exact Or.inr ⟨p', p, q', q, ⟨h3.1, h3.2.1, h3.2.2, h2, h1⟩, hb, ha⟩

/-- **Two arcs interleave** exactly when one endpoint of the second lies between the endpoints of
the first, and the other does not. -/
theorem ilv2_iff_btw {u v u' v' a b : ℕ} (hA : ArcAt s a u v) (hB : ArcAt s b u' v')
    (hab : a ≠ b) : Ilv2 s a b ↔ (Btw u v u' ↔ ¬ Btw u v v') := by
  have hv₁ := hA.id'
  have hv₂ := hB.id'
  have hu := hA.id
  have hu' := hB.id
  have hne : ∀ {i j}, idAt s i = some a → idAt s j = some b → i ≠ j := fun hi hj e => hab
    (by rw [e, hj] at hi; exact (Option.some.inj hi).symm)
  have hd : u ≠ u' ∧ u ≠ v' ∧ v ≠ u' ∧ v ≠ v' :=
    ⟨hne hu hu', hne hu hv₂, hne hv₁ hu', hne hv₁ hv₂⟩
  have n1 := hA.same.ne
  have n2 := hB.same.ne
  constructor
  · rintro (⟨i, j, k, l, ⟨h1, h2, h3, h4, h5⟩, hi, hj⟩ | ⟨i, j, k, l, ⟨h1, h2, h3, h4, h5⟩, hi, hj⟩)
    · have hk := idAt_of_same h4 hi
      have hl := idAt_of_same h5 hj
      rcases hA.pos i hi with rfl | rfl <;> rcases hA.pos k hk with rfl | rfl <;>
        rcases hB.pos j hj with rfl | rfl <;>
        rcases hB.pos l hl with rfl | rfl <;> simp only [Btw] <;> omega
    · have hk := idAt_of_same h4 hi
      have hl := idAt_of_same h5 hj
      rcases hB.pos i hi with rfl | rfl <;> rcases hB.pos k hk with rfl | rfl <;>
        rcases hA.pos j hj with rfl | rfl <;>
        rcases hA.pos l hl with rfl | rfl <;> simp only [Btw] <;> omega
  · intro h
    have huv := hA.same
    have huv' := hB.same
    rcases lt_or_gt_of_ne n1 with h₁ | h₁ <;> rcases lt_or_gt_of_ne n2 with h₂ | h₂
    · exact ilv2_of_sorted h₁ h₂ huv huv' hu hu' hd h
    · exact ilv2_of_sorted h₁ h₂ huv huv'.symm hu hv₂ ⟨hd.2.1, hd.1, hd.2.2.2, hd.2.2.1⟩
        (by simp only [Btw] at h ⊢; omega)
    · exact ilv2_of_sorted h₁ h₂ huv.symm huv' hv₁ hu' ⟨hd.2.2.1, hd.2.2.2, hd.1, hd.2.1⟩
        (by simp only [Btw] at h ⊢; omega)
    · exact ilv2_of_sorted h₁ h₂ huv.symm huv'.symm hv₁ hv₂ ⟨hd.2.2.2, hd.2.2.1, hd.2.1, hd.1⟩
        (by simp only [Btw] at h ⊢; omega)

theorem not_ilv2_of_absent {a b : ℕ} (h : ∀ i, idAt s i ≠ some a) : ¬ Ilv2 s a b := by
  rintro (⟨i, j, k, l, ⟨-, -, -, h4, -⟩, hi, -⟩ | ⟨i, j, k, l, ⟨-, -, -, -, h5⟩, -, hj⟩)
  · exact h i hi
  · exact h l (idAt_of_same h5 hj)

theorem not_ilv2_of_absent' {a b : ℕ} (h : ∀ i, idAt s i ≠ some b) : ¬ Ilv2 s a b :=
  fun hab => not_ilv2_of_absent h (ilv2_comm.1 hab)

/-! ## Interleaving after joining two strands -/

section Join

variable {r x y : ℕ}

/-- The position in `jn s r` of a position of `s` other than `r`, `r + 1`. -/
def unrm (r i : ℕ) : ℕ := if i < r then i else i - 2

theorem rmIdx_unrm {i : ℕ} (h : i ≠ r ∧ i ≠ r + 1) : rmIdx r (unrm r i) = i := by
  unfold rmIdx unrm; split_ifs <;> omega

theorem unrm_rmIdx (i : ℕ) : unrm r (rmIdx r i) = i := by
  unfold rmIdx unrm; split_ifs <;> omega

theorem btw_unrm {u v c : ℕ} (hu : u ≠ r ∧ u ≠ r + 1) (hv : v ≠ r ∧ v ≠ r + 1)
    (hc : c ≠ r ∧ c ≠ r + 1) : Btw (unrm r u) (unrm r v) (unrm r c) ↔ Btw u v c := by
  unfold Btw unrm; split_ifs <;> omega

theorem rmIdx_ne (r i : ℕ) : rmIdx r i ≠ r ∧ rmIdx r i ≠ r + 1 := by
  unfold rmIdx; split_ifs <;> omega

theorem idAt_jn (hr : r + 1 < s.length) (hx : idAt s r = some x) (hy : idAt s (r + 1) = some y)
    (i : ℕ) : idAt (jn s r) i = (idAt s (rmIdx r i)).map (rlId y x) := by
  obtain ⟨P, A, B, Q, rfl, rfl⟩ := exists_mid hr
  have hA : A.1 = x := by simpa [idAt] using hx
  have hB : B.1 = y := by simpa [idAt] using hy
  rw [jn_mid, ← rmAt_mid P Q A B, hA, hB, idAt]
  have := idAt_rmAt (s := P ++ [A, B] ++ Q) (r := P.length) (by simp) i
  simp only [idAt] at this
  rw [List.getElem?_map, Option.map_map,
    (show Prod.fst ∘ rl y x = rlId y x ∘ Prod.fst from rfl), ← Option.map_map, this]
  rfl

theorem idAt_jn_unrm (hr : r + 1 < s.length) (hx : idAt s r = some x)
    (hy : idAt s (r + 1) = some y) {u : ℕ} (hu : u ≠ r ∧ u ≠ r + 1) :
    idAt (jn s r) (unrm r u) = (idAt s u).map (rlId y x) := by
  rw [idAt_jn hr hx hy, rmIdx_unrm hu]

theorem ne_r_of_id (hx : idAt s r = some x) (hy : idAt s (r + 1) = some y) {u c : ℕ}
    (hu : idAt s u = some c) (hcx : c ≠ x) (hcy : c ≠ y) : u ≠ r ∧ u ≠ r + 1 :=
  ⟨fun e => hcx (by rw [e, hx] at hu; exact (Option.some.inj hu).symm),
    fun e => hcy (by rw [e, hy] at hu; exact (Option.some.inj hu).symm)⟩

/-- An arc of `s` other than the joined ones is an arc of `jn s r`. -/
theorem arcAt_jn (hr : r + 1 < s.length) (hx : idAt s r = some x)
    (hy : idAt s (r + 1) = some y) {u v c : ℕ} (h : ArcAt s c u v) (hcx : c ≠ x) (hcy : c ≠ y) :
    ArcAt (jn s r) c (unrm r u) (unrm r v) := by
  have hur := ne_r_of_id hx hy h.id hcx hcy
  have hvr := ne_r_of_id hx hy h.id' hcx hcy
  have huv := h.same
  have := huv.lt_left; have := huv.lt_right; have := huv.ne
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · rw [same_jn_iff hr, rmIdx_unrm hur, rmIdx_unrm hvr]
    refine ⟨?_, by unfold unrm; split_ifs <;> omega, by unfold unrm; split_ifs <;> omega,
      Or.inl huv⟩
    intro e; apply huv.ne; rw [← rmIdx_unrm hur, ← rmIdx_unrm hvr, e]
  · rw [idAt_jn_unrm hr hx hy hur, h.id]; simp [rlId, hcy]
  · rw [idAt_jn hr hx hy] at hi
    rcases e : idAt s (rmIdx r i) with _ | c'
    · rw [e] at hi; simp at hi
    · rw [e] at hi
      have hc' : c' = c := by
        have := Option.some.inj hi; unfold rlId at this; split_ifs at this <;> omega
      subst hc'
      rcases h.pos _ e with e' | e' <;> [left; right] <;> rw [← e', unrm_rmIdx]

theorem absent_jn (hr : r + 1 < s.length) (hx : idAt s r = some x)
    (hy : idAt s (r + 1) = some y) {c : ℕ} (hcy : c ≠ y) (h : ∀ i, idAt s i ≠ some c)
    (hcx : c ≠ x) : ∀ i, idAt (jn s r) i ≠ some c := by
  intro i hi
  rw [idAt_jn hr hx hy] at hi
  rcases e : idAt s (rmIdx r i) with _ | c'
  · rw [e] at hi; simp at hi
  · rw [e] at hi
    have hc' : c' = c := by
      have := Option.some.inj hi; unfold rlId at this; split_ifs at this <;> omega
    subst hc'; exact h _ e
    
theorem absent_jn_right (hr : r + 1 < s.length) (hx : idAt s r = some x)
    (hy : idAt s (r + 1) = some y) (hxy : x ≠ y) : ∀ i, idAt (jn s r) i ≠ some y := by
  intro i hi
  rw [idAt_jn hr hx hy] at hi
  rcases e : idAt s (rmIdx r i) with _ | c'
  · rw [e] at hi; simp at hi
  · rw [e] at hi
    have := Option.some.inj hi; unfold rlId at this; split_ifs at this <;> omega

/-- The joined strand is the arc between the other endpoints of the two joined strands. -/
theorem arcAt_jn_join (hr : r + 1 < s.length) (hx : idAt s r = some x)
    (hy : idAt s (r + 1) = some y) (hxy : x ≠ y) {p q : ℕ} (hp : ArcAt s x r p)
    (hq : ArcAt s y (r + 1) q) : ArcAt (jn s r) x (unrm r p) (unrm r q) ∧
      (p ≠ r ∧ p ≠ r + 1) ∧ (q ≠ r ∧ q ≠ r + 1) := by
  have hpr : p ≠ r ∧ p ≠ r + 1 := ⟨hp.same.ne.symm, fun e => hxy (by
    have := hp.id'; rw [e, hy] at this; exact (Option.some.inj this).symm)⟩
  have hqr : q ≠ r ∧ q ≠ r + 1 := ⟨fun e => hxy (by
    have := hq.id'; rw [e, hx] at this; exact Option.some.inj this), hq.same.ne.symm⟩
  have := hp.same.lt_right; have := hq.same.lt_right
  refine ⟨⟨?_, ?_, fun i hi => ?_⟩, hpr, hqr⟩
  · rw [same_jn_iff hr, rmIdx_unrm hpr, rmIdx_unrm hqr]
    refine ⟨?_, by unfold unrm; split_ifs <;> omega, by unfold unrm; split_ifs <;> omega,
      Or.inr (Or.inr ⟨hp.same.symm, hq.same.symm⟩)⟩
    intro e
    have : p = q := by rw [← rmIdx_unrm hpr, ← rmIdx_unrm hqr, e]
    subst this
    exact hxy (by have := hp.id'; rw [hq.id'] at this; exact (Option.some.inj this).symm)
  · rw [idAt_jn_unrm hr hx hy hpr, hp.id']; simp [rlId]
  · rw [idAt_jn hr hx hy] at hi
    have hne := rmIdx_ne r i
    rcases e : idAt s (rmIdx r i) with _ | c'
    · rw [e] at hi; simp at hi
    · rw [e] at hi
      have := Option.some.inj hi
      unfold rlId at this
      split_ifs at this with h
      · subst h
        rcases hq.pos _ e with e' | e'
        · exact absurd e' hne.2
        · right; rw [← e', unrm_rmIdx]
      · subst this
        rcases hp.pos _ e with e' | e'
        · exact absurd e' hne.1
        · left; rw [← e', unrm_rmIdx]

/-- **Joining keeps a pairing a pairing.** -/
theorem Valid.jn (hv : Valid s) (hr : r + 1 < s.length) (hx : idAt s r = some x)
    (hy : idAt s (r + 1) = some y) (hxy : x ≠ y) : Valid (jn s r) := by
  intro i hi
  rw [length_jn hr] at hi
  have hi2 : i + 2 < s.length := by omega
  have hne := rmIdx_ne r i
  have hlt : rmIdx r i < s.length := by unfold rmIdx; split_ifs <;> omega
  obtain ⟨c, hc⟩ : ∃ c, idAt s (rmIdx r i) = some c := ⟨_, idAt_eq_some hlt⟩
  obtain ⟨p, hp⟩ := exists_arcAt hv hx
  obtain ⟨q, hq⟩ := exists_arcAt hv hy
  obtain ⟨w, hw⟩ := exists_arcAt hv hc
  have key : ∃ j, Same (Chord.jn s r) i j := by
    by_cases hcx : c = x
    · subst hcx
      obtain ⟨h, -, -⟩ := arcAt_jn_join hr hx hy hxy hp hq
      rcases hp.pos _ hc with e | e
      · exact absurd e hne.1
      · refine ⟨unrm r q, ?_⟩; rw [← unrm_rmIdx (r := r) i, e]; exact h.same
    by_cases hcy : c = y
    · subst hcy
      obtain ⟨h, -, -⟩ := arcAt_jn_join hr hx hy hxy hp hq
      rcases hq.pos _ hc with e | e
      · exact absurd e hne.2
      · refine ⟨unrm r p, ?_⟩; rw [← unrm_rmIdx (r := r) i, e]; exact h.same.symm
    · refine ⟨unrm r w, ?_⟩
      have := (arcAt_jn hr hx hy hw hcx hcy).same
      rwa [unrm_rmIdx] at this
  obtain ⟨j, hj⟩ := key
  refine ⟨j, hj, fun j' hj' => ?_⟩
  have h1 := (same_jn_iff hr).1 hj
  have h2 := (same_jn_iff hr).1 hj'
  rw [← rmIdx_inj (r := r)]
  have hjr := rmIdx_ne r j
  have hjr' := rmIdx_ne r j'
  rcases h1 with ⟨-, -, -, h1 | ⟨h1, h1'⟩ | ⟨h1, h1'⟩⟩ <;>
    rcases h2 with ⟨-, -, -, h2 | ⟨h2, h2'⟩ | ⟨h2, h2'⟩⟩
  all_goals first
    | exact hv.unique h2 h1
    | exact (hv.unique h1 h2).symm
    | exact hv.unique h1 h2
    | exact absurd (hv.unique h1 h2) (by omega)
    | exact hv.unique h1'.symm h2'.symm
    | exact hv.unique h2'.symm h1'.symm



theorem xor_xor_comm (a b c d : Prop) :
    ((a ↔ ¬ b) ↔ ¬ (c ↔ ¬ d)) ↔ ((a ↔ ¬ c) ↔ ¬ (b ↔ ¬ d)) := by
  by_cases a <;> by_cases b <;> by_cases c <;> by_cases d <;> simp_all

theorem btw_join {p q r c : ℕ} (hc : c ≠ p ∧ c ≠ q ∧ c ≠ r ∧ c ≠ r + 1) :
    Btw p q c ↔ (Btw r p c ↔ ¬ Btw (r + 1) q c) := by
  unfold Btw; omega

/-- **Two strands other than the joined ones** interleave after the join exactly when they did
before. -/
theorem ilv2_jn_of_ne (hv : Valid s) (hr : r + 1 < s.length) (hx : idAt s r = some x)
    (hy : idAt s (r + 1) = some y) {a b : ℕ} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) : Ilv2 (jn s r) a b ↔ Ilv2 s a b := by
  by_cases ha : ∃ u, idAt s u = some a
  · by_cases hb : ∃ u, idAt s u = some b
    · obtain ⟨u, hu⟩ := ha
      obtain ⟨u', hu'⟩ := hb
      obtain ⟨v, hA⟩ := exists_arcAt hv hu
      obtain ⟨v', hB⟩ := exists_arcAt hv hu'
      rw [ilv2_iff_btw (arcAt_jn hr hx hy hA hax hay) (arcAt_jn hr hx hy hB hbx hby) hab,
        btw_unrm (ne_r_of_id hx hy hA.id hax hay) (ne_r_of_id hx hy hA.id' hax hay)
          (ne_r_of_id hx hy hB.id hbx hby),
        btw_unrm (ne_r_of_id hx hy hA.id hax hay) (ne_r_of_id hx hy hA.id' hax hay)
          (ne_r_of_id hx hy hB.id' hbx hby), ilv2_iff_btw hA hB hab]
    · simp only [not_exists] at hb
      exact iff_of_false (not_ilv2_of_absent' (absent_jn hr hx hy hby hb hbx))
        (not_ilv2_of_absent' hb)
  · simp only [not_exists] at ha
    exact iff_of_false (not_ilv2_of_absent (absent_jn hr hx hy hay ha hax))
      (not_ilv2_of_absent ha)

/-- **The joined strand** interleaves another strand exactly when one of the two joined strands
did. -/
theorem ilv2_jn_left (hv : Valid s) (hr : r + 1 < s.length) (hx : idAt s r = some x)
    (hy : idAt s (r + 1) = some y) (hxy : x ≠ y) {b : ℕ} (hbx : b ≠ x) (hby : b ≠ y) :
    Ilv2 (jn s r) x b ↔ (Ilv2 s x b ↔ ¬ Ilv2 s y b) := by
  by_cases hb : ∃ u, idAt s u = some b
  · obtain ⟨u', hu'⟩ := hb
    obtain ⟨v', hB⟩ := exists_arcAt hv hu'
    obtain ⟨p, hp⟩ := exists_arcAt hv hx
    obtain ⟨q, hq⟩ := exists_arcAt hv hy
    obtain ⟨hJ, hpr, hqr⟩ := arcAt_jn_join hr hx hy hxy hp hq
    have hne : ∀ {i j c d}, idAt s i = some c → idAt s j = some d → c ≠ d → i ≠ j :=
      fun hi hj hcd e => hcd (by rw [e, hj] at hi; exact (Option.some.inj hi).symm)
    have h1 := ne_r_of_id hx hy hB.id hbx hby
    have h2 := ne_r_of_id hx hy hB.id' hbx hby
    rw [ilv2_iff_btw hJ (arcAt_jn hr hx hy hB hbx hby) (Ne.symm hbx), btw_unrm hpr hqr h1,
      btw_unrm hpr hqr h2, ilv2_iff_btw hp hB (Ne.symm hbx), ilv2_iff_btw hq hB (Ne.symm hby),
      btw_join ⟨hne hB.id hp.id' hbx, hne hB.id hq.id' hby, h1⟩,
      btw_join ⟨hne hB.id' hp.id' hbx, hne hB.id' hq.id' hby, h2⟩, btw_comm, btw_comm (u := r)]
    exact xor_xor_comm _ _ _ _
  · simp only [not_exists] at hb
    rw [iff_false_intro (not_ilv2_of_absent' (absent_jn hr hx hy hby hb hbx)),
      iff_false_intro (not_ilv2_of_absent' (s := s) (a := x) hb),
      iff_false_intro (not_ilv2_of_absent' (s := s) (a := y) hb)]
    simp

theorem not_ilv2_jn_right (hr : r + 1 < s.length) (hx : idAt s r = some x)
    (hy : idAt s (r + 1) = some y) (hxy : x ≠ y) {b : ℕ} : ¬ Ilv2 (jn s r) y b :=
  not_ilv2_of_absent (absent_jn_right hr hx hy hxy)

end Join

/-! ## Two-sided matchings -/

/-- A move of a two-sided matching: a cup or a crossing (`Move`), or a cap at `g`, `g + 1`. -/
inductive TMove (α : Type*) where
  | mv (m : Move α)
  | cap (g : ℕ)

/-- The state of a two-sided matching at some height, in the bent picture: the next fresh strand
id, the strands crossing this height (with the id of each), the crossings so far (as pairs of
strand ids, renamed along joins) and the caps so far (as the pairs of ids they joined). -/
structure TState (α : Type*) where
  nxt : ℕ
  st : List (ℕ × α)
  xs : List (Sym2 ℕ)
  cps : List (ℕ × ℕ)

/-- The id of the strand at position `i` (`0` if there is none). -/
def idD (s : List (ℕ × α)) (i : ℕ) : ℕ := (idAt s i).getD 0

theorem idAt_eq_idD {s : List (ℕ × α)} {i : ℕ} (h : i < s.length) : idAt s i = some (idD s i) := by
  rw [idD, idAt_eq_some h]; rfl

section Model

variable (d : α → α)

/-- One move of a two-sided matching, the moves being placed after the first `k` (bent)
strands. -/
def tStep (k : ℕ) (T : TState α) : TMove α → TState α
  | .mv (.cup g a) => ⟨T.nxt + 1, insAt T.st (k + g) (T.nxt, a) (T.nxt, d a), T.xs, T.cps⟩
  | .mv (.cross p) => ⟨T.nxt, swapAt T.st (k + p),
      T.xs ++ [s(idD T.st (k + p), idD T.st (k + p + 1))], T.cps⟩
  | .cap g => ⟨T.nxt, jn T.st (k + g),
      T.xs.map (Sym2.map (rlId (idD T.st (k + g + 1)) (idD T.st (k + g)))),
      T.cps ++ [(idD T.st (k + g), idD T.st (k + g + 1))]⟩

/-- A move applies to the state `s`: a cap joins two distinct strands with dual labels. -/
def TMove.Ok (k : ℕ) (s : List (ℕ × α)) : TMove α → Prop
  | .mv (.cup g _) => k + g ≤ s.length
  | .mv (.cross p) => k + p + 1 < s.length
  | .cap g => ∃ A B, s[k + g]? = some A ∧ s[k + g + 1]? = some B ∧ A.2 = d B.2 ∧ A.1 ≠ B.1

/-- Every move of a two-sided matching applies. -/
def TFits (k : ℕ) : TState α → List (TMove α) → Prop
  | _, [] => True
  | T, m :: R => m.Ok d k T.st ∧ TFits k (tStep d k T m) R

/-- The state after the moves `R`. -/
def tRun (k : ℕ) (T : TState α) (R : List (TMove α)) : TState α := R.foldl (tStep d k) T

/-- The number of crossings of a two-sided matching. -/
def ncr₂ (R : List (TMove α)) : ℕ := R.countP fun m => match m with
  | .mv (.cross _) => true
  | _ => false

theorem length_xs_tRun (k : ℕ) : ∀ (R : List (TMove α)) (T : TState α),
    (tRun d k T R).xs.length = T.xs.length + ncr₂ R
  | [], _ => rfl
  | m :: R, T => by
    rw [tRun, List.foldl_cons, ← tRun, length_xs_tRun k R]
    rcases m with (⟨g, a⟩ | p) | g
    · simp [tStep, ncr₂]
    · simp [tStep, ncr₂]; omega
    · simp [tStep, ncr₂]

/-- The invariant of a two-sided matching: the strands form a pairing with ids below `nxt`, and
two distinct strands interleave exactly when they have crossed an odd number of times. -/
structure TInv (T : TState α) : Prop where
  valid : Valid T.st
  fresh : ∀ e ∈ T.st, e.1 < T.nxt
  parity : ∀ a b, a ≠ b → (Ilv2 T.st a b ↔ Odd (T.xs.count s(a, b)))

variable {d}

theorem count_map_sym2_of (f : ℕ → ℕ) (w : Sym2 ℕ) (h : ∀ z, Sym2.map f z = w ↔ z = w) :
    ∀ xs : List (Sym2 ℕ), (xs.map (Sym2.map f)).count w = xs.count w
  | [] => rfl
  | z :: xs => by
    rw [List.map_cons, List.count_cons, List.count_cons, count_map_sym2_of f w h xs]
    by_cases hz : z = w
    · simp [hz, (h w).2 rfl]
    · simp [hz, show Sym2.map f z ≠ w from fun e => hz ((h z).1 e)]

theorem count_map_sym2_two (f : ℕ → ℕ) (w w₁ w₂ : Sym2 ℕ) (hne : w₁ ≠ w₂)
    (h : ∀ z, Sym2.map f z = w ↔ z = w₁ ∨ z = w₂) :
    ∀ xs : List (Sym2 ℕ), (xs.map (Sym2.map f)).count w = xs.count w₁ + xs.count w₂
  | [] => rfl
  | z :: xs => by
    rw [List.map_cons, List.count_cons, List.count_cons, List.count_cons,
      count_map_sym2_two f w w₁ w₂ hne h xs]
    by_cases h1 : z = w₁
    · subst h1; simp [(h z).2 (Or.inl rfl), hne]; omega
    · by_cases h2 : z = w₂
      · subst h2; simp [(h z).2 (Or.inr rfl), h1]; omega
      · simp [h1, h2, show Sym2.map f z ≠ w from fun e => (((h z).1 e).elim h1 h2)]

theorem count_map_sym2_zero (f : ℕ → ℕ) (w : Sym2 ℕ) (h : ∀ z, Sym2.map f z ≠ w) :
    ∀ xs : List (Sym2 ℕ), (xs.map (Sym2.map f)).count w = 0 := by
  intro xs
  rw [List.count_eq_zero]
  intro hm
  obtain ⟨z, -, hz⟩ := List.mem_map.1 hm
  exact h z hz

theorem mem_jn {s : List (ℕ × α)} {r : ℕ} (hr : r + 1 < s.length) {e : ℕ × α}
    (he : e ∈ jn s r) : ∃ e' ∈ s, e = rl (idD s (r + 1)) (idD s r) e' := by
  obtain ⟨P, A, B, Q, rfl, rfl⟩ := exists_mid hr
  have hA : idD (P ++ [A, B] ++ Q) P.length = A.1 := by simp [idD, idAt]
  have hB : idD (P ++ [A, B] ++ Q) (P.length + 1) = B.1 := by simp [idD, idAt]
  rw [jn_mid] at he
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
  refine ⟨e', ?_, by rw [hA, hB]⟩
  simp only [List.mem_append] at he' ⊢
  rcases he' with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr h

theorem mem_insAt {β : Type*} {s : List β} {g : ℕ} {x y e : β} (he : e ∈ insAt s g x y) :
    e ∈ s ∨ e = x ∨ e = y := by
  simp only [insAt, List.mem_append, List.mem_cons] at he
  rcases he with h | h | h | h
  · exact Or.inl (List.mem_of_mem_take h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl (List.mem_of_mem_drop h)

/-- **The invariant is preserved by every move.** -/
theorem TInv.step {k : ℕ} {T : TState α} (I : TInv T) {m : TMove α} (hm : m.Ok d k T.st) :
    TInv (tStep d k T m) := by
  rcases m with (⟨g, a⟩ | p) | g
  · simp only [TMove.Ok] at hm
    have hk : ∀ x ∈ T.st, x.1 ≠ T.nxt := fun x hx => (I.fresh x hx).ne
    refine ⟨I.valid.insAt hm hk a (d a), fun e he => ?_, fun a' b' hab => ?_⟩
    · rcases mem_insAt he with h | rfl | rfl
      · have := I.fresh e h; simp only [tStep]; omega
      · simp [tStep]
      · simp [tStep]
    · simp only [tStep]
      rw [← I.parity a' b' hab, Ilv2, Ilv2, ilvArc_insAt_iff hm hk, ilvArc_insAt_iff hm hk]
  · simp only [TMove.Ok] at hm
    set s := T.st
    have hp0 : k + p < s.length := by omega
    have ha0 := idAt_eq_idD hp0
    have hb0 := idAt_eq_idD hm
    set a0 := idD s (k + p)
    set b0 := idD s (k + p + 1)
    set z : Sym2 ℕ := s(a0, b0) with hz
    refine ⟨I.valid.swapAt hm, fun e he => I.fresh e (mem_swapAt he), fun a b hab => ?_⟩
    simp only [tStep]
    rw [List.count_append, List.count_singleton]
    split_ifs with hc
    · have hzw : z = s(a, b) := beq_iff_eq.1 hc
      rw [Nat.odd_add_one, ← I.parity a b hab]
      rw [hz, Sym2.eq_iff] at hzw
      rcases hzw with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1] at ha0; rw [e2] at hb0
        exact ilv2_swapAt_iff I.valid hm ha0 hb0 hab
      · rw [e1] at ha0; rw [e2] at hb0
        rw [ilv2_comm, ilv2_swapAt_iff I.valid hm ha0 hb0 (Ne.symm hab), ilv2_comm]
    · have hzw : z ≠ s(a, b) := fun e => hc (beq_iff_eq.2 e)
      rw [add_zero, ← I.parity a b hab]
      refine ilv2_swapAt_of_ne hm (fun ⟨h1, h2⟩ => hzw ?_) (fun ⟨h1, h2⟩ => hzw ?_)
      · rw [ha0] at h1; rw [hb0] at h2
        rw [hz, Option.some.inj h1, Option.some.inj h2]
      · rw [ha0] at h1; rw [hb0] at h2
        rw [hz, Option.some.inj h1, Option.some.inj h2, Sym2.eq_swap]
  · obtain ⟨A, B, hA, hB, -, hAB⟩ := hm
    set s := T.st
    have hr : k + g + 1 < s.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hB; cases hB
    have hx := idAt_eq_idD (s := s) (i := k + g) (by omega)
    have hy := idAt_eq_idD hr
    set x := idD s (k + g)
    set y := idD s (k + g + 1)
    have hxy : x ≠ y := by
      have e1 : x = A.1 := by simp [x, idD, idAt, hA]
      have e2 : y = B.1 := by simp [y, idD, idAt, hB]
      rw [e1, e2]; exact hAB
    refine ⟨I.valid.jn hr hx hy hxy, fun e he => ?_, fun a b hab => ?_⟩
    · obtain ⟨e', he', rfl⟩ := mem_jn hr he
      simp only [rl, rlId]
      split_ifs
      · have hm : (s[k + g]'(by omega)) ∈ s := List.getElem_mem _
        have := I.fresh _ hm
        have e : x = (s[k + g]'(by omega)).1 := by
          simp [x, idD, idAt, List.getElem?_eq_getElem (show k + g < s.length by omega)]
        simp only [tStep]; rw [← e] at this; exact this
      · exact I.fresh e' he'
    · simp only [tStep]
      have hf : ∀ c, rlId y x c = if c = y then x else c := fun c => rfl
      by_cases hay : a = y
      · subst hay
        rw [iff_false_intro (not_ilv2_jn_right hr hx hy hxy), count_map_sym2_zero _ _ ?_]
        · simp
        · intro z hz
          induction z using Sym2.ind with
          | _ c e =>
          rw [Sym2.map_mk, Sym2.eq_iff, hf, hf] at hz
          split_ifs at hz <;> omega
      by_cases hby : b = y
      · subst hby
        rw [ilv2_comm, iff_false_intro (not_ilv2_jn_right hr hx hy hxy),
          count_map_sym2_zero _ _ ?_]
        · simp
        · intro z hz
          induction z using Sym2.ind with
          | _ c e =>
          rw [Sym2.map_mk, Sym2.eq_iff, hf, hf] at hz
          split_ifs at hz <;> omega
      by_cases hax : a = x
      · subst hax
        rw [ilv2_jn_left I.valid hr hx hy hxy (Ne.symm hab) hby,
          count_map_sym2_two _ _ s(x, b) s(y, b) (by simp; omega) ?_,
          I.parity x b hab, I.parity y b (Ne.symm hby), Nat.odd_add]
        · simp only [← Nat.not_odd_iff_even]
        · intro z
          induction z using Sym2.ind with
          | _ c e =>
          rw [Sym2.map_mk, Sym2.eq_iff, Sym2.eq_iff, Sym2.eq_iff, hf, hf]
          split_ifs <;> omega
      by_cases hbx : b = x
      · subst hbx
        rw [ilv2_comm, ilv2_jn_left I.valid hr hx hy hxy hab hay,
          count_map_sym2_two _ _ s(x, a) s(y, a) (by simp; omega) ?_,
          I.parity x a (Ne.symm hab), I.parity y a (Ne.symm hay), Nat.odd_add]
        · simp only [← Nat.not_odd_iff_even]
        · intro z
          induction z using Sym2.ind with
          | _ c e =>
          rw [Sym2.map_mk, Sym2.eq_iff, Sym2.eq_iff, Sym2.eq_iff, hf, hf]
          split_ifs <;> omega
      rw [ilv2_jn_of_ne I.valid hr hx hy hab hax hay hbx hby, count_map_sym2_of _ _ ?_,
        I.parity a b hab]
      intro z
      induction z using Sym2.ind with
      | _ c e =>
      rw [Sym2.map_mk, Sym2.eq_iff, Sym2.eq_iff, hf, hf]
      split_ifs <;> omega

theorem TInv.run {k : ℕ} {R : List (TMove α)} : ∀ {T : TState α}, TInv T → TFits d k T R →
    TInv (tRun d k T R) := by
  induction R with
  | nil => intro T I _; exact I
  | cons m R ih => intro T I h; exact ih (I.step h.1) h.2

/-- **Parity bound**: if no strand crosses itself and two strands cross at most once, there are at
most as many crossings as the crossing number of the pairing. -/
theorem length_xs_le_cr {T : TState α} (I : TInv T) (hn : T.xs.Nodup)
    (hd : ∀ z ∈ T.xs, ¬ z.IsDiag) : T.xs.length ≤ cr T.st := by
  classical
  let f : ℕ × ℕ × ℕ × ℕ → Sym2 ℕ := fun q => s(idD T.st q.1, idD T.st q.2.1)
  have hsub : T.xs.toFinset ⊆ (crSet T.st).image f := by
    intro z hz
    rw [List.mem_toFinset] at hz
    have hdz := hd z hz
    induction z using Sym2.ind with
    | _ a b =>
    have hab : a ≠ b := fun e => hdz (by rw [e]; exact Sym2.mk_isDiag_iff.2 rfl)
    have hc : T.xs.count s(a, b) = 1 := List.count_eq_one_of_mem hn hz
    have hil := (I.parity a b hab).2 (by rw [hc]; decide)
    rw [Finset.mem_image]
    rcases hil with ⟨i, j, k, l, hq, hi, hj⟩ | ⟨i, j, k, l, hq, hi, hj⟩
    · refine ⟨(i, j, k, l), mem_crSet.2 hq, ?_⟩
      simp only [f, idD, hi, hj, Option.getD_some]
    · refine ⟨(i, j, k, l), mem_crSet.2 hq, ?_⟩
      simp only [f, idD, hi, hj, Option.getD_some, Sym2.eq_swap]
  calc T.xs.length = T.xs.toFinset.card := (List.toFinset_card_of_nodup hn).symm
    _ ≤ ((crSet T.st).image f).card := Finset.card_le_card hsub
    _ ≤ (crSet T.st).card := Finset.card_image_le
    _ = cr T.st := rfl

theorem length_xps (D : List (Move α)) : ∀ s : List (ℕ × α),
    (xps d s D).length = OddMath.SKM.ncr D := by
  induction D with
  | nil => intro s; rfl
  | cons m D ih =>
    intro s
    cases m <;> simp [xps, xpOf, ih]

/-- A diagram of cups and crossings without crossings is a starting state for the invariant. -/
theorem tInv_start {D : List (Move α)} (hf : Fits 0 D) (h0 : OddMath.SKM.ncr D = 0) :
    TInv (⟨(run d D).length, run d D, [], []⟩ : TState α) := by
  have hi := inv_run (d := d) hf
  have I := runInv d hf
  have hx : xps d [] D = [] := List.eq_nil_of_length_eq_zero (by rw [length_xps, h0])
  refine ⟨hi.1, hi.2, fun a b hab => ?_⟩
  have := I.parity a b hab
  rw [hx] at this
  simpa using this

end Model

end StringDiagrams.Chord
