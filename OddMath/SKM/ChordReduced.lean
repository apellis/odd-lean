/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanChord
import Mathlib.Data.Sym.Sym2

/-!
# Reduced chord diagrams

Combinatorics for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
§8 (the reduced matchings before Theorem 8.1), in the one-sided case of an empty bottom boundary.

A diagram of cups and crossings `D : List (Move α)` (from `StringDiagrams.Chord`, read from the
bottom) is an `∅v`-matching: its strands are the arcs created by the cups, and `run d D` records
for every top endpoint the id of its strand. Every strand has exactly one critical point, the
minimum of its cup. The crossings of `D` are recorded as unordered pairs of strand ids
(`xps`). Following [BE2] §8, `D` is *reduced* (`Reduced`) if no strand crosses itself and two
distinct strands cross at most once.

## Main results

* `cr_swapAt_add_one`, `cr_swapAt_of_same`, `cr_swapAt_of_not_ilv`, `cr_insAt`: how the crossing
  number of a pairing changes under the moves.
* `ilv2_swapAt_iff`, `ilv2_swapAt_of_ne`, `ilvArc_insAt_iff`: two arcs interleave after a move
  exactly when they did before, except for the two arcs of a crossing, whose interleaving toggles.
* `runInv`, `cr_run_le_ncr`: a diagram has at least as many crossings as the crossing number of its pairing.
* `reduced_iff`: **a diagram is reduced if and only if it has as many crossings as the crossing
  number of its pairing**, i.e. the minimal number (two strands cross an odd number of times
  exactly when their endpoints interleave).
* `reduced_canon`: the canonical diagram of a pairing is reduced.
* `equiv_canon_of_reduced`: a reduced diagram is equivalent (`Chord.Equiv`: isotopy and the braid
  move) to the canonical diagram of its pairing.
-/

namespace StringDiagrams.Chord

variable {α : Type*}

/-! ## Crossing numbers under the moves -/

section CrossingNumber

open scoped Classical

variable {s : List (ℕ × α)}

/-- The quadruple `x` has the positions `p`, `p + 1` in consecutive slots. -/
def ConsAt (x : ℕ × ℕ × ℕ × ℕ) (p : ℕ) : Prop :=
  (x.1 = p ∧ x.2.1 = p + 1) ∨ (x.2.1 = p ∧ x.2.2.1 = p + 1) ∨ (x.2.2.1 = p ∧ x.2.2.2 = p + 1)

/-- Apply `tau p` to the four positions. -/
def tau4 (p : ℕ) (x : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (tau p x.1, tau p x.2.1, tau p x.2.2.1, tau p x.2.2.2)

theorem tau4_tau4 (p : ℕ) (x : ℕ × ℕ × ℕ × ℕ) : tau4 p (tau4 p x) = x := by
  simp [tau4, tau_tau]

theorem ilv_iff_consAt {p : ℕ} : Ilv s p ↔ ∃ x ∈ crSet s, ConsAt x p := by
  constructor
  · rintro ⟨i, j, k, l, h, hc⟩
    exact ⟨(i, j, k, l), mem_crSet.2 h, hc⟩
  · rintro ⟨x, hx, hc⟩
    exact ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, mem_crSet.1 hx, hc⟩

/-- A crossing quadruple without `p`, `p + 1` in consecutive slots survives the exchange of the
positions `p`, `p + 1`. -/
theorem tau4_mem_crSet {p : ℕ} (hp : p + 1 < s.length) {x : ℕ × ℕ × ℕ × ℕ} (hx : x ∈ crSet s)
    (hc : ¬ ConsAt x p) : tau4 p x ∈ crSet (swapAt s p) := by
  obtain ⟨i, j, k, l⟩ := x
  obtain ⟨h1, h2, h3, h4, h5⟩ : Cr4 s i j k l := mem_crSet.1 hx
  simp only [ConsAt, not_or] at hc
  obtain ⟨c1, c2, c3⟩ := hc
  apply mem_crSet.2
  refine ⟨(tau_lt_iff p c1 (by omega)).2 h1, (tau_lt_iff p c2 (by omega)).2 h2,
    (tau_lt_iff p c3 (by omega)).2 h3, ?_, ?_⟩
  · rw [same_swapAt hp]; simp only [tau4, tau_tau]; exact h4
  · rw [same_swapAt hp]; simp only [tau4, tau_tau]; exact h5

/-- At most one crossing quadruple has `p`, `p + 1` in consecutive slots. -/
theorem consAt_unique (hv : Valid s) {p : ℕ} {x y : ℕ × ℕ × ℕ × ℕ} (hx : x ∈ crSet s)
    (hy : y ∈ crSet s) (hcx : ConsAt x p) (hcy : ConsAt y p) : x = y := by
  have key : ∀ z ∈ crSet s, ConsAt z p → ∀ a b, Same s p a → Same s (p + 1) b →
      z = (p, p + 1, a, b) ∨ z = (b, p, p + 1, a) ∨ z = (a, b, p, p + 1) := by
    intro z hz hc a b ha hb
    obtain ⟨i, j, k, l⟩ := z
    obtain ⟨h1, h2, h3, h4, h5⟩ : Cr4 s i j k l := mem_crSet.1 hz
    rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only at e1 e2 <;> subst e1 e2
    · left; rw [hv.unique h4 ha, hv.unique h5 hb]
    · right; left; rw [hv.unique h4.symm hb, hv.unique h5 ha]
    · right; right; rw [hv.unique h4.symm ha, hv.unique h5.symm hb]
  have hp : p + 1 < s.length := by
    obtain ⟨i, j, k, l⟩ := x
    obtain ⟨h1, h2, h3, h4, h5⟩ : Cr4 s i j k l := mem_crSet.1 hx
    rcases hcx with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only at e1 e2 <;> subst e1 e2
    · exact h5.lt_left
    · exact h4.lt_right
    · exact h5.lt_right
  obtain ⟨a, ha⟩ := hv.exists (show p < s.length by omega)
  obtain ⟨b, hb⟩ := hv.exists hp
  have ox := mem_crSet.1 hx
  have oy := mem_crSet.1 hy
  rcases key x hx hcx a b ha hb with rfl | rfl | rfl <;>
    rcases key y hy hcy a b ha hb with rfl | rfl | rfl <;>
    first | rfl | (exfalso; obtain ⟨o1, o2, o3, -, -⟩ := ox; obtain ⟨o1', o2', o3', -, -⟩ := oy
                   simp only at o1 o2 o3 o1' o2' o3'; omega)

/-- Without interleaving at `p`, exchanging the positions `p`, `p + 1` does not decrease the
crossing number. -/
theorem cr_le_cr_swapAt {p : ℕ} (hp : p + 1 < s.length) (h : ¬ Ilv s p) :
    cr s ≤ cr (swapAt s p) := by
  unfold cr
  refine Finset.card_le_card_of_injOn (tau4 p) (fun x hx => ?_) (fun x _ y _ e => ?_)
  · exact tau4_mem_crSet hp hx fun hc => h (ilv_iff_consAt.2 ⟨x, hx, hc⟩)
  · have := congrArg (tau4 p) e
    rwa [tau4_tau4, tau4_tau4] at this

/-- With interleaving at `p`, exchanging the positions `p`, `p + 1` decreases the crossing number
by at most one. -/
theorem cr_le_cr_swapAt_add_one (hv : Valid s) {p : ℕ} (h : Ilv s p) :
    cr s ≤ cr (swapAt s p) + 1 := by
  have hp := h.lt
  obtain ⟨x₀, hx₀, hc₀⟩ := ilv_iff_consAt.1 h
  unfold cr
  have hsub : crSet s ⊆ insert x₀ ((crSet (swapAt s p)).image (tau4 p)) := by
    intro x hx
    by_cases hc : ConsAt x p
    · rw [consAt_unique hv hx hx₀ hc hc₀]; exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨tau4 p x, ?_, tau4_tau4 p x⟩)
      exact tau4_mem_crSet hp hx hc
  calc (crSet s).card ≤ (insert x₀ ((crSet (swapAt s p)).image (tau4 p))).card :=
        Finset.card_le_card hsub
    _ ≤ ((crSet (swapAt s p)).image (tau4 p)).card + 1 := Finset.card_insert_le _ _
    _ ≤ (crSet (swapAt s p)).card + 1 := by
        have := Finset.card_image_le (s := crSet (swapAt s p)) (f := tau4 p); omega

/-- **Exchanging interleaved adjacent endpoints decreases the crossing number by one.** -/
theorem cr_swapAt_add_one (hv : Valid s) {p : ℕ} (h : Ilv s p) :
    cr (swapAt s p) + 1 = cr s := by
  have := cr_swapAt_lt hv h
  have := cr_le_cr_swapAt_add_one hv h
  omega

/-- **Exchanging non-interleaved adjacent endpoints of distinct arcs increases the crossing number
by one.** -/
theorem cr_swapAt_of_not_ilv (hv : Valid s) {p : ℕ} (hp : p + 1 < s.length)
    (hn : ¬ Same s p (p + 1)) (h : ¬ Ilv s p) : cr (swapAt s p) = cr s + 1 := by
  have h' : Ilv (swapAt s p) p := (ilv_swapAt_iff hv hp hn).2 h
  have := cr_swapAt_add_one (hv.swapAt hp) h'
  rw [swapAt_swapAt] at this
  omega

/-- **Exchanging the two ends of one arc does not change the crossing number.** -/
theorem cr_swapAt_of_same (hv : Valid s) {p : ℕ} (hs : Same s p (p + 1)) :
    cr (swapAt s p) = cr s := by
  have hp : p + 1 < s.length := hs.lt_right
  have hs' : Same (swapAt s p) p (p + 1) := by
    rw [same_swapAt hp]; simp only [tau_left, tau_right]; exact hs.symm
  have h1 : ¬ Ilv s p := fun h => h.not_same hv hs
  have h2 : ¬ Ilv (swapAt s p) p := fun h => h.not_same (hv.swapAt hp) hs'
  have a := cr_le_cr_swapAt hp h1
  have b := cr_le_cr_swapAt (by simpa using hp) h2
  rw [swapAt_swapAt] at b
  omega

/-- The index of a position of `insAt s g x y` other than `g`, `g + 1` in `s`. -/
def unIns (g i : ℕ) : ℕ := if i < g then i else i - 2

theorem unIns_inj {g i j : ℕ} (hi : i ≠ g ∧ i ≠ g + 1) (hj : j ≠ g ∧ j ≠ g + 1)
    (e : unIns g i = unIns g j) : i = j := by
  unfold unIns at e; split_ifs at e <;> omega

theorem unIns_lt {g i j : ℕ} (hi : i ≠ g ∧ i ≠ g + 1) (hj : j ≠ g ∧ j ≠ g + 1) (h : i < j) :
    unIns g i < unIns g j := by
  unfold unIns; split_ifs <;> omega

theorem same_insAt_split {g : ℕ} (hg : g ≤ s.length) {n : ℕ} (hk : ∀ x ∈ s, x.1 ≠ n) (a b : α)
    {i j : ℕ} (hij : Same (insAt s g (n, a) (n, b)) i j) (hlt : i < j) (hgap : ¬ (i = g ∧ j = g + 1)) :
    i ≠ g ∧ i ≠ g + 1 ∧ j ≠ g ∧ j ≠ g + 1 ∧ Same s (unIns g i) (unIns g j) := by
  rw [same_insAt_iff hg hk] at hij
  rcases hij with h | h | h
  · exact absurd h hgap
  · omega
  · exact h

theorem same_insAt_of {g : ℕ} (hg : g ≤ s.length) {n : ℕ} (hk : ∀ x ∈ s, x.1 ≠ n) (a b : α)
    {i j : ℕ} (h : Same s i j) :
    Same (insAt s g (n, a) (n, b)) (if i < g then i else i + 2) (if j < g then j else j + 2) := by
  rw [same_insAt_iff hg hk]
  right; right
  refine ⟨by split_ifs <;> omega, by split_ifs <;> omega, by split_ifs <;> omega,
    by split_ifs <;> omega, ?_⟩
  have e : ∀ m, (if (if m < g then m else m + 2) < g then (if m < g then m else m + 2)
      else (if m < g then m else m + 2) - 2) = m := by intro m; split_ifs <;> omega
  rw [e, e]; exact h

/-- **A cup with a fresh id does not change the crossing number.** -/
theorem cr_insAt {g : ℕ} (hg : g ≤ s.length) {n : ℕ} (hk : ∀ x ∈ s, x.1 ≠ n) (a b : α) :
    cr (insAt s g (n, a) (n, b)) = cr s := by
  apply le_antisymm
  · unfold cr
    refine Finset.card_le_card_of_injOn
      (fun x => (unIns g x.1, unIns g x.2.1, unIns g x.2.2.1, unIns g x.2.2.2))
      (fun x hx => ?_) (fun x hx y hy e => ?_)
    · obtain ⟨i, j, k, l⟩ := x
      obtain ⟨h1, h2, h3, h4, h5⟩ : Cr4 (insAt s g (n, a) (n, b)) i j k l := mem_crSet.1 hx
      obtain ⟨a1, a2, a3, a4, a5⟩ := same_insAt_split hg hk a b h4 (by omega) (by omega)
      obtain ⟨b1, b2, b3, b4, b5⟩ := same_insAt_split hg hk a b h5 (by omega) (by omega)
      apply mem_crSet.2
      exact ⟨unIns_lt ⟨a1, a2⟩ ⟨b1, b2⟩ h1, unIns_lt ⟨b1, b2⟩ ⟨a3, a4⟩ h2,
        unIns_lt ⟨a3, a4⟩ ⟨b3, b4⟩ h3, a5, b5⟩
    · obtain ⟨i, j, k, l⟩ := x
      obtain ⟨i', j', k', l'⟩ := y
      obtain ⟨h1, h2, h3, h4, h5⟩ : Cr4 (insAt s g (n, a) (n, b)) i j k l := mem_crSet.1 hx
      obtain ⟨h1', h2', h3', h4', h5'⟩ : Cr4 (insAt s g (n, a) (n, b)) i' j' k' l' := mem_crSet.1 hy
      obtain ⟨a1, a2, a3, a4, -⟩ := same_insAt_split hg hk a b h4 (by omega) (by omega)
      obtain ⟨b1, b2, b3, b4, -⟩ := same_insAt_split hg hk a b h5 (by omega) (by omega)
      obtain ⟨a1', a2', a3', a4', -⟩ := same_insAt_split hg hk a b h4' (by omega) (by omega)
      obtain ⟨b1', b2', b3', b4', -⟩ := same_insAt_split hg hk a b h5' (by omega) (by omega)
      simp only [Prod.mk.injEq] at e
      obtain ⟨e1, e2, e3, e4⟩ := e
      simp only [Prod.mk.injEq]
      exact ⟨unIns_inj ⟨a1, a2⟩ ⟨a1', a2'⟩ e1, unIns_inj ⟨b1, b2⟩ ⟨b1', b2'⟩ e2,
        unIns_inj ⟨a3, a4⟩ ⟨a3', a4'⟩ e3, unIns_inj ⟨b3, b4⟩ ⟨b3', b4'⟩ e4⟩
  · have := cr_rmAt_le (s := insAt s g (n, a) (n, b)) (r := g) (by rw [length_insAt s hg]; omega)
    rwa [rmAt_insAt s g _ _ hg] at this

end CrossingNumber

/-! ## Interleaving of two arcs under the moves -/

section Interleaving

variable {s : List (ℕ × α)}

/-- The arcs with ids `a` and `b` interleave, the arc `a` having the leftmost endpoint. -/
def IlvArc (s : List (ℕ × α)) (a b : ℕ) : Prop :=
  ∃ i j k l, Cr4 s i j k l ∧ idAt s i = some a ∧ idAt s j = some b

/-- The arcs with ids `a` and `b` interleave. -/
def Ilv2 (s : List (ℕ × α)) (a b : ℕ) : Prop := IlvArc s a b ∨ IlvArc s b a

theorem ilv2_comm {a b : ℕ} : Ilv2 s a b ↔ Ilv2 s b a := Or.comm

/-- The position of a position of `s` in `insAt s g x y`. -/
def insIdx (g i : ℕ) : ℕ := if i < g then i else i + 2

theorem idAt_insAt_insIdx {g : ℕ} (hg : g ≤ s.length) (n : ℕ) (a b : α) (i : ℕ) :
    idAt (insAt s g (n, a) (n, b)) (insIdx g i) = idAt s i := by
  rw [idAt_insAt hg]; unfold insIdx; split_ifs <;> first | rfl | omega

theorem idAt_insAt_unIns {g : ℕ} (hg : g ≤ s.length) (n : ℕ) (a b : α) {i : ℕ}
    (hi : i ≠ g ∧ i ≠ g + 1) : idAt (insAt s g (n, a) (n, b)) i = idAt s (unIns g i) := by
  rw [idAt_insAt hg]; unfold unIns; split_ifs <;> first | rfl | omega

/-- **A cup with a fresh id does not change the interleaving of arcs.** -/
theorem ilvArc_insAt_iff {g : ℕ} (hg : g ≤ s.length) {n : ℕ} (hk : ∀ x ∈ s, x.1 ≠ n) (a b : α)
    {c e : ℕ} : IlvArc (insAt s g (n, a) (n, b)) c e ↔ IlvArc s c e := by
  constructor
  · rintro ⟨i, j, k, l, ⟨h1, h2, h3, h4, h5⟩, hc, he⟩
    obtain ⟨a1, a2, a3, a4, a5⟩ := same_insAt_split hg hk a b h4 (by omega) (by omega)
    obtain ⟨b1, b2, b3, b4, b5⟩ := same_insAt_split hg hk a b h5 (by omega) (by omega)
    refine ⟨unIns g i, unIns g j, unIns g k, unIns g l,
      ⟨unIns_lt ⟨a1, a2⟩ ⟨b1, b2⟩ h1, unIns_lt ⟨b1, b2⟩ ⟨a3, a4⟩ h2,
        unIns_lt ⟨a3, a4⟩ ⟨b3, b4⟩ h3, a5, b5⟩, ?_, ?_⟩
    · rw [← idAt_insAt_unIns hg n a b ⟨a1, a2⟩]; exact hc
    · rw [← idAt_insAt_unIns hg n a b ⟨b1, b2⟩]; exact he
  · rintro ⟨i, j, k, l, ⟨h1, h2, h3, h4, h5⟩, hc, he⟩
    refine ⟨insIdx g i, insIdx g j, insIdx g k, insIdx g l,
      ⟨?_, ?_, ?_, same_insAt_of hg hk a b h4, same_insAt_of hg hk a b h5⟩, ?_, ?_⟩
    · unfold insIdx; split_ifs <;> omega
    · unfold insIdx; split_ifs <;> omega
    · unfold insIdx; split_ifs <;> omega
    · rw [idAt_insAt_insIdx hg]; exact hc
    · rw [idAt_insAt_insIdx hg]; exact he

theorem idAt_eq_of_same {i j : ℕ} (h : Same s i j) : idAt s j = idAt s i := h.2.2.symm

/-- Interleaving arcs other than the two arcs at `p`, `p + 1` survive the exchange of `p` and
`p + 1`. -/
theorem ilvArc_swapAt_of {p : ℕ} (hp : p + 1 < s.length) {a b : ℕ} (h : IlvArc s a b)
    (h1 : ¬ (idAt s p = some a ∧ idAt s (p + 1) = some b))
    (h2 : ¬ (idAt s p = some b ∧ idAt s (p + 1) = some a)) : IlvArc (swapAt s p) a b := by
  obtain ⟨i, j, k, l, hx, ha, hb⟩ := h
  have hk : idAt s k = some a := by rw [idAt_eq_of_same hx.2.2.2.1, ha]
  have hl : idAt s l = some b := by rw [idAt_eq_of_same hx.2.2.2.2, hb]
  have hc : ¬ ConsAt (i, j, k, l) p := by
    rintro (⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩) <;> simp only at e1 e2 <;> subst e1
    · exact h1 ⟨ha, e2 ▸ hb⟩
    · exact h2 ⟨hb, e2 ▸ hk⟩
    · exact h1 ⟨hk, e2 ▸ hl⟩
  have hm := tau4_mem_crSet hp (mem_crSet.2 hx) hc
  refine ⟨tau p i, tau p j, tau p k, tau p l, mem_crSet.1 hm, ?_, ?_⟩
  · rw [idAt_swapAt hp, tau_tau]; exact ha
  · rw [idAt_swapAt hp, tau_tau]; exact hb

/-- **The exchange of `p` and `p + 1` does not change the interleaving of arcs other than the
two arcs at `p` and `p + 1`.** -/
theorem ilv2_swapAt_of_ne {p : ℕ} (hp : p + 1 < s.length) {a b : ℕ}
    (h1 : ¬ (idAt s p = some a ∧ idAt s (p + 1) = some b))
    (h2 : ¬ (idAt s p = some b ∧ idAt s (p + 1) = some a)) :
    Ilv2 (swapAt s p) a b ↔ Ilv2 s a b := by
  have hp' : p + 1 < (swapAt s p).length := by simpa using hp
  have e1 : idAt (swapAt s p) p = idAt s (p + 1) := by rw [idAt_swapAt hp, tau_left]
  have e2 : idAt (swapAt s p) (p + 1) = idAt s p := by rw [idAt_swapAt hp, tau_right]
  have back : ∀ {a b : ℕ}, ¬ (idAt s p = some a ∧ idAt s (p + 1) = some b) →
      ¬ (idAt s p = some b ∧ idAt s (p + 1) = some a) → IlvArc (swapAt s p) a b →
        IlvArc s a b := by
    intro a b h1 h2 h
    have := ilvArc_swapAt_of hp' h (by rw [e1, e2]; exact fun ⟨x, y⟩ => h2 ⟨y, x⟩)
      (by rw [e1, e2]; exact fun ⟨x, y⟩ => h1 ⟨y, x⟩)
    rwa [swapAt_swapAt] at this
  constructor
  · rintro (h | h)
    · exact Or.inl (back h1 h2 h)
    · exact Or.inr (back h2 h1 h)
  · rintro (h | h)
    · exact Or.inl (ilvArc_swapAt_of hp h h1 h2)
    · exact Or.inr (ilvArc_swapAt_of hp h h2 h1)

/-- Three positions with the same id in a pairing: two of them coincide. -/
theorem Valid.pos_of_id (hv : Valid s) {i k p a : ℕ} (hi : idAt s i = some a)
    (hk : idAt s k = some a) (hp : idAt s p = some a) (hik : i ≠ k) : p = i ∨ p = k := by
  by_contra h
  rw [not_or] at h
  have s1 : Same s p i := ⟨h.1, by rw [hp]; simp, by rw [hp, hi]⟩
  have s2 : Same s p k := ⟨h.2, by rw [hp]; simp, by rw [hp, hk]⟩
  exact hik (hv.unique s1 s2)

/-- **The arcs at `p` and `p + 1` interleave exactly when `Ilv s p`.** -/
theorem ilv2_iff_ilv (hv : Valid s) {p a b : ℕ} (ha : idAt s p = some a)
    (hb : idAt s (p + 1) = some b) : Ilv2 s a b ↔ Ilv s p := by
  constructor
  · have key : ∀ {a b : ℕ}, idAt s p = some a → idAt s (p + 1) = some b → IlvArc s a b →
        Ilv s p := by
      intro a b ha hb ⟨i, j, k, l, hx, hi, hj⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := hx
      have hk : idAt s k = some a := by rw [idAt_eq_of_same h4, hi]
      have hl : idAt s l = some b := by rw [idAt_eq_of_same h5, hj]
      have e1 := hv.pos_of_id hi hk ha (by omega)
      have e2 := hv.pos_of_id hj hl hb (by omega)
      refine ⟨i, j, k, l, ⟨h1, h2, h3, h4, h5⟩, ?_⟩
      omega
    have key' : ∀ {a b : ℕ}, idAt s p = some a → idAt s (p + 1) = some b → IlvArc s b a →
        Ilv s p := by
      intro a b ha hb ⟨i, j, k, l, hx, hi, hj⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := hx
      have hk : idAt s k = some b := by rw [idAt_eq_of_same h4, hi]
      have hl : idAt s l = some a := by rw [idAt_eq_of_same h5, hj]
      have e1 := hv.pos_of_id hj hl ha (by omega)
      have e2 := hv.pos_of_id hi hk hb (by omega)
      refine ⟨i, j, k, l, ⟨h1, h2, h3, h4, h5⟩, ?_⟩
      omega
    rintro (h | h)
    · exact key ha hb h
    · exact key' ha hb h
  · rintro ⟨i, j, k, l, ⟨h1, h2, h3, h4, h5⟩, h⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨_, _, _, _, ⟨h1, h2, h3, h4, h5⟩, ha, hb⟩
    · refine Or.inr ⟨_, _, _, _, ⟨h1, h2, h3, h4, h5⟩, ?_, ha⟩
      rw [← idAt_eq_of_same h4, hb]
    · refine Or.inl ⟨_, _, _, _, ⟨h1, h2, h3, h4, h5⟩, ?_, ?_⟩
      · rw [← idAt_eq_of_same h4, ha]
      · rw [← idAt_eq_of_same h5, hb]

theorem not_same_of_id_ne {p a b : ℕ} (ha : idAt s p = some a) (hb : idAt s (p + 1) = some b)
    (hab : a ≠ b) : ¬ Same s p (p + 1) := by
  intro h
  rw [h.2.2, hb] at ha
  exact hab (Option.some.inj ha).symm

/-- **A crossing toggles the interleaving of the two arcs it crosses.** -/
theorem ilv2_swapAt_iff (hv : Valid s) {p a b : ℕ} (hp : p + 1 < s.length)
    (ha : idAt s p = some a) (hb : idAt s (p + 1) = some b) (hab : a ≠ b) :
    Ilv2 (swapAt s p) a b ↔ ¬ Ilv2 s a b := by
  have hn := not_same_of_id_ne ha hb hab
  have e1 : idAt (swapAt s p) p = some b := by rw [idAt_swapAt hp, tau_left, hb]
  have e2 : idAt (swapAt s p) (p + 1) = some a := by rw [idAt_swapAt hp, tau_right, ha]
  rw [ilv2_comm, ilv2_iff_ilv (hv.swapAt hp) e1 e2, ilv_swapAt_iff hv hp hn,
    ilv2_iff_ilv hv ha hb]

end Interleaving

/-! ## Reduced diagrams -/

section Reduced

variable (d : α → α)

/-- The unordered pair of strand ids crossed by a move applied to the state `s` (none for a
cup). -/
def xpOf (s : List (ℕ × α)) : Move α → List (Sym2 (Option ℕ))
  | .cup _ _ => []
  | .cross p => [s(idAt s p, idAt s (p + 1))]

/-- The crossings of a diagram applied to the state `s`, as unordered pairs of strand ids. -/
def xps : List (ℕ × α) → List (Move α) → List (Sym2 (Option ℕ))
  | _, [] => []
  | s, m :: D => xpOf s m ++ xps (step d s m) D

theorem xps_append (s : List (ℕ × α)) (D E : List (Move α)) :
    xps d s (D ++ E) = xps d s D ++ xps d (D.foldl (step d) s) E := by
  induction D generalizing s with
  | nil => rfl
  | cons m D ih => simp [xps, ih]

theorem xps_snoc (D : List (Move α)) (m : Move α) :
    xps d [] (D ++ [m]) = xps d [] D ++ xpOf (run d D) m := by
  rw [xps_append]; simp [xps, run]

/-- **Reduced diagrams** ([BE2] §8, before Theorem 8.1): no strand crosses itself and two
distinct strands cross at most once. (Every strand of a diagram of cups and crossings has exactly
one critical point, the minimum of its cup.) -/
def Reduced (D : List (Move α)) : Prop :=
  (xps d [] D).Nodup ∧ ∀ z ∈ xps d [] D, ¬ z.IsDiag

/-- The invariant of `runInv`. -/
structure RunInv (s : List (ℕ × α)) (X : List (Sym2 (Option ℕ))) (n : ℕ) : Prop where
  bound : ∀ z ∈ X, ∀ o ∈ z, ∀ y, o = some y → y < s.length
  parity : ∀ a b, a ≠ b → (Ilv2 s a b ↔ Odd (X.count s(some a, some b)))
  le : cr s ≤ n
  eq_iff : n = cr s ↔ (X.Nodup ∧ ∀ z ∈ X, ¬ z.IsDiag)

theorem idAt_eq_some {s : List (ℕ × α)} {p : ℕ} (hp : p < s.length) :
    idAt s p = some (s[p]'hp).1 := by
  simp [idAt, List.getElem?_eq_getElem hp]

theorem not_ilv2_nil {a b : ℕ} : ¬ Ilv2 ([] : List (ℕ × α)) a b := by
  rintro (⟨i, j, k, l, ⟨-, -, -, h, -⟩, -⟩ | ⟨i, j, k, l, ⟨-, -, -, h, -⟩, -⟩) <;>
    simpa using h.lt_left

theorem cr_nil : cr ([] : List (ℕ × α)) = 0 := by
  simp [cr, crSet]

/-- **Strands and crossings**: along a diagram, two distinct strands interleave exactly when they
have crossed an odd number of times, the crossing number of the pairing is at most the number of
crossings, with equality exactly for reduced diagrams. -/
theorem runInv : ∀ {D : List (Move α)}, Fits 0 D →
    RunInv (run d D) (xps d [] D) (OddMath.SKM.ncr D) := by
  intro D
  induction D using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨by simp [xps], fun a b _ => ?_, by simp [run, cr_nil], ?_⟩
    · simp only [run, List.foldl_nil, xps, List.count_nil]
      exact ⟨fun h => absurd h not_ilv2_nil, fun h => absurd h (by decide)⟩
    · simp [run, cr_nil, xps]
  | append_singleton D m ih =>
    intro hf
    obtain ⟨hfD, hm⟩ := (fits_snoc (d := d)).1 hf
    have I := ih hfD
    have hinv := inv_run (d := d) hfD
    rw [xps_snoc, run_append, OddMath.SKM.ncr_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set s := run d D with hs
    set X := xps d [] D
    cases m with
    | cup g a =>
      simp only [Move.Ok] at hm
      have hk : ∀ x ∈ s, x.1 ≠ s.length := fun x hx => (hinv.2 x hx).ne
      simp only [step, xpOf, List.append_nil, OddMath.SKM.ncr_cons_cup, OddMath.SKM.ncr_nil,
        add_zero]
      refine ⟨fun z hz o ho y hy => ?_, fun a' b' hab => ?_, ?_, ?_⟩
      · rw [length_insAt s hm]; have := I.bound z hz o ho y hy; omega
      · rw [← I.parity a' b' hab, Ilv2, Ilv2, ilvArc_insAt_iff hm hk, ilvArc_insAt_iff hm hk]
      · rw [cr_insAt hm hk]; exact I.le
      · rw [cr_insAt hm hk]; exact I.eq_iff
    | cross p =>
      simp only [Move.Ok] at hm
      have hp0 : p < s.length := by omega
      obtain ⟨a0, ha0⟩ : ∃ a0, idAt s p = some a0 := ⟨_, idAt_eq_some hp0⟩
      obtain ⟨b0, hb0⟩ : ∃ b0, idAt s (p + 1) = some b0 := ⟨_, idAt_eq_some hm⟩
      have ha0l : a0 < s.length := by
        rw [idAt_eq_some hp0, Option.some.injEq] at ha0
        rw [← ha0]; exact hinv.2 _ (List.getElem_mem _)
      have hb0l : b0 < s.length := by
        rw [idAt_eq_some hm, Option.some.injEq] at hb0
        rw [← hb0]; exact hinv.2 _ (List.getElem_mem _)
      simp only [step, xpOf, ha0, hb0, OddMath.SKM.ncr_cons_cross, OddMath.SKM.ncr_nil, zero_add]
      set z : Sym2 (Option ℕ) := s(some a0, some b0) with hz
      have hcount : ∀ w, (X ++ [z]).count w = X.count w + if z = w then 1 else 0 := by
        intro w; rw [List.count_append, List.count_singleton]
        by_cases h : z = w
        · simp [h]
        · simp [h]
      refine ⟨fun z' hz' o ho y hy => ?_, fun a b hab => ?_, ?_, ?_⟩
      · rw [length_swapAt]
        rcases List.mem_append.1 hz' with h | h
        · exact I.bound z' h o ho y hy
        · rw [List.mem_singleton] at h
          subst h
          rw [hz, Sym2.mem_iff] at ho
          rcases ho with rfl | rfl <;> cases hy <;> assumption
      · rw [hcount]
        by_cases hzw : z = s(some a, some b)
        · simp only [hzw, ite_true]
          rw [Nat.odd_add_one, ← I.parity a b hab]
          rw [hz, Sym2.eq_iff] at hzw
          simp only [Option.some.injEq] at hzw
          rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ilv2_swapAt_iff hinv.1 hm ha0 hb0 hab
          · rw [ilv2_comm, ilv2_swapAt_iff hinv.1 hm ha0 hb0 (Ne.symm hab), ilv2_comm]
        · simp only [hzw, ite_false, add_zero]
          rw [← I.parity a b hab]
          refine ilv2_swapAt_of_ne hm (fun ⟨h1, h2⟩ => hzw ?_) (fun ⟨h1, h2⟩ => hzw ?_)
          · rw [ha0] at h1; rw [hb0] at h2; rw [hz, h1, h2]
          · rw [ha0] at h1; rw [hb0] at h2; rw [hz, h1, h2, Sym2.eq_swap]
      · by_cases hab : a0 = b0
        · subst hab
          have hsame : Same s p (p + 1) := ⟨by omega, by rw [ha0]; simp, by rw [ha0, hb0]⟩
          rw [cr_swapAt_of_same hinv.1 hsame]; have := I.le; omega
        · by_cases hil : Ilv s p
          · have := cr_swapAt_add_one hinv.1 hil; have := I.le; omega
          · rw [cr_swapAt_of_not_ilv hinv.1 hm (not_same_of_id_ne ha0 hb0 hab) hil]
            have := I.le; omega
      · by_cases hab : a0 = b0
        · subst hab
          have hsame : Same s p (p + 1) := ⟨by omega, by rw [ha0]; simp, by rw [ha0, hb0]⟩
          rw [cr_swapAt_of_same hinv.1 hsame]
          have := I.le
          refine ⟨fun h => by omega, fun h => absurd (h.2 z (by simp)) ?_⟩
          rw [hz, Sym2.mk_isDiag_iff]; exact not_not.2 rfl
        · by_cases hil : Ilv s p
          · have h1 := cr_swapAt_add_one hinv.1 hil
            have := I.le
            refine ⟨fun h => by omega, fun h => ?_⟩
            exfalso
            have hodd := (I.parity a0 b0 hab).1 ((ilv2_iff_ilv hinv.1 ha0 hb0).2 hil)
            have hmem : z ∈ X := List.count_pos_iff.1 (Nat.pos_of_ne_zero fun e => by
              rw [e] at hodd; exact (Nat.not_odd_zero hodd))
            exact (List.nodup_append.1 h.1).2.2 z hmem z (by simp) rfl
          · rw [cr_swapAt_of_not_ilv hinv.1 hm (not_same_of_id_ne ha0 hb0 hab) hil]
            have hev : ¬ Odd (X.count z) := fun h =>
              hil ((ilv2_iff_ilv hinv.1 ha0 hb0).1 ((I.parity a0 b0 hab).2 h))
            constructor
            · intro h
              obtain ⟨hn, hd⟩ := I.eq_iff.1 (by omega)
              have hz0 : X.count z = 0 := by
                have := List.nodup_iff_count_le_one.1 hn z
                rcases (show X.count z = 0 ∨ X.count z = 1 by omega) with h | h
                · exact h
                · exact absurd (by rw [h]; decide) hev
              refine ⟨List.nodup_append.2 ⟨hn, List.nodup_singleton _, ?_⟩, ?_⟩
              · intro x hx y hy e
                rw [List.mem_singleton] at hy
                subst hy e
                exact (List.count_eq_zero.1 hz0) hx
              · intro w hw
                rcases List.mem_append.1 hw with hw | hw
                · exact hd w hw
                · rw [List.mem_singleton] at hw
                  rw [hw, hz, Sym2.mk_isDiag_iff, Option.some.injEq]; exact hab
            · intro h
              have := I.eq_iff.2 ⟨(List.nodup_append.1 h.1).1,
                fun w hw => h.2 w (List.mem_append_left _ hw)⟩
              omega

/-- **A diagram has at least as many crossings as its pairing.** -/
theorem cr_run_le_ncr {D : List (Move α)} (hf : Fits 0 D) : cr (run d D) ≤ OddMath.SKM.ncr D :=
  (runInv d hf).le

/-- **A diagram is reduced if and only if it has as many crossings as the crossing number of its
pairing** (the minimal number of crossings). -/
theorem reduced_iff {D : List (Move α)} (hf : Fits 0 D) :
    Reduced d D ↔ OddMath.SKM.ncr D = cr (run d D) :=
  (runInv d hf).eq_iff.symm

theorem ncr_canon_le : ∀ (n : ℕ) {s : List (ℕ × α)}, s.length + cr s < n → Valid s →
    OddMath.SKM.ncr (canon s) ≤ cr s := by
  intro n
  induction n with
  | zero => intro s h; omega
  | succ n ih =>
    intro s hn hv
    by_cases hadj : ∃ r, Same s r (r + 1)
    · classical
      obtain ⟨r, hr, hmin⟩ : ∃ r, Same s r (r + 1) ∧ ∀ r' < r, ¬ Same s r' (r' + 1) :=
        ⟨Nat.find hadj, Nat.find_spec hadj, fun _ => Nat.find_min hadj⟩
      have hl2 : r + 2 ≤ s.length := hr.lt_right
      have h1 := cr_rmAt_le hl2
      have h2 := ih (s := rmAt s r) (by rw [length_rmAt s hl2]; omega) (hv.rmAt hr)
      rw [canon_adj hv hr hmin, OddMath.SKM.ncr_append]
      simp only [OddMath.SKM.ncr_cons_cup, OddMath.SKM.ncr_nil, add_zero]
      omega
    · have hno : ∀ r, ¬ Same s r (r + 1) := fun r hr => hadj ⟨r, hr⟩
      by_cases hne : s = []
      · subst hne; rw [canon_nil]; simp
      obtain ⟨q, ho, hc, hq, -⟩ := canon_cross hv hno hne
      have hilv := ilv_of_opn_cls hv (hno q) ho hc
      have h1 := cr_swapAt_add_one hv hilv
      have h2 := ih (s := swapAt s q) (by rw [length_swapAt]; omega) (hv.swapAt hilv.lt)
      rw [hq, OddMath.SKM.ncr_append]
      simp only [OddMath.SKM.ncr_cons_cross, OddMath.SKM.ncr_nil, zero_add]
      omega

/-- **The canonical diagram of a pairing is reduced**, with as many crossings as the crossing
number of the pairing. -/
theorem reduced_canon {s : List (ℕ × α)} (hv : Valid s) (hl : Lettered d s) :
    Fits 0 (canon s) ∧ Reduced d (canon s) ∧ OddMath.SKM.ncr (canon s) = cr s := by
  obtain ⟨hf, hiso⟩ := run_canon (d := d) _ (Nat.lt_succ_self _) hv hl
  have e : cr (run d (canon s)) = cr s := le_antisymm (cr_le_of_iso hiso) (cr_le_of_iso hiso.symm)
  have h1 := ncr_canon_le _ (Nat.lt_succ_self _) hv
  have h2 := cr_run_le_ncr d hf
  refine ⟨hf, (reduced_iff d hf).2 (by omega), by omega⟩

theorem Reduced.of_append {D E : List (Move α)} (h : Reduced d (D ++ E)) : Reduced d D := by
  obtain ⟨hn, hd⟩ := h
  rw [xps_append] at hn hd
  exact ⟨(List.nodup_append.1 hn).1, fun z hz => hd z (List.mem_append_left _ hz)⟩

/-- **A reduced diagram is equivalent to the canonical diagram of its pairing** (by isotopies and
braid moves, `Chord.Equiv`). -/
theorem equiv_canon_of_reduced : ∀ {D : List (Move α)}, Fits 0 D → Reduced d D →
    Equiv D (canon (run d D)) := by
  intro D
  induction D using List.reverseRecOn with
  | nil => intro _ _; rw [run, List.foldl_nil, canon_nil]
  | append_singleton D m ih =>
    intro h hr
    obtain ⟨hfD, hm⟩ := (fits_snoc (d := d)).1 h
    have hi := inv_run (d := d) hfD
    have he' := (ih hfD (hr.of_append d)).append_right [m]
    have I := runInv d hfD
    obtain ⟨hn, hdg⟩ := hr
    rw [xps_snoc] at hn hdg
    rw [run_append, List.foldl_cons, List.foldl_nil]
    set s := run d D
    cases m with
    | cup g a =>
      simp only [Move.Ok] at hm
      have hk : ∀ x ∈ s, x.1 ≠ s.length := fun x hx => (hi.2 x hx).ne
      have hs : Same (step d s (.cup g a)) g (g + 1) :=
        (same_insAt_iff hm hk a (d a)).2 (Or.inl ⟨rfl, rfl⟩)
      have c := canon_cup ((hi.step (d := d) (m := .cup g a) hm).1) hs
      have e1 : rmAt (step d s (.cup g a)) g = s := rmAt_insAt s g _ _ hm
      have e2 : ((step d s (.cup g a))[g]'hs.lt_left).2 = a := by
        have : (step d s (.cup g a))[g]? = some (s.length, a) := by
          rw [step, getElem?_insAt s hm]; simp
        rw [List.getElem?_eq_getElem hs.lt_left] at this
        rw [Option.some.inj this]
      rw [e1, e2] at c
      exact he'.trans c.symm
    | cross p =>
      simp only [Move.Ok] at hm
      have hp0 : p < s.length := by omega
      obtain ⟨a0, ha0⟩ : ∃ a0, idAt s p = some a0 := ⟨_, idAt_eq_some hp0⟩
      obtain ⟨b0, hb0⟩ : ∃ b0, idAt s (p + 1) = some b0 := ⟨_, idAt_eq_some hm⟩
      simp only [xpOf, ha0, hb0] at hn hdg
      have hab : a0 ≠ b0 := by
        intro e; subst e
        exact hdg _ (List.mem_append_right _ (List.mem_singleton_self _))
          ((Sym2.mk_isDiag_iff).2 rfl)
      have hsame : ¬ Same s p (p + 1) := not_same_of_id_ne ha0 hb0 hab
      have hilv : ¬ Ilv s p := by
        intro hil
        have hodd := (I.parity a0 b0 hab).1 ((ilv2_iff_ilv hi.1 ha0 hb0).2 hil)
        have hmem : s(some a0, some b0) ∈ xps d [] D := List.count_pos_iff.1
          (Nat.pos_of_ne_zero fun e => by rw [e] at hodd; exact Nat.not_odd_zero hodd)
        exact (List.nodup_append.1 hn).2.2 _ hmem _ (List.mem_singleton_self _) rfl
      have hilv' : Ilv (swapAt s p) p := (ilv_swapAt_iff hi.1 hm hsame).2 hilv
      have c := canon_ilv (hi.1.swapAt hm) hilv'
      rw [swapAt_swapAt] at c
      exact he'.trans c.symm

end Reduced

end StringDiagrams.Chord
