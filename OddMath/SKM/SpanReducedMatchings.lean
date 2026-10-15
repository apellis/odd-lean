/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanDecoratedMatchings

/-!
# Every pairing is the pairing of a reduced matching ([BE2] Theorem 8.1)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 8.1, in the
form of the paper: a choice of reduced `(a, b)`-matchings representing every equivalence class of
reduced matchings, decorated with dots at distinguished points, spans
`Hom(E_a 1_λ, E_b 1_λ)` over `SYM`.

`theorem_8_1_of_pairings` assumes that the chosen matchings represent every *pairing* of `a* b`.
The missing step is that every pairing is realised by a reduced matching
(`exists_reduced_matching`): put the canonical chord diagram of the pairing to the right of `a`
and cap `a` against the new `a*` with nested caps. Each strand of the result contains exactly one
arc of the canonical diagram, so the matching is reduced.

## Main results

* `Chord.reduced_of_length_xs_eq_cr`: a two-sided matching with as many crossings as the crossing
  number of its pairing is reduced.
* `exists_reduced_matching`: **every pairing of `a* b` is the pairing of a reduced
  `(a, b)`-matching.**
* `theorem_8_1`: **[BE2] Theorem 8.1** (for any bottom boundary).
-/

namespace StringDiagrams.Chord

variable {α : Type*} {s : List (ℕ × α)}

/-! ## Reduced matchings and the crossing number -/

theorem eq_or_same_of_idD_eq {x y : ℕ} (hx : x < s.length) (hy : y < s.length)
    (h : idD s x = idD s y) : x = y ∨ Same s x y := by
  by_cases e : x = y
  · exact Or.inl e
  · exact Or.inr ⟨e, idAt_ne_none_iff.2 hx, by rw [idAt_eq_idD hx, idAt_eq_idD hy, h]⟩

/-- A crossing of a pairing is determined by the ids of its two arcs. -/
theorem injOn_crSet (hv : Valid s) :
    Set.InjOn (fun q : ℕ × ℕ × ℕ × ℕ => s(idD s q.1, idD s q.2.1)) (crSet s) := by
  rintro ⟨i, j, k, l⟩ hq ⟨i', j', k', l'⟩ hq' e
  simp only [Finset.mem_coe, mem_crSet] at hq hq'
  obtain ⟨hij, hjk, hkl, hik, hjl⟩ := hq
  obtain ⟨hij', hjk', hkl', hik', hjl'⟩ := hq'
  simp only [Sym2.eq_iff] at e
  have pi := hik.lt_left; have pj := hjl.lt_left; have pi' := hik'.lt_left
  have pj' := hjl'.lt_left
  rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hii : i = i' := by
      rcases eq_or_same_of_idD_eq pi pi' e1 with h | h
      · exact h
      · have h1 := hv.unique hik h
        have h2 := hv.unique hik' h.symm
        omega
    have hjj : j = j' := by
      rcases eq_or_same_of_idD_eq pj pj' e2 with h | h
      · exact h
      · have h1 := hv.unique hjl h
        have h2 := hv.unique hjl' h.symm
        omega
    subst hii hjj
    rw [hv.unique hik hik', hv.unique hjl hjl']
  · exfalso
    rcases eq_or_same_of_idD_eq pi pj' e1 with h1 | h1 <;>
      rcases eq_or_same_of_idD_eq pj pi' e2 with h2 | h2
    · omega
    · have := hv.unique hjl h2; omega
    · have e3 := hv.unique hik h1
      subst e3
      have := hv.unique hjl' hik.symm
      omega
    · have e3 := hv.unique hik h1
      have e4 := hv.unique hjl h2
      subst e3 e4
      have := hv.unique hjl' hik.symm
      omega

section Model

variable {d : α → α}

/-- **A two-sided matching with as many crossings as the crossing number of its pairing is
reduced**: no strand crosses itself and two strands cross at most once (the converse of
`length_xs_le_cr`). -/
theorem reduced_of_length_xs_eq_cr {T : TState α} (I : TInv T) (h : T.xs.length = cr T.st) :
    T.xs.Nodup ∧ ∀ z ∈ T.xs, ¬ z.IsDiag := by
  classical
  set f : ℕ × ℕ × ℕ × ℕ → Sym2 ℕ := fun q => s(idD T.st q.1, idD T.st q.2.1) with hf
  have hS : ∀ q ∈ crSet T.st, ¬ (f q).IsDiag ∧ f q ∈ T.xs := by
    rintro ⟨i, j, k, l⟩ hq
    obtain ⟨hij, hjk, hkl, hik, hjl⟩ : Cr4 T.st i j k l := mem_crSet.1 hq
    have hi := idAt_eq_idD hik.lt_left
    have hj := idAt_eq_idD hjl.lt_left
    have hne : idD T.st i ≠ idD T.st j := by
      intro e
      have hs : Same T.st i j := ⟨by omega, idAt_ne_none_iff.2 hik.lt_left, by rw [hi, hj, e]⟩
      have := I.valid.unique hik hs
      omega
    refine ⟨fun hd => hne (Sym2.mk_isDiag_iff.1 hd), ?_⟩
    have hil : Ilv2 T.st (idD T.st i) (idD T.st j) :=
      Or.inl ⟨i, j, k, l, ⟨hij, hjk, hkl, hik, hjl⟩, hi, hj⟩
    exact List.count_pos_iff.1 ((I.parity _ _ hne).1 hil).pos
  have hsub : (crSet T.st).image f ⊆ T.xs.toFinset := fun z hz => by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hz
    exact List.mem_toFinset.2 (hS q hq).2
  have hcard : ((crSet T.st).image f).card = cr T.st :=
    Finset.card_image_of_injOn (injOn_crSet I.valid)
  have h1 : T.xs.length ≤ T.xs.toFinset.card := by
    rw [h, ← hcard]; exact Finset.card_le_card hsub
  have hnd : T.xs.Nodup := by
    rw [List.card_toFinset] at h1
    rw [← (List.dedup_sublist T.xs).eq_of_length_le h1]
    exact List.nodup_dedup _
  have heq : (crSet T.st).image f = T.xs.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, ← h, List.toFinset_card_of_nodup hnd])
  refine ⟨hnd, fun z hz => ?_⟩
  have hz' : z ∈ (crSet T.st).image f := by rw [heq]; exact List.mem_toFinset.2 hz
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hz'
  exact (hS q hq).1

/-- A cap applies to a state if it applies to a state with the same pairing. -/
theorem okCap_of_iso {s s' : List (ℕ × α)} (h : Iso s s') {k g : ℕ}
    (hok : (TMove.cap g : TMove α).Ok d k s') : (TMove.cap g : TMove α).Ok d k s := by
  obtain ⟨A', B', hA', hB', hl, hne⟩ := hok
  have hr' : k + g + 1 < s'.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hB'; cases hB'
  have hr : k + g + 1 < s.length := h.length_eq ▸ hr'
  have eA : s'[k + g] = A' := by rw [List.getElem?_eq_getElem (by omega)] at hA'; simpa using hA'
  have eB : s'[k + g + 1] = B' := by rw [List.getElem?_eq_getElem hr'] at hB'; simpa using hB'
  refine ⟨s[k + g], s[k + g + 1], List.getElem?_eq_getElem _, List.getElem?_eq_getElem _, ?_, ?_⟩
  · rw [h.snd_getElem (by omega) (by omega), h.snd_getElem hr hr', eA, eB, hl]
  · intro e
    have hs : Same s (k + g) (k + g + 1) := ⟨by omega, idAt_ne_none_iff.2 (by omega), by
      rw [idAt_eq_some (by omega), idAt_eq_some hr, e]⟩
    have hs' := ((h.2 _ _).1 hs).2.2
    rw [idAt_eq_some (by omega), idAt_eq_some hr', eA, eB] at hs'
    exact hne (Option.some.inj hs')

end Model

/-! ## States with a common prefix -/

theorem insAt_append_left {β : Type*} (P w : List β) (g : ℕ) (x y : β) :
    insAt (P ++ w) (P.length + g) x y = P ++ insAt w g x y := by
  have h1 : (P ++ w).take (P.length + g) = P ++ w.take g := by rw [List.take_append]; simp
  have h2 : (P ++ w).drop (P.length + g) = w.drop g := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]; simp
  rw [insAt, h1, h2, insAt]; simp

theorem swapAt_append_left (P w : List (ℕ × α)) {p : ℕ} (hp : p + 1 < w.length) :
    swapAt (P ++ w) (P.length + p) = P ++ swapAt w p := by
  obtain ⟨U, A, B, V, rfl, rfl⟩ := exists_mid hp
  have e1 : P ++ (U ++ [A, B] ++ V) = (P ++ U) ++ A :: B :: V := by simp
  have e2 : U ++ [A, B] ++ V = U ++ A :: B :: V := by simp
  rw [e1, show P.length + U.length = (P ++ U).length by simp, OddMath.SKM.swapAt_mid, e2,
    OddMath.SKM.swapAt_mid]
  simp

end StringDiagrams.Chord

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation
open StringDiagrams.Chord (Move Fits run Iso rl rlId TMove TState tStep tRun TFits TInv ncr₂ jn idD
  Same Valid Lettered canon insAt swapAt)

universe u v w

variable {I : Type u}

/-! ## The nested cups -/

/-- The strands `x_0, …, x_{n-1}` of the nested cups `cupA w`, the strand `i` with id `2 i`. -/
def cupLeft (w : List (Letter I)) : List (ℕ × Letter I) := w.mapIdx fun i x => (2 * i, x)

/-- The dual letter, keeping the strand id. -/
def flipSnd (x : ℕ × Letter I) : ℕ × Letter I := (x.1, flipL x.2)

@[simp] theorem length_cupLeft (w : List (Letter I)) : (cupLeft w).length = w.length := by
  simp [cupLeft]

theorem cupMoves_append (x : Letter I) : ∀ w : List (Letter I),
    cupMoves (w ++ [x]) = cupMoves w ++ [.cup w.length x]
  | [] => rfl
  | y :: w => by
    simp only [List.cons_append, cupMoves, cupMoves_append x w, List.map_append, List.map_cons,
      List.map_nil, shiftM, List.length_cons, List.cons.injEq, true_and, List.append_cancel_left_eq,
      Move.cup.injEq, and_true]
    omega

/-- **The state of the nested cups**: `x_0 ⋯ x_{n-1} x_{n-1}* ⋯ x_0*`, the strand `i` joining the
positions `i` and `2n - 1 - i`. -/
theorem run_cupMoves (w : List (Letter I)) :
    run flipL (cupMoves w) = cupLeft w ++ (cupLeft w).reverse.map flipSnd := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
    rw [cupMoves_append, Chord.run_append, ih]
    have hlen : (cupLeft w ++ (cupLeft w).reverse.map flipSnd).length = 2 * w.length := by
      simp; omega
    simp only [List.foldl_cons, List.foldl_nil, Chord.step, hlen]
    have e := Chord.insAt_append_left (cupLeft w) ((cupLeft w).reverse.map flipSnd) 0
      (2 * w.length, x) (2 * w.length, flipL x)
    simp only [length_cupLeft, add_zero] at e
    rw [e]
    simp [cupLeft, List.mapIdx_append, Chord.insAt, flipSnd]

/-! ## The canonical diagram to the right of the bottom boundary -/

/-- The strand ids shifted by `N`. -/
def shId (N : ℕ) (x : ℕ × Letter I) : ℕ × Letter I := (N + x.1, x.2)

/-- The cups and crossings of a chord diagram `D`, placed `o` positions to the right, as moves
of a two-sided matching. -/
def mvMoves (o : ℕ) (D : List (Move (Letter I))) : List (TMove (Letter I)) :=
  D.map fun m => .mv (shiftM o m)

theorem ncr₂_mvMoves (o : ℕ) (D : List (Move (Letter I))) : ncr₂ (mvMoves o D) = ncr D := by
  rw [ncr₂, mvMoves, List.countP_map, ncr]
  congr 1
  funext m
  rcases m with ⟨g, x⟩ | p <;> rfl

theorem tFits_append_at (k : ℕ) : ∀ (T : TState (Letter I)) (R R' : List (TMove (Letter I))),
    TFits flipL k T (R ++ R') ↔ TFits flipL k T R ∧ TFits flipL k (tRun flipL k T R) R'
  | _, [], _ => by simp [Chord.TFits, Chord.tRun]
  | T, m :: R, R' => by
    simp only [List.cons_append, Chord.TFits, tFits_append_at k _ R R', and_assoc]
    rfl

/-- **A chord diagram to the right of a two-sided matching**: the cups and crossings of `D`,
placed after the strands `P`, act on the states as on `P` followed by the state of `D`. -/
theorem mvMoves_spec (k o N : ℕ) (P : List (ℕ × Letter I)) (hP : ∀ x ∈ P, x.1 < N)
    (hPl : P.length = k + o) : ∀ (D : List (Move (Letter I))) (T : TState (Letter I))
    (v : List (ℕ × Letter I)), TInv T → Chord.Inv v → Fits v.length D →
    Iso T.st (P ++ v.map (shId N)) →
    TFits flipL k T (mvMoves o D) ∧ TInv (tRun flipL k T (mvMoves o D)) ∧
      Iso (tRun flipL k T (mvMoves o D)).st (P ++ (D.foldl (Chord.step flipL) v).map (shId N))
  | [], _, _, I, _, _, h => ⟨trivial, I, h⟩
  | m :: D, T, v, I, hv, hf, h => by
    have hlen : T.st.length = P.length + v.length := by rw [h.length_eq]; simp
    have hok : (TMove.mv (shiftM o m)).Ok flipL k T.st := by
      rcases m with ⟨g, a⟩ | p
      · have := hf.1; simp only [Move.Ok] at this; show k + (o + g) ≤ _; omega
      · have := hf.1; simp only [Move.Ok] at this; show k + (o + p) + 1 < _; omega
    have hiso : Iso (tStep flipL k T (.mv (shiftM o m))).st
        (P ++ (Chord.step flipL v m).map (shId N)) := by
      rcases m with ⟨g, a⟩ | p
      · have hg : g ≤ v.length := hf.1
        have e : P ++ (Chord.step flipL v (.cup g a)).map (shId N) =
            insAt (P ++ v.map (shId N)) (P.length + g) (N + v.length, a)
              (N + v.length, flipL a) := by
          rw [Chord.insAt_append_left]; simp only [Chord.step, Chord.map_insAt]; rfl
        rw [e]
        show Iso (insAt T.st (k + (o + g)) (T.nxt, a) (T.nxt, flipL a)) _
        rw [show k + (o + g) = P.length + g by omega]
        refine h.insAt (by omega) (fun x hx => (I.fresh x hx).ne) (fun x hx => ?_) a (flipL a)
        rcases List.mem_append.1 hx with hx | hx
        · have := hP x hx; omega
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          have := hv.2 y hy; simp only [shId]; omega
      · have hp : p + 1 < v.length := hf.1
        have e : P ++ (Chord.step flipL v (.cross p)).map (shId N) =
            swapAt (P ++ v.map (shId N)) (P.length + p) := by
          rw [Chord.swapAt_append_left _ _ (by simpa using hp)]
          simp only [Chord.step, Chord.map_swapAt]
        rw [e]
        show Iso (swapAt T.st (k + (o + p))) _
        rw [show k + (o + p) = P.length + p by omega]
        exact h.swapAt _
    obtain ⟨h1, h2, h3⟩ := mvMoves_spec k o N P hP hPl D _ _ (I.step hok)
      (hv.step (d := flipL) hf.1) (by rw [Chord.length_step]; exact hf.2) hiso
    exact ⟨⟨hok, h1⟩, h2, h3⟩

/-! ## Capping the bottom boundary against its dual -/

/-- The nested caps `cap (n - 1), …, cap 0`. -/
def nestCaps : ℕ → List (TMove (Letter I))
  | 0 => []
  | n + 1 => .cap n :: nestCaps n

theorem ncr₂_nestCaps : ∀ n : ℕ, ncr₂ (nestCaps (I := I) n) = 0
  | 0 => rfl
  | n + 1 => by rw [nestCaps, ncr₂_cons, ncr₂_nestCaps n]; rfl

theorem foldl_tLet_nestCaps (b : List (Letter I)) (a : List (Letter I)) :
    (nestCaps a.length).foldl tLet (a ++ dualW a ++ b) = b := by
  induction a using List.reverseRecOn with
  | nil => rfl
  | append_singleton a x ih =>
    have e : a ++ [x] ++ dualW (a ++ [x]) ++ b = a ++ x :: flipL x :: (dualW a ++ b) := by
      simp [dualW]
    rw [List.length_append, List.length_singleton, nestCaps, List.foldl_cons, e,
      (tmLay_cap a (dualW a ++ b) x (flipL x)).2, ← List.append_assoc, ih]

/-- The strand ids renamed by `G`. -/
def mapId (G : ℕ → ℕ) (x : ℕ × Letter I) : ℕ × Letter I := (G x.1, x.2)

/-- **Nested caps joining the strands `Q` of the nested cups to the strands `tr` on their right.**
The state is `tp ++ Q ++ Q* ++ tr` (strand ids renamed by `G`), where the strands `Q` and `Q*` are
joined by nested cups and `Q` has the letters of the first strands of `tr`. Capping `Q*` against
`tr` joins the strand of each point of `Q` to the corresponding point of `tr`, so that afterwards
the state is `tp ++ tr`, with the ids renamed injectively. -/
theorem nestCaps_spec : ∀ (Q tp tr : List (ℕ × Letter I)) (G : ℕ → ℕ) (T : TState (Letter I))
    (k : ℕ), k = tp.length + Q.length → Q.length ≤ tr.length →
    Q.map Prod.snd = (tr.take Q.length).map Prod.snd → (Q.map Prod.fst).Nodup →
    (∀ q ∈ Q, ∀ x ∈ tp ++ tr, G x.1 ≠ q.1) →
    (∀ x ∈ tp ++ tr, ∀ y ∈ tp ++ tr, G x.1 = G y.1 → x.1 = y.1) →
    Iso T.st (tp.map (mapId G) ++ Q ++ Q.reverse.map flipSnd ++ tr.map (mapId G)) →
    ∃ G' : ℕ → ℕ, (∀ x ∈ tp ++ tr, ∀ y ∈ tp ++ tr, G' x.1 = G' y.1 → x.1 = y.1) ∧
      TFits flipL k T (nestCaps Q.length) ∧
      Iso (tRun flipL k T (nestCaps Q.length)).st ((tp ++ tr).map (mapId G'))
  | [], tp, tr, G, T, k, _, _, _, _, _, hG, h => ⟨G, hG, trivial, by show Iso T.st _; simpa using h⟩
  | _ :: _, _, [], _, _, _, _, hl, _, _, _, _, _ => by simp at hl
  | q :: Q, tp, τ :: tr, G, T, k, hk, hl, hlet, hnd, hQ, hG, h => by
    simp only [List.length_cons, List.take_succ_cons, List.map_cons, List.cons.injEq] at hlet
    obtain ⟨hq2, hlet⟩ := hlet
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hq1, hnd⟩ := hnd
    have hτ : G τ.1 ≠ q.1 := hQ q (by simp) τ (by simp)
    set Pf := tp.map (mapId G) ++ q :: Q ++ Q.reverse.map flipSnd with hPf
    have hrep : tp.map (mapId G) ++ (q :: Q) ++ (q :: Q).reverse.map flipSnd ++
        (τ :: tr).map (mapId G) = Pf ++ [flipSnd q, mapId G τ] ++ tr.map (mapId G) := by
      simp [Pf]
    have hpos : k + Q.length = Pf.length := by simp [Pf] at hk ⊢; omega
    rw [hrep] at h
    have hok : (TMove.cap Q.length).Ok flipL k T.st := by
      refine Chord.okCap_of_iso h ⟨flipSnd q, mapId G τ, ?_, ?_, ?_, ?_⟩
      · rw [hpos]; simp
      · rw [hpos]; simp
      · simp [flipSnd, mapId, hq2]
      · simpa [flipSnd, mapId] using hτ.symm
    set G' : ℕ → ℕ := fun x => rlId (G τ.1) q.1 (G x) with hG'
    have hjn : jn (Pf ++ [flipSnd q, mapId G τ] ++ tr.map (mapId G)) Pf.length =
        (tp ++ [τ]).map (mapId G') ++ Q ++ Q.reverse.map flipSnd ++ tr.map (mapId G') := by
      rw [Chord.jn_mid]
      have e1 : (tp.map (mapId G)).map (rl (G τ.1) q.1) = tp.map (mapId G') := by
        rw [List.map_map]; rfl
      have e2 : rl (G τ.1) q.1 q = mapId G' τ := by
        rw [Chord.rl_of_ne hτ.symm]
        simp only [mapId, G', rlId, ↓reduceIte]
        exact Prod.ext rfl hq2
      have e3 : Q.map (rl (G τ.1) q.1) = Q :=
        Chord.map_rl_of_forall_ne fun x hx => (hQ x (by simp [hx]) τ (by simp)).symm
      have e4 : (Q.reverse.map flipSnd).map (rl (G τ.1) q.1) = Q.reverse.map flipSnd := by
        refine Chord.map_rl_of_forall_ne fun x hx => ?_
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact (hQ y (by simp at hy; simp [hy]) τ (by simp)).symm
      have e5 : (tr.map (mapId G)).map (rl (G τ.1) q.1) = tr.map (mapId G') := by
        rw [List.map_map]; rfl
      show (Pf ++ tr.map (mapId G)).map (rl (G τ.1) q.1) = _
      rw [List.map_append, hPf, List.map_append, List.map_append, List.map_cons, e1, e2, e3, e4,
        e5]
      simp
    have hiso : Iso (tStep flipL k T (.cap Q.length)).st
        ((tp ++ [τ]).map (mapId G') ++ Q ++ Q.reverse.map flipSnd ++ tr.map (mapId G')) := by
      rw [← hjn]
      show Iso (jn T.st (k + Q.length)) _
      rw [hpos]
      exact h.jn (by rw [h.length_eq]; simp)
    have hmem : ∀ x, x ∈ (tp ++ [τ]) ++ tr ↔ x ∈ tp ++ τ :: tr := by simp
    obtain ⟨G'', hG'', hfit, hiso''⟩ := nestCaps_spec Q (tp ++ [τ]) tr G' _ k
      (by simp at hk ⊢; omega) (by simp at hl; omega) hlet hnd
      (fun q' hq' x hx => by
        rw [hmem] at hx
        simp only [G', rlId]
        split_ifs
        · intro e; exact hq1 (List.mem_map.2 ⟨q', hq', e.symm⟩)
        · exact hQ q' (by simp [hq']) x hx)
      (fun x hx y hy e => by
        rw [hmem] at hx hy
        simp only [G', rlId] at e
        split_ifs at e with h1 h2 h2
        · exact hG x hx y hy (h1.trans h2.symm)
        · exact absurd e.symm (hQ q (by simp) y hy)
        · exact absurd e (hQ q (by simp) x hx)
        · exact hG x hx y hy e)
      hiso
    refine ⟨G'', fun x hx y hy => hG'' x ((hmem x).2 hx) y ((hmem y).2 hy), ⟨hok, hfit⟩, ?_⟩
    have e : (tp ++ [τ]) ++ tr = tp ++ τ :: tr := by simp
    rw [← e]
    exact hiso''

/-! ## Every pairing is the pairing of a reduced matching -/

theorem map_fst_cupLeft (w : List (Letter I)) :
    (cupLeft w).map Prod.fst = (List.range w.length).map (2 * ·) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [cupLeft]

theorem map_snd_cupLeft (w : List (Letter I)) : (cupLeft w).map Prod.snd = w := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [cupLeft]

/-- **Every pairing of `a* b` is the pairing of a reduced `(a, b)`-matching** ([BE2] §8): put the
canonical chord diagram of the pairing to the right of `a`, and cap `a` against the `a*` of the
pairing by nested caps. Every strand of this matching contains exactly one arc of the canonical
diagram, so it has as many crossings as the crossing number of its pairing, and is reduced. -/
theorem exists_reduced_matching {a b : List (Letter I)} {s : List (ℕ × Letter I)} (hv : Valid s)
    (hl : Lettered flipL s) (hs : s.map Prod.snd = dualW a ++ b) :
    ∃ R, IsMatching₂ a b R ∧ Reduced₂ a R ∧ Iso (pairing₂ a R) s := by
  obtain ⟨hf, hiso⟩ := Chord.run_canon (d := flipL) _ (Nat.lt_succ_self _) hv hl
  obtain ⟨-, -, hncr⟩ := Chord.reduced_canon flipL hv hl
  set n := a.length with hn
  set E := canon s with hE
  set r := run flipL E with hr
  obtain ⟨hf₀, hn₀, -, -⟩ := cupMoves_spec (dualW a)
  have I₀ : TInv (tStart a) := Chord.tInv_start hf₀ hn₀
  set Q := cupLeft (dualW a) with hQ
  have hS₀ : (tStart a).st = Q ++ Q.reverse.map flipSnd := run_cupMoves (dualW a)
  have hQl : Q.length = n := by simp [Q, dualW, n]
  have hnxt : (tStart a).nxt = 2 * n := by
    show (run flipL (cupMoves (dualW a))).length = _
    rw [run_cupMoves]; simp only [List.length_append, List.length_map, List.length_reverse]
    rw [← hQ, hQl]; omega
  -- the canonical diagram to the right of `a`
  obtain ⟨hfit₁, -, hiso₁⟩ := mvMoves_spec n n (2 * n) (tStart a).st
    (fun x hx => hnxt ▸ I₀.fresh x hx) (by rw [hS₀]; simp [hQl]) E (tStart a) []
    I₀ ⟨fun i hi => by simp at hi, fun x hx => by simp at hx⟩ hf (by simpa using Chord.Iso.refl _)
  set T₁ := tRun flipL n (tStart a) (mvMoves n E) with hT₁
  set tr := r.map (shId (2 * n)) with htr
  have hrl : r.length = s.length := hiso.length_eq
  have htrs : tr.map Prod.snd = dualW a ++ b := by
    rw [← hs, ← hiso.1]; simp [tr, List.map_map, Function.comp_def, shId]
  have hQf : ∀ q ∈ Q, q.1 < 2 * n := fun q hq =>
    hnxt ▸ I₀.fresh q (by rw [hS₀]; exact List.mem_append_left _ hq)
  -- nested caps
  have hid : tr.map (mapId id) = tr := by
    conv_rhs => rw [← List.map_id tr]
    exact List.map_congr_left fun x _ => rfl
  have hrun₁ : List.foldl (Chord.step flipL) [] E = r := rfl
  rw [hrun₁] at hiso₁
  obtain ⟨G, hG, hfit₂, hiso₂⟩ := nestCaps_spec Q [] tr id T₁ n (by simp [hQl])
    (by have := congrArg List.length htrs; simp [dualW] at this; omega)
    (by
      rw [List.map_take, htrs, hQl, map_snd_cupLeft]
      simp [n, length_dualW])
    (by rw [map_fst_cupLeft]; exact List.nodup_range.map fun i j h => by simpa using h)
    (fun q hq x hx => by
      have := hQf q hq
      have hx' : x ∈ r.map (shId (2 * n)) := by rw [List.nil_append] at hx; exact hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx'
      simp only [shId, id]; omega)
    (fun x _ y _ h => h)
    (by have := hiso₁; rw [hS₀] at this; simpa [hid] using this)
  rw [hQl] at hfit₂ hiso₂
  set R := mvMoves n E ++ nestCaps n with hR
  have hfit : TFits flipL n (tStart a) R := (tFits_append_at n _ _ _).2 ⟨hfit₁, hfit₂⟩
  have hrun : tRun flipL n (tStart a) R = tRun flipL n T₁ (nestCaps n) := by
    simp [R, T₁, Chord.tRun, List.foldl_append]
  have hpair : Iso (pairing₂ a R) s := by
    rw [pairing₂, hrun]
    refine hiso₂.trans ((Chord.iso_map_of_injOn tr G ?_).trans
      ((Chord.iso_map_of_injOn r (fun i => 2 * n + i) fun x _ y _ h => by omega).trans hiso))
    simpa using hG
  have hlet : R.foldl tLet a = b := by
    obtain ⟨-, h⟩ := chordLay_shift a [] (l := []) (E := E) hf
    have e : (mvMoves n E).foldl tLet a = a ++ dualW a ++ b := by
      have e1 : (mvMoves n E).foldl tLet a = (E.map (shiftM a.length)).foldl chStep a := by
        rw [mvMoves, List.foldl_map, List.foldl_map]; rfl
      rw [e1]
      simp only [List.append_nil] at h
      rw [h, foldl_chStep_eq, ← hr, hiso.1, hs, List.append_assoc]
    rw [hR, List.foldl_append, e, hn, foldl_tLet_nestCaps]
  refine ⟨R, ⟨hfit, hlet⟩, ?_, hpair⟩
  have I := I₀.run hfit
  refine Chord.reduced_of_length_xs_eq_cr I ?_
  rw [Chord.length_xs_tRun, show (tStart a).xs.length = 0 from rfl, zero_add, hR, ncr₂,
    List.countP_append, ← ncr₂, ← ncr₂, ncr₂_mvMoves, ncr₂_nestCaps, add_zero, hncr]
  exact le_antisymm (Chord.cr_le_of_iso hpair.symm) (Chord.cr_le_of_iso hpair)

/-! ## Theorem 8.1 -/

section Theorem

variable {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {cs : CScalars Sc}

variable (μ : X) (a b : List (Letter I)) (M : Set (List (TMove (Letter I))))
  (hM : ∀ R ∈ M, IsMatching₂ a b R ∧ Reduced₂ a R)
  (hrep : ∀ R', IsMatching₂ a b R' → Reduced₂ a R' → ∃ R ∈ M, Iso (pairing₂ a R) (pairing₂ a R'))
  (q : List (TMove (Letter I)) → ℕ → ℕ × ℕ)
  (hq : ∀ R ∈ M, ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q R j))
  (σ : List (TMove (Letter I)) → (ℕ → ℕ) → List (DTMove I))
  (hσ : ∀ R ∈ M, ∀ n, Decorates₂ a R (q R) n (σ R n))

include hM hrep hq hσ in
/-- **[BE2] Theorem 8.1.** Let `M` be a set of reduced `(a, b)`-matchings (`IsMatching₂ a b R`,
`Reduced₂ a R`) containing a representative of every equivalence class of reduced
`(a, b)`-matchings, two matchings being equivalent when they define the same pairing of the
letters of `a* b` (`Iso (pairing₂ a R) (pairing₂ a R')`). For each `R ∈ M` let `q R j` be a
distinguished point on the strand with left endpoint `j` (`OnStrand₂`), and for counts `n` let
`σ R n` be the decorated matching with `n j` dots at `q R j` (`Decorates₂`). Then the 2-morphisms
`dLay a (σ R n) : E_a 1_λ → E_b 1_λ` generate `Hom(E_a 1_λ, E_b 1_λ)` as a right `SYM`-module,
`SYM` acting by `β_λ` in the rightmost region (`diagBubSpan`).

Matchings are encoded by generic layerings (sequences of cups, crossings and caps); every planar
matching has such layerings, and they differ by the super interchange law, i.e. by signs. Compared
with the printed statement, every deviation makes the statement more general:
* `Reduced₂` asks that no strand crosses itself and two strands cross at most once, but not that
  every strand has at most one critical point. So `M` may contain more matchings, and it is asked
  to represent the classes of these reduced matchings. Each such class is a pairing of `a* b`,
  which is the pairing of a matching reduced in the paper's sense, by the remark of [BE2] §8 that
  every matching is equivalent to a reduced one; so a set of representatives as in the paper is a
  valid `M` here. (By `exists_reduced_matching`, the hypothesis amounts to `M` representing every
  pairing.)
* `M` need not consist of pairwise inequivalent matchings, and for each `R` and `n` any decorated
  matching with the prescribed dots may be chosen, in particular with the dots at one height in any
  order.
* `wt(a) = wt(b)` is not assumed. -/
theorem theorem_8_1 : diagBubSpan D Sc cs μ a b (decoratedFamily₂ a M σ) = ⊤ :=
  theorem_8_1_of_pairings μ a b M hM (fun s hv hl hs => by
    obtain ⟨R', hR', hred, hiso⟩ := exists_reduced_matching hv hl hs
    obtain ⟨R, hRM, hR⟩ := hrep R' hR' hred
    exact ⟨R, hRM, hR.trans hiso⟩) q hq σ hσ

end Theorem

end OddMath.SKM
