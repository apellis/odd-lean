/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChordReduced

/-!
# Joining strands: the pairing after a cap

Combinatorics for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
§8 (matchings and reduced matchings before Theorem 8.1), for the two-sided case. As in M.
Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1, an
`(a, b)`-matching is studied through its bent form, a matching of `a* b` (the lower endpoints are
bent up to the left by nested cups). A state of strands is a list of `(id, letter)` (as in
`StringDiagrams.Chord`); a cap joins the two strands at adjacent positions: both positions are
removed and the id of the right strand is renamed to the id of the left one (`jn`).

## Main results

* `iso_map_of_injOn`: renaming ids injectively does not change the pairing.
* `same_jn_iff`, `Iso.jn`: the pairing after a cap depends only on the pairing before.
* `foldl_mvL`, `foldl_mvR`: a strand moving left (right) across a block of strands by crossings.
* `foldl_shift`: a diagram placed between other strands.
-/

namespace StringDiagrams.Chord

variable {α : Type*}

/-! ## Renaming ids -/

/-- Rename the id `b` to `a`. -/
def rlId (b a : ℕ) (i : ℕ) : ℕ := if i = b then a else i

/-- Rename the strand id `b` to `a` (the strand `b` is joined to the strand `a`). -/
def rl (b a : ℕ) (x : ℕ × α) : ℕ × α := (rlId b a x.1, x.2)

@[simp] theorem rl_snd (b a : ℕ) (x : ℕ × α) : (rl b a x).2 = x.2 := rfl

@[simp] theorem snd_comp_rl (b a : ℕ) : (Prod.snd ∘ rl b a : ℕ × α → α) = Prod.snd := rfl

@[simp] theorem map_snd_map_rl (b a : ℕ) (s : List (ℕ × α)) :
    (s.map (rl b a)).map Prod.snd = s.map Prod.snd := by
  simp [List.map_map, Function.comp_def]

theorem rl_of_ne {b a : ℕ} {x : ℕ × α} (h : x.1 ≠ b) : rl b a x = x := by
  simp [rl, rlId, h]

theorem rl_of_eq {b a : ℕ} {x : ℕ × α} (h : x.1 = b) : rl b a x = (a, x.2) := by
  simp [rl, rlId, h]

theorem map_rl_of_forall_ne {b a : ℕ} {s : List (ℕ × α)} (h : ∀ x ∈ s, x.1 ≠ b) :
    s.map (rl b a) = s := by
  conv_rhs => rw [← List.map_id s]
  exact List.map_congr_left fun x hx => rl_of_ne (h x hx)

theorem rlId_eq_rlId {b a x y : ℕ} :
    rlId b a x = rlId b a y ↔ x = y ∨ (x = b ∧ y = a) ∨ (x = a ∧ y = b) := by
  unfold rlId; split_ifs <;> omega

theorem idAt_map_fst (s : List (ℕ × α)) (f : ℕ → ℕ) (i : ℕ) :
    idAt (s.map fun x => (f x.1, x.2)) i = (idAt s i).map f := by
  simp only [idAt, List.getElem?_map]
  cases s[i]? <;> rfl

/-- **Renaming the ids injectively does not change the pairing.** -/
theorem iso_map_of_injOn (s : List (ℕ × α)) (f : ℕ → ℕ)
    (hf : ∀ x ∈ s, ∀ y ∈ s, f x.1 = f y.1 → x.1 = y.1) :
    Iso (s.map fun x => (f x.1, x.2)) s := by
  refine ⟨by simp [List.map_map, Function.comp_def], fun i j => ?_⟩
  simp only [Same, idAt_map_fst, ne_eq, Option.map_eq_none_iff]
  refine and_congr_right fun _ => and_congr_right fun hi => ?_
  simp only [idAt] at hi ⊢
  rcases e₁ : s[i]? with _ | x
  · simp [e₁] at hi
  rcases e₂ : s[j]? with _ | y
  · simp
  simp only [Option.map_some, Option.some.injEq]
  exact ⟨hf x (List.mem_of_getElem? e₁) y (List.mem_of_getElem? e₂), fun h => by rw [h]⟩

theorem iso_map_rl_of_fresh {b a : ℕ} {s : List (ℕ × α)} (h : ∀ x ∈ s, x.1 ≠ a) :
    Iso (s.map (rl b a)) s :=
  iso_map_of_injOn s (rlId b a) fun x hx y hy e => by
    have := h x hx; have := h y hy; unfold rlId at e; split_ifs at e <;> omega

/-- The two ways of joining the strands `a` and `b` give the same pairing. -/
theorem iso_map_rl_comm {a b : ℕ} (hab : a ≠ b) (s : List (ℕ × α)) :
    Iso (s.map (rl a b)) (s.map (rl b a)) := by
  have e : s.map (rl b a) = (s.map (rl a b)).map fun x => (Equiv.swap a b x.1, x.2) := by
    rw [List.map_map]
    refine List.map_congr_left fun x _ => ?_
    simp only [rl, rlId, Function.comp_apply]
    by_cases h1 : x.1 = b
    · simp [h1, Ne.symm hab]
    · by_cases h2 : x.1 = a
      · simp [h2, hab]
      · simp [h1, h2, Equiv.swap_apply_of_ne_of_ne h2 h1]
  rw [e]
  exact (iso_map_of_injOn _ _ fun x _ y _ h => (Equiv.swap a b).injective h).symm

/-! ## Joining two adjacent strands -/

theorem same_map_rl_iff (u : List (ℕ × α)) (b a : ℕ) {i j : ℕ} :
    Same (u.map (rl b a)) i j ↔ i ≠ j ∧ i < u.length ∧ j < u.length ∧
      (idAt u i = idAt u j ∨ (idAt u i = some b ∧ idAt u j = some a) ∨
        (idAt u i = some a ∧ idAt u j = some b)) := by
  have hid : ∀ i, idAt (u.map (rl b a)) i = (idAt u i).map (rlId b a) := fun i =>
    idAt_map_fst u (rlId b a) i
  simp only [Same, hid, ne_eq, Option.map_eq_none_iff, idAt_ne_none_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hi, h⟩
    rcases e₂ : idAt u j with _ | y
    · rw [e₂] at h
      rcases e₁ : idAt u i with _ | x
      · exact absurd e₁ (idAt_ne_none_iff.2 hi)
      · rw [e₁] at h; simp at h
    have hj : j < u.length := idAt_ne_none_iff.1 (by rw [e₂]; simp)
    rcases e₁ : idAt u i with _ | x
    · exact absurd e₁ (idAt_ne_none_iff.2 hi)
    rw [e₁, e₂] at h
    simp only [Option.map_some, Option.some.injEq, rlId_eq_rlId] at h
    refine ⟨hi, hj, ?_⟩
    rcases h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · rintro ⟨hi, hj, h⟩
    refine ⟨hi, ?_⟩
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h]
    · rw [h1, h2]; simp [rlId_eq_rlId]
    · rw [h1, h2]; simp [rlId_eq_rlId]

/-- **Joining** the strands at the adjacent positions `r` and `r + 1` (a cap): both positions are
removed and the id of the strand at `r + 1` is renamed to the id of the strand at `r`. -/
def jn (s : List (ℕ × α)) (r : ℕ) : List (ℕ × α) :=
  match s.drop r with
  | A :: B :: _ => (rmAt s r).map (rl B.1 A.1)
  | _ => s

theorem rmAt_mid (P Q : List (ℕ × α)) (A B : ℕ × α) :
    rmAt (P ++ [A, B] ++ Q) P.length = P ++ Q := by
  simp [rmAt]

theorem jn_mid (P Q : List (ℕ × α)) (A B : ℕ × α) :
    jn (P ++ [A, B] ++ Q) P.length = (P ++ Q).map (rl B.1 A.1) := by
  have e : (P ++ [A, B] ++ Q).drop P.length = A :: B :: Q := by simp
  unfold jn; rw [e, rmAt_mid]

theorem exists_mid {s : List (ℕ × α)} {r : ℕ} (h : r + 1 < s.length) :
    ∃ P A B Q, s = P ++ [A, B] ++ Q ∧ P.length = r := by
  refine ⟨s.take r, s[r], s[r + 1], s.drop (r + 2), ?_, by simp; omega⟩
  have h1 : s.drop r = s[r] :: s.drop (r + 1) := List.drop_eq_getElem_cons (by omega)
  have h2 : s.drop (r + 1) = s[r + 1] :: s.drop (r + 2) := List.drop_eq_getElem_cons h
  calc s = s.take r ++ s.drop r := (List.take_append_drop r s).symm
    _ = _ := by rw [h1, h2]; simp

theorem idAt_eq_iff_same {s : List (ℕ × α)} {x r : ℕ} (hx : x < s.length) (hxr : x ≠ r) : idAt s x = idAt s r ↔ Same s x r :=
  ⟨fun h => ⟨hxr, idAt_ne_none_iff.2 hx, h⟩, fun h => h.2.2⟩

/-- **The pairing after joining two adjacent strands**, in terms of the pairing before. -/
theorem same_jn_iff {s : List (ℕ × α)} {r : ℕ} (hr : r + 1 < s.length) {i j : ℕ} :
    Same (jn s r) i j ↔ i ≠ j ∧ i + 2 < s.length ∧ j + 2 < s.length ∧
      (Same s (rmIdx r i) (rmIdx r j) ∨
        (Same s (rmIdx r i) (r + 1) ∧ Same s (rmIdx r j) r) ∨
        (Same s (rmIdx r i) r ∧ Same s (rmIdx r j) (r + 1))) := by
  obtain ⟨P, A, B, Q, rfl, rfl⟩ := exists_mid hr
  set s := P ++ [A, B] ++ Q with hs
  have hl : P.length + 2 ≤ s.length := by simp [hs]
  have hlen : (rmAt s P.length).length = s.length - 2 := length_rmAt s hl
  have hA : idAt s P.length = some A.1 := by simp [idAt, hs]
  have hB : idAt s (P.length + 1) = some B.1 := by simp [idAt, hs]
  rw [jn_mid, ← rmAt_mid P Q A B, same_map_rl_iff, hlen, idAt_rmAt hl, idAt_rmAt hl]
  refine and_congr_right fun hij => ?_
  have key : ∀ i, i + 2 < s.length → rmIdx P.length i < s.length ∧
      rmIdx P.length i ≠ P.length ∧ rmIdx P.length i ≠ P.length + 1 := by
    intro i hi; unfold rmIdx; split_ifs <;> omega
  constructor
  · rintro ⟨hi, hj, h⟩
    have hi' : i + 2 < s.length := by omega
    have hj' : j + 2 < s.length := by omega
    obtain ⟨k1, k2, k3⟩ := key i hi'
    obtain ⟨l1, l2, l3⟩ := key j hj'
    refine ⟨hi', hj', ?_⟩
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rwa [Ne, rmIdx_inj], idAt_ne_none_iff.2 k1, h⟩
    · rw [← hB] at h1; rw [← hA] at h2
      exact Or.inr (Or.inl ⟨(idAt_eq_iff_same k1 k3).1 h1,
        (idAt_eq_iff_same l1 l2).1 h2⟩)
    · rw [← hA] at h1; rw [← hB] at h2
      exact Or.inr (Or.inr ⟨(idAt_eq_iff_same k1 k2).1 h1,
        (idAt_eq_iff_same l1 l3).1 h2⟩)
  · rintro ⟨hi', hj', h⟩
    obtain ⟨k1, k2, k3⟩ := key i hi'
    obtain ⟨l1, l2, l3⟩ := key j hj'
    refine ⟨by omega, by omega, ?_⟩
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h.2.2
    · exact Or.inr (Or.inl ⟨by rw [← hB]; exact h1.2.2, by rw [← hA]; exact h2.2.2⟩)
    · exact Or.inr (Or.inr ⟨by rw [← hA]; exact h1.2.2, by rw [← hB]; exact h2.2.2⟩)

theorem map_snd_jn (s : List (ℕ × α)) (r : ℕ) (hr : r + 1 < s.length) :
    (jn s r).map Prod.snd = (rmAt s r).map Prod.snd := by
  obtain ⟨P, A, B, Q, rfl, rfl⟩ := exists_mid hr
  rw [jn_mid, map_snd_map_rl, rmAt_mid]

/-- **The pairing after a cap depends only on the pairing before.** -/
theorem Iso.jn {s s' : List (ℕ × α)} (h : Iso s s') {r : ℕ} (hr : r + 1 < s.length) :
    Iso (Chord.jn s r) (Chord.jn s' r) := by
  have hr' : r + 1 < s'.length := h.length_eq ▸ hr
  refine ⟨?_, fun i j => ?_⟩
  · rw [map_snd_jn s r hr, map_snd_jn s' r hr']
    exact (h.rmAt (by omega)).1
  · rw [same_jn_iff hr, same_jn_iff hr', h.length_eq, h.2, h.2, h.2, h.2, h.2]

theorem length_jn {s : List (ℕ × α)} {r : ℕ} (hr : r + 1 < s.length) :
    (jn s r).length = s.length - 2 := by
  obtain ⟨P, A, B, Q, rfl, rfl⟩ := exists_mid hr
  rw [jn_mid]; simp; omega

/-! ## A strand moving across a block of strands -/

/-- The crossings moving the strand at position `g + n` left across the `n` strands before it. -/
def mvL (g : ℕ) : ℕ → List (Move α)
  | 0 => []
  | n + 1 => mvL (g + 1) n ++ [.cross g]

/-- The crossings moving the strand at position `g` right across the `n` strands after it. -/
def mvR (g : ℕ) : ℕ → List (Move α)
  | 0 => []
  | n + 1 => .cross g :: mvR (g + 1) n

theorem ncr_mvL (g : ℕ) : ∀ n, OddMath.SKM.ncr (mvL (α := α) g n) = n
  | 0 => rfl
  | n + 1 => by rw [mvL, OddMath.SKM.ncr_append, ncr_mvL]; rfl

theorem ncr_mvR (g : ℕ) : ∀ n, OddMath.SKM.ncr (mvR (α := α) g n) = n
  | 0 => rfl
  | n + 1 => by rw [mvR, ← List.singleton_append, OddMath.SKM.ncr_append, ncr_mvR]; simp [OddMath.SKM.ncr]; omega

theorem fits_mvL {m : ℕ} : ∀ (g n : ℕ), g + n < m → Fits m (mvL (α := α) g n)
  | _, 0, _ => trivial
  | g, n + 1, h => by
    rw [mvL, fits_append]
    refine ⟨fits_mvL (g + 1) n (by omega), ?_⟩
    have : (mvL (α := α) (g + 1) n).foldl Move.len m = m := by
      clear h; induction n generalizing g with
      | zero => rfl
      | succ n ih => rw [mvL, List.foldl_append, ih]; rfl
    rw [this]; exact ⟨show g + 1 < m by omega, trivial⟩

theorem fits_mvR {m : ℕ} : ∀ (g n : ℕ), g + n < m → Fits m (mvR (α := α) g n)
  | _, 0, _ => trivial
  | g, n + 1, h => ⟨show g + 1 < m by omega, fits_mvR (m := m) (g + 1) n (by omega)⟩

variable {β : Type*}

/-- **A strand moving left across a block**, for any step function acting on crossings by
`swapAt`. -/
theorem foldl_mvL (f : List β → Move α → List β) (hf : ∀ l p, f l (.cross p) = swapAt l p) :
    ∀ (u S Q : List β) (b : β),
      (mvL u.length S.length).foldl f (u ++ S ++ [b] ++ Q) = u ++ [b] ++ S ++ Q
  | u, [], Q, b => by simp [mvL]
  | u, x :: S, Q, b => by
    have e1 : u ++ (x :: S) ++ [b] ++ Q = (u ++ [x]) ++ S ++ [b] ++ Q := by simp
    have e2 : u.length + 1 = (u ++ [x]).length := by simp
    rw [List.length_cons, mvL, List.foldl_append, e1, e2, foldl_mvL f hf (u ++ [x]) S Q b]
    simp only [List.foldl_cons, List.foldl_nil, hf]
    have e3 : u ++ [x] ++ [b] ++ S ++ Q = u ++ x :: b :: (S ++ Q) := by simp
    rw [e3, OddMath.SKM.swapAt_mid]; simp

/-- **A strand moving right across a block.** -/
theorem foldl_mvR (f : List β → Move α → List β) (hf : ∀ l p, f l (.cross p) = swapAt l p) :
    ∀ (u S Q : List β) (a : β),
      (mvR u.length S.length).foldl f (u ++ [a] ++ S ++ Q) = u ++ S ++ [a] ++ Q
  | u, [], Q, a => by simp [mvR]
  | u, x :: S, Q, a => by
    rw [List.length_cons, mvR, List.foldl_cons, hf]
    have e3 : u ++ [a] ++ (x :: S) ++ Q = u ++ a :: x :: (S ++ Q) := by simp
    rw [e3, OddMath.SKM.swapAt_mid]
    have e4 : u ++ x :: a :: (S ++ Q) = (u ++ [x]) ++ [a] ++ S ++ Q := by simp
    have e2 : u.length + 1 = (u ++ [x]).length := by simp
    rw [e4, e2, foldl_mvR f hf (u ++ [x]) S Q a]; simp

end StringDiagrams.Chord
