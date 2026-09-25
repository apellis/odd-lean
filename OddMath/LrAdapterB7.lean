/-
  LR adapter B7 — S1 finite fixed-weight shape census (sorry-free).

  Parent the design specification is the
  ONLY required input. This file realizes exactly ONE the design specification ADDRESSED item —
  the `partition-adapter` shape S1 (finite fixed-weight shape census) — as
  compiled Lean. All other the design specification shapes (S2–S6) and checks (C1–C8) are NOT
  realized here.

  Paper: Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1.
  the design specification (S1): a fixed weight isolates one comparison slice; census
  membership is over partitions (weakly decreasing tuples of positive
  integers — the sign convention, "Partition and tableau conventions"),
  so no trailing zeros exist and membership is unambiguous.

  What this module proves (sorry-free, `Init` only, no Mathlib import):
  - `isPartitionOf`: decidable census predicate (sum + positivity +
    weakly-decreasing);
  - `shapeCensus wt`: computable census (bounded enumeration filtered by
    the predicate);
  - `shapeCount wt`: census length — the `n` that a future adapter feeds
    to `OddMath.LrTriangular.unique`;
  - `shapeCensus_sound`: every census entry satisfies the predicate;
  - `shapeCensus_complete`: every predicate-satisfying list is a census
    entry;
  - `shapeCensus_nodup`: the census has no duplicates;
  - `shapeCensus_mem_single`: `[wt] ∈ census` for `0 < wt` (nonempty slice).

  Honestly NOT here (obstructions in the unpublished development notes): `shapeCensus_sorted`
  (needs the S2 order, whose transpose-vs-row-lex source check is open),
  any S4 shared-lead/matrix/right-hand-side content (needs B1/B2 proof work),
  any `RowSystem` instance (needs genuine P/S families blocked on
  scaffold stubs G2/G3), and therefore no comparison theorem.

  Non-tautology: no Schur object is defined here; the census is pure
  partition combinatorics, independent of the three scaffold families.
  Names live in `OddMath.LrAdapterB7` so no global `Partition` is promoted
  (the scaffold's standalone `abbrev Partition := List Nat` in
  `formal-statements/lr-theorem38.lean` is untouched).
-/

namespace OddMath.LrAdapterB7

/-- Partitions as lists of naturals (scaffold convention,
    `formal-statements/lr-theorem38.lean:22`). Positivity and
    weakly-decreasing order are enforced by `isPartitionOf`, not by
    this abbreviation. -/
abbrev Partition := List Nat

/-- All parts positive (boolean). -/
def allPos : List Nat → Bool
  | [] => true
  | 0 :: _ => false
  | (_ + 1) :: xs => allPos xs

/-- Weakly decreasing (boolean): each part is at least its successor.
    This is the list form of the "weakly decreasing tuples"
    convention in the sign convention. -/
def descending : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: xs => decide (b ≤ a) && descending (b :: xs)

/-- Decidable census predicate (the design specification S1): `l` is a partition of weight `wt`.
    No trailing zeros can occur: every part is positive. -/
def isPartitionOf (l : List Nat) (wt : Nat) : Bool :=
  decide (l.sum = wt) && allPos l && descending l

/-- All lists of length exactly `k` with entries `< m`. -/
def allLists : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | k + 1, m =>
    (List.range m).flatMap fun a => (allLists k m).map fun l => a :: l

/-- All lists of length at most `k` with entries `< m`. -/
def allListsUpTo : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | k + 1, m => allListsUpTo k m ++ allLists (k + 1) m

/-- the design specification S1 census type: a finite list of partitions. -/
abbrev ShapeCensus := List Partition

/-- the design specification S1 census: every partition of weight `wt`, each exactly once.
    Entries are `< wt + 1` and length is at most `wt` (a positive-part
    list summing to `wt` cannot be longer or taller), so the bounded
    enumeration is exhaustive. -/
def shapeCensus (wt : Nat) : ShapeCensus :=
  (allListsUpTo wt (wt + 1)).filter fun l => isPartitionOf l wt

/-- the design specification S1 count: the `n` a future adapter feeds to
    `OddMath.LrTriangular.unique` at weight `wt`. -/
def shapeCount (wt : Nat) : Nat := (shapeCensus wt).length

/-- Generator characterization: membership is exactly
    "right length + bounded entries". -/
theorem mem_allLists {k m : Nat} {l : List Nat} :
    l ∈ allLists k m ↔ l.length = k ∧ ∀ x ∈ l, x < m := by
  induction k generalizing l with
  | zero =>
    constructor
    · intro h
      simp only [allLists, List.mem_singleton] at h
      subst h
      exact ⟨rfl, fun _ hx => (List.not_mem_nil hx).elim⟩
    · intro h
      simp only [allLists, List.mem_singleton]
      exact List.length_eq_zero_iff.mp h.1
  | succ k ih =>
    simp only [allLists, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨a, ham, l', hmem, rfl⟩
      have hrec := ih.mp hmem
      refine ⟨?_, ?_⟩
      · simp only [List.length_cons, hrec.1]
      · intro x hx
        simp only [List.mem_cons] at hx
        cases hx with
        | inl heq => rw [heq]; exact ham
        | inr hmem' => exact hrec.2 x hmem'
    · rintro ⟨hlen, hmem⟩
      match l with
      | [] => simp at hlen
      | a :: l' =>
        refine ⟨a, hmem a (List.mem_cons_self), l', ?_, rfl⟩
        apply ih.mpr
        refine ⟨?_, fun x hx => hmem x (List.mem_cons_of_mem _ hx)⟩
        · simp only [List.length_cons] at hlen ⊢
          omega

/-- Every generator entry is short. -/
theorem allListsUpTo_mem_length (k m : Nat) (l : List Nat)
    (h : l ∈ allListsUpTo k m) : l.length ≤ k := by
  induction k with
  | zero =>
    simp only [allListsUpTo, List.mem_singleton] at h
    subst h
    exact Nat.zero_le _
  | succ k ih =>
    unfold allListsUpTo at h
    rw [List.mem_append] at h
    cases h with
    | inl hmem => exact Nat.le_succ_of_le (ih hmem)
    | inr hmem => have hlen := (mem_allLists.mp hmem).1; omega

/-- The bounded enumeration is exhaustive. -/
theorem allListsUpTo_complete (k m : Nat) (l : List Nat)
    (hlen : l.length ≤ k) (hmem : ∀ x ∈ l, x < m) :
    l ∈ allListsUpTo k m := by
  induction k with
  | zero =>
    match l with
    | [] => simp [allListsUpTo]
    | _ :: _ => simp only [List.length_cons] at hlen; omega
  | succ k ih =>
    unfold allListsUpTo
    rw [List.mem_append]
    by_cases h : l.length ≤ k
    · exact Or.inl (ih h)
    · have hlen' : l.length = k + 1 := by omega
      exact Or.inr (mem_allLists.mpr ⟨hlen', hmem⟩)

/-- A member entry is at most the list sum. -/
theorem mem_le_sum (l : List Nat) (x : Nat) (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => exact (List.not_mem_nil h).elim
  | cons a t ih =>
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    cases h with
    | inl heq => rw [heq]; exact Nat.le_add_right _ _
    | inr hmem => exact Nat.le_trans (ih hmem) (Nat.le_add_left _ _)

/-- A positive-part list is no longer than its sum. -/
theorem length_le_sum_of_pos (l : List Nat)
    (h : ∀ x ∈ l, 0 < x) : l.length ≤ l.sum := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a t ih =>
    have ha : 0 < a := h a (List.mem_cons_self)
    have ht : ∀ x ∈ t, 0 < x :=
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.length_cons, List.sum_cons]
    have := ih ht
    omega

/-- Positivity predicate correctness. -/
theorem allPos_correct (l : List Nat) (h : allPos l = true) :
    ∀ x ∈ l, 0 < x := by
  induction l with
  | nil => intro x hx; exact (List.not_mem_nil hx).elim
  | cons a t ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    cases hx with
    | inl heq =>
      match a with
      | 0 => simp [allPos] at h
      | _ + 1 => rw [heq]; exact Nat.zero_lt_succ _
    | inr hmem =>
      match a with
      | 0 => simp [allPos] at h
      | _ + 1 =>
        simp only [allPos] at h
        exact ih h x hmem

/-- Census entries satisfy the predicate (soundness). -/
theorem shapeCensus_sound (wt : Nat) (l : List Nat)
    (h : l ∈ shapeCensus wt) : isPartitionOf l wt = true := by
  unfold shapeCensus at h
  exact (List.mem_filter.mp h).2

/-- Every predicate-satisfying list is a census entry (completeness).
    The bounds that place `l` in the generator — length at most `wt`,
    entries below `wt + 1` — follow from positivity and the weight sum. -/
theorem shapeCensus_complete (wt : Nat) (l : List Nat)
    (h : isPartitionOf l wt = true) : l ∈ shapeCensus wt := by
  unfold isPartitionOf at h
  have hconj := (Bool.and_eq_true _ _).mp h
  have hconj1 := (Bool.and_eq_true _ _).mp hconj.1
  have hsum : l.sum = wt := of_decide_eq_true hconj1.1
  have hpos : ∀ x ∈ l, 0 < x := allPos_correct l hconj1.2
  unfold shapeCensus
  apply List.mem_filter.mpr
  refine ⟨?_, h⟩
  apply allListsUpTo_complete
  · calc l.length ≤ l.sum := length_le_sum_of_pos l hpos
      _ = wt := hsum
  · intro x hx
    have hle := mem_le_sum l x hx
    omega

/-- Appending nodup lists with disjoint entries stays nodup. -/
theorem nodup_append {l₁ l₂ : List α} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (h : ∀ x ∈ l₁, x ∉ l₂) : (l₁ ++ l₂).Nodup := by
  induction l₁ with
  | nil => simpa using h₂
  | cons a t ih =>
    have hcons := (List.nodup_cons.mp h₁)
    have hat : a ∉ t ++ l₂ := by
      intro hcon
      rw [List.mem_append] at hcon
      cases hcon with
      | inl hmem => exact hcons.1 hmem
      | inr hmem => exact h a List.mem_cons_self hmem
    have hsub : ∀ x ∈ t, x ∉ l₂ :=
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact (List.nodup_cons.mpr ⟨hat, ih hcons.2 hsub⟩)

/-- Flat-map over a nodup list with nodup, pairwise-disjoint fibers. -/
theorem nodup_flatMap {f : α → List β} {l : List α} (hl : l.Nodup)
    (hf : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ f a, x ∉ f b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hcons := (List.nodup_cons.mp hl)
    simp only [List.flatMap_cons]
    apply nodup_append (hf a (List.mem_cons_self))
    · apply ih hcons.2
      · intro b hb
        exact hf b (List.mem_cons_of_mem _ hb)
      · intro b hb1 b' hb2 hne x hx
        exact hdisj b (List.mem_cons_of_mem _ hb1) b'
          (List.mem_cons_of_mem _ hb2) hne x hx
    · intro x hx hcon
      have hex := List.mem_flatMap.mp hcon
      obtain ⟨b, hb, hxb⟩ := hex
      by_cases heq : a = b
      · subst heq
        exact hcons.1 hb
      · exact hdisj a List.mem_cons_self b
          (List.mem_cons_of_mem _ hb) heq x hx hxb

/-- The range enumerator is nodup (proved directly to avoid depending
    on the exact core lemma name). -/
theorem nodup_range' : ∀ (m : Nat), (List.range m).Nodup
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ]
    apply nodup_append (nodup_range' m) (by simp)
    intro x hxmem hxcon
    have h1 : x = m := List.mem_singleton.mp hxcon
    have h2 : x < m := List.mem_range.mp hxmem
    omega

/-- Prefixing every entry preserves nodup. -/
theorem nodup_map_prefix (a : Nat) (l : List (List Nat))
    (h : l.Nodup) : ((l.map fun x => a :: x)).Nodup := by
  induction l with
  | nil => simp
  | cons y t ih =>
    have hcons := (List.nodup_cons.mp h)
    have hmem : a :: y ∉ (t.map fun x => a :: x) := by
      intro hcon
      have hex := List.mem_map.mp hcon
      obtain ⟨z, hzin, hzeq⟩ := hex
      have hzy : z = y := by simpa using hzeq
      rw [hzy] at hzin
      exact hcons.1 hzin
    exact (List.nodup_cons.mpr ⟨hmem, ih hcons.2⟩)

/-- The exact-length generator is nodup. -/
theorem allLists_nodup (k m : Nat) : (allLists k m).Nodup := by
  induction k with
  | zero => simp [allLists]
  | succ k ih =>
    unfold allLists
    apply nodup_flatMap (nodup_range' m)
    · intro a _
      exact nodup_map_prefix a _ ih
    · intro a _ b _ hne x hxmem hxcon
      have hex1 := List.mem_map.mp hxmem
      have hex2 := List.mem_map.mp hxcon
      obtain ⟨y, _, hyeq⟩ := hex1
      obtain ⟨z, _, hzeq⟩ := hex2
      have hcc : a :: y = b :: z := hyeq.trans hzeq.symm
      have hconj : a = b ∧ y = z := by simpa using hcc
      exact hne hconj.1

/-- The bounded enumeration is nodup (fibers by length are disjoint). -/
theorem allListsUpTo_nodup (k m : Nat) : (allListsUpTo k m).Nodup := by
  induction k with
  | zero => simp [allListsUpTo]
  | succ k ih =>
    unfold allListsUpTo
    apply nodup_append ih (allLists_nodup (k + 1) m)
    intro x hxmem hxcon
    have hle := allListsUpTo_mem_length k m x hxmem
    have heq := (mem_allLists.mp hxcon).1
    omega

/-- Filtering preserves nodup. -/
theorem nodup_filter (p : α → Bool) (l : List α)
    (h : l.Nodup) : (l.filter p).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hcons := (List.nodup_cons.mp h)
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, ↓reduceIte]
      have hmem : a ∉ t.filter p := by
        intro hcon
        have hex := (List.mem_filter.mp hcon).1
        exact hcons.1 hex
      exact (List.nodup_cons.mpr ⟨hmem, ih hcons.2⟩)
    · simp only [List.filter_cons, hp, ↓reduceIte]
      exact ih hcons.2

/-- the design specification S1 justification: the census has no duplicates. -/
theorem shapeCensus_nodup (wt : Nat) : (shapeCensus wt).Nodup := by
  unfold shapeCensus
  exact nodup_filter _ _ (allListsUpTo_nodup wt (wt + 1))

/-- The singleton partition always qualifies (nonempty slice, `0 < wt`). -/
theorem shapeCensus_mem_single {wt : Nat} (hwt : 0 < wt) :
    [wt] ∈ shapeCensus wt := by
  match wt with
  | 0 => omega
  | n + 1 =>
    apply shapeCensus_complete
    have hsum : [n + 1].sum = n + 1 := by simp
    have hdec : decide ([n + 1].sum = n + 1) = true := by
      rw [hsum]
      exact decide_eq_true rfl
    have hpos : allPos [n + 1] = true := by rfl
    have hdesc : descending [n + 1] = true := by rfl
    unfold isPartitionOf
    rw [hdec, hpos, hdesc]
    rfl

/- Census spot-values (compiled execution evidence; outputs appear in
   the isolated build log): partitions of 0-4.
   (Plain block comment: `#eval` takes no docstring.) -/
#eval shapeCensus 0
#eval shapeCensus 1
#eval shapeCensus 2
#eval shapeCensus 3
#eval shapeCensus 4
#eval shapeCount 4

/- Axiom audit (outputs appear in the isolated build log; expected:
   at most `propext`, with no unfinished-proof axiom). -/
#print axioms mem_allLists
#print axioms shapeCensus_sound
#print axioms shapeCensus_complete
#print axioms shapeCensus_nodup
#print axioms shapeCensus_mem_single

end OddMath.LrAdapterB7
