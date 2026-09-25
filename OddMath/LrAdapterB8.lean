/-
  LR adapter B8 — S2 enumeration order + index over the B7 census (sorry-free).

  Context: the design specification is the
  shape-spec authority; B7 delivered
  the S1 census this module builds on. The B7 census module is IMPORTED
  here, never redefined: no S1 declaration (`shapeCensus`, `shapeCount`,
  soundness/completeness/nodup, generators) is restated below.
  This file realizes exactly ONE further the design specification item — the
  `enumeration-order` shape S2 — as compiled Lean. All other the design specification shapes
  (S3–S6) and end-to-end checks (C1–C8) are NOT realized here.

  Paper: Ellis, "The odd Littlewood-Richardson rule", arXiv:1111.3932v1.
  the design specification (S2): width-first enumeration order with justifications
  `shapeOrder_wf` and `shapeIndex_correct`.

  Choice documentation (C6 narrowing): the design specification records that the paper's
  induction-ordering passage (lines 508-520) carries two phrasings —
  transpose-lexicographic and row-lexicographic — and the adapter must
  pick one with a paper locator. B8 fixes the row/list phrasing:
  `shapeOrder` compares the partition lists themselves (length first,
  then head-major lexicographic), NOT their transposes. The
  transpose-vs-row source adjudication (which phrasing the paper's
  induction actually consumes) is recorded as the remaining C6 half in
  the unpublished development notes; the order/index machinery itself (well-foundedness,
  totality, transitivity, index round-trip, census sortedness) is proved
  here and is independent of that adjudication.

  What this module proves (sorry-free, `Init` + B7 import only):
  - `lexLt`: head-major lexicographic strict order on partitions;
  - `shapeOrder`: the design specification S2 width-first order (list length, then `lexLt`);
  - `shapeOrder_wf`: well-foundedness (future induction measure carrier);
  - `shapeOrder_total` / `shapeOrder_trans` / `shapeOrder_irrefl`:
    order bona fides;
  - `shapeIndex`: position of a census member as `Fin (shapeCount wt)`;
  - `shapeIndex_correct`: the index round-trips through the census;
  - `shapeCensus_sorted`: the B7 census is ordered by `shapeOrder`
    (proved below).

  Honest deviation from the the design specification declaration sketch: the design specification writes the index
  totally (`Partition → Fin (shapeCount wt)`). A non-member has no
  position, so the constructible form carries the membership proof
  (`(h : l ∈ shapeCensus wt)`); this is documented, not hidden.

  Non-tautology: no Schur object is defined here; the order/index is
  pure partition combinatorics over the imported S1 census.
  Names live in `OddMath.LrAdapterB8`.
-/

import OddMath.LrAdapterB7

namespace OddMath.LrAdapterB8

open OddMath.LrAdapterB7

/-- Bootstrapped strong induction on `Nat`, proved from structural
    induction alone (no Mathlib/WF API needed). -/
theorem b8StrongNat (motive : Nat → Prop)
    (step : ∀ n, (∀ m, m < n → motive m) → motive n) :
    ∀ n, motive n := by
  have H : ∀ n, ∀ m, m ≤ n → motive m := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have h0 : m = 0 := by omega
      subst h0
      exact step 0 (fun m hm => False.elim (by omega))
    | succ n ih =>
      intro m hm
      by_cases hle : m ≤ n
      · exact ih m hle
      · have heq : m = n + 1 := by omega
        subst heq
        exact step (n + 1) (fun m' hm' => ih m' (by omega))
  intro n
  exact H n n (by omega)

/-- Head-major lexicographic strict order on partitions (boolean).
    `[]` is below every nonempty list; equal heads recurse on tails. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a < b then true else if b < a then false else lexLt as bs

theorem lexLt_cons_cons (a b : Nat) (as bs : List Nat) :
    lexLt (a :: as) (b :: bs) =
      (if a < b then true else if b < a then false else lexLt as bs) := by
  rfl

theorem lexLt_nil_nil : lexLt ([] : List Nat) [] = false := by
  rfl

theorem lexLt_nil_cons (b : Nat) (bs : List Nat) :
    lexLt ([] : List Nat) (b :: bs) = true := by
  rfl

theorem lexLt_cons_nil (a : Nat) (as : List Nat) :
    lexLt (a :: as) ([] : List Nat) = false := by
  rfl

/-- The lexicographic order is irreflexive. -/
theorem lexLt_self : ∀ (l : List Nat), lexLt l l = false := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [lexLt_cons_cons]
    have hab : ¬ a < a := by omega
    rw [if_neg hab, if_neg hab]
    exact ih

/-- The lexicographic order is transitive. -/
theorem lexLt_trans : ∀ (x y z : List Nat),
    lexLt x y = true → lexLt y z = true → lexLt x z = true := by
  intro x
  induction x with
  | nil =>
    intro y z hxy hyz
    cases y with
    | nil =>
      rw [lexLt_nil_nil] at hxy
      simp at hxy
    | cons b bs =>
      rw [lexLt_nil_cons] at hxy
      cases z with
      | nil =>
        rw [lexLt_cons_nil] at hyz
        simp at hyz
      | cons c cs =>
        exact lexLt_nil_cons c cs
  | cons a as ih =>
    intro y z hxy hyz
    cases y with
    | nil =>
      rw [lexLt_cons_nil] at hxy
      simp at hxy
    | cons b bs =>
      rw [lexLt_cons_cons] at hxy
      cases z with
      | nil =>
        rw [lexLt_cons_nil] at hyz
        simp at hyz
      | cons c cs =>
        rw [lexLt_cons_cons] at hyz ⊢
        by_cases hab : a < b
        · rw [if_pos hab] at hxy
          by_cases hbc : b < c
          · rw [if_pos hbc] at hyz
            have hac : a < c := by omega
            rw [if_pos hac]
          · rw [if_neg hbc] at hyz
            by_cases hcb : c < b
            · rw [if_pos hcb] at hyz
              simp at hyz
            · rw [if_neg hcb] at hyz
              have hac : a < c := by omega
              rw [if_pos hac]
        · rw [if_neg hab] at hxy
          by_cases hba : b < a
          · rw [if_pos hba] at hxy
            simp at hxy
          · rw [if_neg hba] at hxy
            have hab_eq : a = b := by omega
            by_cases hbc : b < c
            · rw [if_pos hbc] at hyz
              have hac : a < c := by omega
              rw [if_pos hac]
            · rw [if_neg hbc] at hyz
              by_cases hcb : c < b
              · rw [if_pos hcb] at hyz
                simp at hyz
              · rw [if_neg hcb] at hyz
                have hac_eq : a = c := by omega
                rw [hac_eq]
                have hcc : ¬ c < c := by omega
                rw [if_neg hcc, if_neg hcc]
                exact ih bs cs hxy hyz

/-- Trichotomy: any two lists are lex-ordered one way or equal. -/
theorem lexLt_total : ∀ (a b : List Nat),
    lexLt a b = true ∨ a = b ∨ lexLt b a = true := by
  intro a
  induction a with
  | nil =>
    intro b
    cases b with
    | nil => exact Or.inr (Or.inl rfl)
    | cons c cs => exact Or.inl (lexLt_nil_cons c cs)
  | cons a as ih =>
    intro b
    cases b with
    | nil => exact Or.inr (Or.inr (lexLt_nil_cons a as))
    | cons c cs =>
      rw [lexLt_cons_cons]
      by_cases hac : a < c
      · rw [if_pos hac]
        exact Or.inl rfl
      · rw [if_neg hac]
        by_cases hca : c < a
        · have hba : lexLt (c :: cs) (a :: as) = true := by
            rw [lexLt_cons_cons, if_pos hca]
          exact Or.inr (Or.inr hba)
        · have e : a = c := by omega
          subst e
          have haa : ¬ a < a := by omega
          rw [if_neg haa]
          have h := ih cs
          cases h with
          | inl hlt => exact Or.inl hlt
          | inr h =>
            cases h with
            | inl heq =>
              subst heq
              exact Or.inr (Or.inl rfl)
            | inr hlt =>
              have hrev : lexLt (a :: cs) (a :: as) = true := by
                rw [lexLt_cons_cons, if_neg haa, if_neg haa]
                exact hlt
              exact Or.inr (Or.inr hrev)

/-- the design specification S2 order: width (list length) first, then head-major
    lexicographic on the partition lists themselves (row/list phrasing;
    see the module header for the transpose documentation). -/
def shapeOrder (a b : Partition) : Prop :=
  a.length < b.length ∨ (a.length = b.length ∧ lexLt a b = true)

theorem shapeOrder_eq (a b : Partition) :
    shapeOrder a b =
      (a.length < b.length ∨ (a.length = b.length ∧ lexLt a b = true)) := by
  rfl

/-- The width-first order is irreflexive. -/
theorem shapeOrder_irrefl : ∀ (l : Partition), ¬ shapeOrder l l := by
  intro l h
  rw [shapeOrder_eq] at h
  cases h with
  | inl hlt => omega
  | inr h =>
    obtain ⟨_, hlt⟩ := h
    rw [lexLt_self l] at hlt
    cases hlt

/-- The width-first order is transitive. -/
theorem shapeOrder_trans : ∀ (x y z : Partition),
    shapeOrder x y → shapeOrder y z → shapeOrder x z := by
  intro x y z hxy hyz
  rw [shapeOrder_eq] at hxy hyz ⊢
  cases hxy with
  | inl h1 =>
    cases hyz with
    | inl h2 => exact Or.inl (by omega)
    | inr h2 => exact Or.inl (by omega)
  | inr h1 =>
    cases hyz with
    | inl h2 => exact Or.inl (by omega)
    | inr h2 =>
      have hlen : x.length = z.length := by omega
      have hlex : lexLt x z = true := lexLt_trans x y z h1.2 h2.2
      exact Or.inr ⟨hlen, hlex⟩

/-- The width-first order is total (trichotomy). -/
theorem shapeOrder_total : ∀ (a b : Partition),
    shapeOrder a b ∨ a = b ∨ shapeOrder b a := by
  intro a b
  by_cases hlen : a.length < b.length
  · exact Or.inl (Or.inl hlen)
  · by_cases hlen2 : b.length < a.length
    · exact Or.inr (Or.inr (Or.inl hlen2))
    · have heq : a.length = b.length := by omega
      have h := lexLt_total a b
      cases h with
      | inl hlt => exact Or.inl (Or.inr ⟨heq, hlt⟩)
      | inr h =>
        cases h with
        | inl heq2 => exact Or.inr (Or.inl heq2)
        | inr hlt =>
          have heq' : b.length = a.length := by omega
          exact Or.inr (Or.inr (Or.inr ⟨heq', hlt⟩))

/-- The width-first order is decidable (needed for executable checks). -/
instance : DecidableRel shapeOrder := fun a b => by
  unfold shapeOrder
  infer_instance

/-- Graded lexicographic relation: same-length lists of length `K`
    ordered by `lexLt`. The grade keeps every predecessor in-grade so
    the well-foundedness induction closes. -/
def lexRel (K : Nat) (x y : List Nat) : Prop :=
  x.length = K ∧ y.length = K ∧ lexLt x y = true

/-- A list of successor length splits into head and tail. -/
theorem cons_of_length_succ (l : List Nat) (n : Nat) :
    l.length = n + 1 → ∃ a t, l = a :: t ∧ t.length = n := by
  intro h
  cases l with
  | nil => simp at h
  | cons a t => exact ⟨a, t, rfl, by have h2 : t.length + 1 = n + 1 := h; omega⟩

/-- A list of length zero is empty. -/
theorem length_zero_eq_nil : ∀ (l : List Nat), l.length = 0 → l = [] := by
  intro l h
  cases l with
  | nil => rfl
  | cons a t => simp at h

/-- Well-foundedness lifts one grade: every list of length `K + 1` is
    accessible once every list of length `K` is. Heads strictly
    decrease (strong induction) or stay equal with lex-smaller tails
    (graded accessibility). -/
theorem lexRel_acc_step (K : Nat)
    (IHK : ∀ t : List Nat, t.length = K → Acc (lexRel K) t)
    (s : List Nat) (hs : s.length = K + 1) :
    Acc (lexRel (K + 1)) s := by
  obtain ⟨a, as, rfl, has⟩ := cons_of_length_succ s K hs
  suffices H : ∀ (b : Nat) (u : List Nat),
      u.length = K → Acc (lexRel (K + 1)) (b :: u) from H a as has
  exact b8StrongNat
    (fun b => ∀ u : List Nat, u.length = K → Acc (lexRel (K + 1)) (b :: u))
    (fun b innerIH u hu => by
      induction (IHK u hu) generalizing b with
      | intro u hacc ihAcc =>
        refine Acc.intro (b :: u) ?_
        intro y hy
        obtain ⟨hy1, _, hlex⟩ := hy
        obtain ⟨c, w, rfl, hw⟩ := cons_of_length_succ y K hy1
        rw [lexLt_cons_cons] at hlex
        by_cases hcb : c < b
        · exact innerIH c hcb w hw
        · rw [if_neg hcb] at hlex
          by_cases hbc : b < c
          · rw [if_pos hbc] at hlex
            simp at hlex
          · rw [if_neg hbc] at hlex
            have hc_eq : c = b := by omega
            subst hc_eq
            exact ihAcc w ⟨hw, hu, hlex⟩ c innerIH hw)

/-- The graded lexicographic relation is well-founded at every grade. -/
theorem lexRel_wf : ∀ (K : Nat), WellFounded (lexRel K) := by
  intro K
  induction K with
  | zero =>
    refine ⟨?_⟩
    intro y
    refine Acc.intro y ?_
    intro x hx
    obtain ⟨hx1, hy1, hlex⟩ := hx
    have hxnil : x = [] := length_zero_eq_nil x hx1
    have hynil : y = [] := length_zero_eq_nil y hy1
    subst hxnil
    subst hynil
    rw [lexLt_nil_nil] at hlex
    simp at hlex
  | succ K ih =>
    refine ⟨?_⟩
    intro s
    by_cases hs : s.length = K + 1
    · exact lexRel_acc_step K (fun t ht => WellFounded.apply ih t) s hs
    · refine Acc.intro s ?_
      intro x hx
      obtain ⟨_, hs1, _⟩ := hx
      omega

/-- Accessibility transfers from the graded lex relation to
    `shapeOrder`: shorter lists come from the caller's hypothesis,
    same-length lex-smaller lists from the graded proof. -/
theorem acc_shapeOrder_of_lexAcc (K : Nat) (x : Partition)
    (hx : x.length = K)
    (hshort : ∀ z : Partition, z.length < K → Acc shapeOrder z)
    (hacc : Acc (lexRel K) x) :
    Acc shapeOrder x := by
  revert hx hshort
  induction hacc with
  | intro x hacc ihAcc =>
    intro hx hshort
    refine Acc.intro x ?_
    intro z hz
    rw [shapeOrder_eq] at hz
    cases hz with
    | inl hlt =>
      exact hshort z (by omega)
    | inr h =>
      obtain ⟨hlen, hlex⟩ := h
      exact ihAcc z ⟨by omega, hx, hlex⟩ (by omega) hshort

/-- Every length-bounded list is accessible (strong induction on the
    bound; same-length lex predecessors go through the graded
    relation). -/
theorem accOfLen : ∀ (K : Nat) (l : Partition),
    l.length ≤ K → Acc shapeOrder l := by
  exact b8StrongNat (fun K => ∀ l : Partition, l.length ≤ K → Acc shapeOrder l)
    (fun K outerIH l hl => by
      refine Acc.intro l ?_
      intro z hz
      rw [shapeOrder_eq] at hz
      cases hz with
      | inl hlt =>
        exact outerIH z.length (by omega) z (by omega)
      | inr h =>
        obtain ⟨hlen, hlex⟩ := h
        have hshort : ∀ w : Partition, w.length < z.length → Acc shapeOrder w := by
          intro w hw
          exact outerIH w.length (by omega) w (by omega)
        have haccZ : Acc (lexRel z.length) z :=
          WellFounded.apply (lexRel_wf z.length) z
        exact acc_shapeOrder_of_lexAcc z.length z rfl hshort haccZ)

/-- the design specification S2 justification `shapeOrder_wf`: the width-first order is
    well-founded — the future induction measure carrier. -/
theorem shapeOrder_wf : WellFounded shapeOrder :=
  ⟨fun l => accOfLen l.length l (Nat.le_refl _)⟩

/-- First-match position of `l` in `t` (`0` if absent). -/
def posOf : List (List Nat) → List Nat → Nat
  | [], _ => 0
  | a :: t, l => if a = l then 0 else posOf t l + 1

/-- A member's first-match position is in bounds. -/
theorem posOf_lt_length : ∀ (t : List (List Nat)) (l : List Nat),
    l ∈ t → posOf t l < t.length := by
  intro t
  induction t with
  | nil =>
    intro l hm
    exact (List.not_mem_nil hm).elim
  | cons a t' ih =>
    intro l hm
    simp only [List.mem_cons] at hm
    show (if a = l then 0 else posOf t' l + 1) < (a :: t').length
    by_cases heq : a = l
    · rw [if_pos heq]
      show (0 : Nat) < t'.length + 1
      omega
    · rw [if_neg heq]
      cases hm with
      | inl heq2 => exact absurd heq2.symm heq
      | inr hmem =>
        have h1 := ih l hmem
        show posOf t' l + 1 < t'.length + 1
        omega

/-- Position lookup returning an option (no partiality, no extra API). -/
def atPos : List (List Nat) → Nat → Option (List Nat)
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: t, n + 1 => atPos t n

/-- Lookup at the first-match position returns the member. -/
theorem atPos_posOf : ∀ (t : List (List Nat)) (l : List Nat),
    l ∈ t → atPos t (posOf t l) = some l := by
  intro t
  induction t with
  | nil =>
    intro l hm
    exact (List.not_mem_nil hm).elim
  | cons a t' ih =>
    intro l hm
    simp only [List.mem_cons] at hm
    by_cases heq : a = l
    · subst heq
      have hpos : posOf (a :: t') a = 0 := by
        show (if a = a then (0 : Nat) else posOf t' a + 1) = 0
        rw [if_pos rfl]
      rw [hpos]
      rfl
    · have hpos : posOf (a :: t') l = posOf t' l + 1 := by
        show (if a = l then (0 : Nat) else posOf t' l + 1) = posOf t' l + 1
        rw [if_neg heq]
      rw [hpos]
      cases hm with
      | inl heq2 => exact absurd heq2.symm heq
      | inr hmem =>
        show atPos t' (posOf t' l) = some l
        exact ih l hmem

/-- the design specification S2 index: position of a census member as `Fin (shapeCount wt)`.
    the design specification sketches this totally; the honest constructible form carries the
    membership proof (a non-member has no position). -/
def shapeIndex (wt : Nat) (l : Partition) (h : l ∈ shapeCensus wt) :
    Fin (shapeCount wt) :=
  ⟨posOf (shapeCensus wt) l, by
    have h1 := posOf_lt_length (shapeCensus wt) l h
    show posOf (shapeCensus wt) l < (shapeCensus wt).length
    exact h1⟩

/-- the design specification S2 justification `shapeIndex_correct`: the index round-trips
    through the census. -/
theorem shapeIndex_correct (wt : Nat) (l : Partition) (h : l ∈ shapeCensus wt) :
    atPos (shapeCensus wt) (shapeIndex wt l h).val = some l := by
  exact atPos_posOf (shapeCensus wt) l h

/-- Adjacent-sortedness for the census order: each adjacent pair is
    ordered (or equal). Transitivity lifts this to arbitrary pairs. -/
def SortedOrder : List (List Nat) → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => (shapeOrder a b ∨ a = b) ∧ SortedOrder (b :: t)

/-- In an ordered list, the head is below-or-equal to every later entry. -/
theorem sorted_mem_ge : ∀ (t : List (List Nat)) (a y : List Nat),
    SortedOrder (a :: t) → y ∈ t → shapeOrder a y ∨ a = y := by
  intro t
  induction t with
  | nil =>
    intro a y _hs hm
    exact (List.not_mem_nil hm).elim
  | cons b t' ih =>
    intro a y hs hm
    have hs' : (shapeOrder a b ∨ a = b) ∧ SortedOrder (b :: t') := hs
    obtain ⟨hab, hrest⟩ := hs'
    simp only [List.mem_cons] at hm
    cases hm with
    | inl heq =>
      subst heq
      exact hab
    | inr hmem =>
      have h2 := ih b y hrest hmem
      cases h2 with
      | inl hby =>
        cases hab with
        | inl hab' => exact Or.inl (shapeOrder_trans a b y hab' hby)
        | inr heqab =>
          subst heqab
          exact Or.inl hby
      | inr heqby =>
        subst heqby
        exact hab

/-- Filtering preserves order. -/
theorem sorted_filter : ∀ (t : List (List Nat)) (p : List Nat → Bool),
    SortedOrder t → SortedOrder (t.filter p) := by
  intro t
  induction t with
  | nil =>
    intro p _hs
    exact True.intro
  | cons a t' ih =>
    intro p hs
    cases t' with
    | nil =>
      by_cases hpa : p a = true
      · have hflt : ((a :: []).filter p) = [a] := by simp [hpa]
        rw [hflt]
        exact True.intro
      · have hflt : ((a :: []).filter p) = [] := by simp [hpa]
        rw [hflt]
        exact True.intro
    | cons b t'' =>
      by_cases hpa : p a = true
      · have hs' : (shapeOrder a b ∨ a = b) ∧ SortedOrder (b :: t'') := hs
        obtain ⟨_hab, hrest⟩ := hs'
        have hflt : ((a :: b :: t'').filter p) = a :: ((b :: t'').filter p) := by
          simp only [List.filter_cons, hpa, ↓reduceIte]
        rw [hflt]
        have htail := ih p hrest
        by_cases hemp : ((b :: t'').filter p) = []
        · rw [hemp]
          exact True.intro
        · obtain ⟨c, rest, hflt2⟩ := List.exists_cons_of_ne_nil hemp
          rw [hflt2] at htail ⊢
          have hfltmem : c ∈ ((b :: t'').filter p) := by
            rw [hflt2]
            exact List.mem_cons_self
          have hmem : c ∈ (b :: t'') := (List.mem_filter.mp hfltmem).1
          have hge := sorted_mem_ge (b :: t'') a c hs hmem
          exact ⟨hge, htail⟩
      · have hs' : (shapeOrder a b ∨ a = b) ∧ SortedOrder (b :: t'') := hs
        have hflt : ((a :: b :: t'').filter p) = ((b :: t'').filter p) := by
          simp [List.filter_cons, hpa]
        rw [hflt]
        exact ih p hs'.2

/-- Prefixing every entry preserves order (equal heads recurse). -/
theorem sorted_map_prefix (a : Nat) :
    ∀ (t : List (List Nat)),
      SortedOrder t → SortedOrder (t.map fun x => a :: x) := by
  intro t
  induction t with
  | nil =>
    intro _hs
    exact True.intro
  | cons y t' ih =>
    cases t' with
    | nil =>
      intro _hs
      exact True.intro
    | cons b t'' =>
      intro hs
      have hs' : (shapeOrder y b ∨ y = b) ∧ SortedOrder (b :: t'') := hs
      obtain ⟨hab, hrest⟩ := hs'
      have hpair : shapeOrder (a :: y) (a :: b) ∨ (a :: y) = (a :: b) := by
        cases hab with
        | inl h =>
          rw [shapeOrder_eq] at h
          cases h with
          | inl hlen =>
            have e1 : (a :: y).length = y.length + 1 := rfl
            have e2 : (a :: b).length = b.length + 1 := rfl
            have hlt : (a :: y).length < (a :: b).length := by omega
            rw [shapeOrder_eq]
            exact Or.inl (Or.inl hlt)
          | inr h =>
            obtain ⟨hlen, hlex⟩ := h
            have e1 : (a :: y).length = y.length + 1 := rfl
            have e2 : (a :: b).length = b.length + 1 := rfl
            have hlen' : (a :: y).length = (a :: b).length := by omega
            have hlex' : lexLt (a :: y) (a :: b) = true := by
              rw [lexLt_cons_cons]
              have haa : ¬ a < a := by omega
              rw [if_neg haa, if_neg haa]
              exact hlex
            rw [shapeOrder_eq]
            exact Or.inl (Or.inr ⟨hlen', hlex'⟩)
        | inr heq =>
          subst heq
          exact Or.inr rfl
      exact ⟨hpair, ih hrest⟩

/-- Appending ordered lists with an ordered cross-boundary stays ordered. -/
theorem sorted_append : ∀ (l₁ l₂ : List (List Nat)),
    SortedOrder l₁ → SortedOrder l₂ →
    (∀ x ∈ l₁, ∀ y ∈ l₂, shapeOrder x y ∨ x = y) →
    SortedOrder (l₁ ++ l₂) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ _hs hs₂ _hcross
    exact hs₂
  | cons a t' ih =>
    intro l₂ hs₁ hs₂ hcross
    cases t' with
    | nil =>
      cases l₂ with
      | nil => exact True.intro
      | cons b t'' =>
        exact ⟨hcross a List.mem_cons_self b List.mem_cons_self, hs₂⟩
    | cons b t'' =>
      have hs₁' : (shapeOrder a b ∨ a = b) ∧ SortedOrder (b :: t'') := hs₁
      obtain ⟨hab, hrest⟩ := hs₁'
      have htail : SortedOrder ((b :: t'') ++ l₂) :=
        ih l₂ hrest hs₂
          (fun x hx y hy => hcross x (List.mem_cons_of_mem _ hx) y hy)
      exact ⟨hab, htail⟩

/-- One range-fiber step of the exact-length generator. -/
theorem flatMap_range_succ (f : Nat → List (List Nat)) (m : Nat) :
    ((List.range (m + 1)).flatMap f) = ((List.range m).flatMap f) ++ f m := by
  have hnil : List.flatMap f ([] : List Nat) = [] := by rfl
  have h1 : m + 1 = m.succ := by omega
  rw [h1, List.range_succ, List.flatMap_append, List.flatMap_cons, hnil,
    List.append_nil]

/-- A fiber family ordered across fibers enumerates in order. -/
theorem sorted_fiber_range (m : Nat) (fiber : Nat → List (List Nat))
    (hsorted : ∀ a, SortedOrder (fiber a))
    (hcross : ∀ a b, a < b → ∀ x ∈ fiber a, ∀ y ∈ fiber b,
      shapeOrder x y ∨ x = y) :
    SortedOrder ((List.range m).flatMap fiber) := by
  induction m with
  | zero => exact True.intro
  | succ m ih =>
    rw [flatMap_range_succ fiber m]
    apply sorted_append
    · exact ih
    · exact hsorted m
    · intro x hx y hy
      obtain ⟨a, ha, hxa⟩ := List.mem_flatMap.mp hx
      have ham : a < m := List.mem_range.mp ha
      exact hcross a m ham x hxa y hy

/-- The exact-length generator enumerates in order (fibers share one
    length, so heads decide the cross-fiber comparison). -/
theorem allLists_sorted : ∀ (k m : Nat), SortedOrder (allLists k m) := by
  intro k
  induction k with
  | zero =>
    intro m
    exact True.intro
  | succ k ih =>
    intro m
    show SortedOrder
      ((List.range m).flatMap fun a => (allLists k m).map fun l => a :: l)
    apply sorted_fiber_range
    · intro a
      exact sorted_map_prefix a (allLists k m) (ih m)
    · intro a b hab x hx y hy
      obtain ⟨x', hx'mem, hx'eq⟩ := List.mem_map.mp hx
      obtain ⟨y', hy'mem, hy'eq⟩ := List.mem_map.mp hy
      have hx' : a :: x' = x := hx'eq
      have hy' : b :: y' = y := hy'eq
      have hxlen : x'.length = k := (mem_allLists.mp hx'mem).1
      have hylen : y'.length = k := (mem_allLists.mp hy'mem).1
      have ex : x.length = k + 1 := by
        rw [← hx']
        show x'.length + 1 = k + 1
        omega
      have ey : y.length = k + 1 := by
        rw [← hy']
        show y'.length + 1 = k + 1
        omega
      have hlex : lexLt x y = true := by
        rw [← hx', ← hy', lexLt_cons_cons, if_pos hab]
      exact Or.inl (Or.inr ⟨by omega, hlex⟩)

/-- The bounded generator enumerates in order (shorter lengths first). -/
theorem allListsUpTo_sorted : ∀ (k m : Nat), SortedOrder (allListsUpTo k m) := by
  intro k
  induction k with
  | zero =>
    intro m
    exact True.intro
  | succ k ih =>
    intro m
    show SortedOrder (allListsUpTo k m ++ allLists (k + 1) m)
    apply sorted_append
    · exact ih m
    · exact allLists_sorted (k + 1) m
    · intro x hx y hy
      have hxlen : x.length ≤ k := allListsUpTo_mem_length k m x hx
      have hylen : y.length = k + 1 := (mem_allLists.mp hy).1
      exact Or.inl (Or.inl (by omega))

/-- the design specification S1 justification:
    the B7 census is ordered by `shapeOrder`. Filtering preserves order. -/
theorem shapeCensus_sorted : ∀ (wt : Nat), SortedOrder (shapeCensus wt) := by
  intro wt
  show SortedOrder ((allListsUpTo wt (wt + 1)).filter fun l => isPartitionOf l wt)
  exact sorted_filter _ _ (allListsUpTo_sorted wt (wt + 1))

/-- Census membership witness used by the executable spot-values below. -/
theorem mem_22_4 : ([2, 2] : Partition) ∈ shapeCensus 4 := by
  apply shapeCensus_complete
  rfl

/- Executable spot-values (compiled execution evidence; outputs appear in
   the isolated build log). -/
#eval ("lex89", lexLt [2, 2] [3, 1])
#eval ("lex98", lexLt [3, 1] [2, 2])
#eval ("ordA", decide (shapeOrder [2] [1, 1]))
#eval ("ordB", decide (shapeOrder [1, 1] [2]))
#eval ("idx22", (shapeIndex 4 [2, 2] mem_22_4).val)
#eval ("at1", atPos (shapeCensus 4) 1)
#eval ("cnt4", shapeCount 4)

/- Axiom audit (outputs appear in the isolated build log; expected: no
   unfinished-proof axiom). -/
#print axioms shapeOrder_wf
#print axioms shapeIndex_correct
#print axioms shapeCensus_sorted
#print axioms accOfLen
#print axioms sorted_append

end OddMath.LrAdapterB8
