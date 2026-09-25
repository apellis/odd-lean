import OddMath.Frontier.EKRskBijectionControls
import OddMath.Frontier.CompleteTableauExpansion
import OddMath.Frontier.TableauStripBijection

/-!
# EK Theorem 4.3 (RSK correspondence) and (4.4)

Source: Ellis–Khovanov, arXiv:1107.5610v2, §4.1, pp. 32–33 (classical RSK, cited from Fulton).

Printed (4.3): `RSK : {N-matrices A with row(A)=µ and col(A)=ρ} → {pairs (P,Q) of semistandard
Young tableaux of the same shape, with cont(P)=µ and cont(Q)=ρ}` is a bijection; printed (4.4):
`N_{µρ} = ∑_{λ ⊢ n} K_{λµ} K_{λρ}`.  Here `row(A)`/`col(A)` are the row/column sums (EK p.24).

Frozen RSK (the fixed specification, identical to EK's p.32 description): read the two-line array
lexicographically, `P_k := TableauInsertion.insert P_{k-1} v_k`, `Q_k := Q_{k-1}` with `u_k` put in
the unique new cell of `P_k`.  Since `v` are COLUMN indices, `cont(P) = col(A) = ρ` and
`cont(Q) = row(A) = µ` (this is also what EK's own Examples 4.4/4.5 print).  Consequently:

* `rsk_bijective`: RSK is a bijection onto pairs with `cont(P) = ρ`, `cont(Q) = µ` (all
  compositions µ, ρ, any numbers of rows/columns, including zero parts).
* `printed_codomain_obstruction`/`ex45_printed_obstruction`: whenever µ ≠ ρ (as contents), NO
  matrix is sent into the printed codomain `cont(P)=µ, cont(Q)=ρ`; EK's own Example 4.5 data
  (µ=(2,2), ρ=(2,1,1), four matrices) is an explicit machine-checked instance.  The printed (4.3)
  is therefore false as literally printed (a transposition of the two content conditions); the
  failure is of well-definedness into the printed codomain, not of cardinality.
* `ek_eq_4_4`: (4.4) exactly as printed, with UNSIGNED Kostka numbers
  `K⁰_{λc} = #(tableauxOfContent λ c)`, summed over all Young diagrams λ with `|µ|` cells.
* `rsk_eq_frozen`: the map used is literally the frozen entry-by-entry fold of existing
  `TableauInsertion.insert` with recording (both `P` and every entry of `Q`).

Conventions: English zero-based cells; `Fin n` letter `a` is paper label `a.val+1`; matrix row
`i : Fin m` is paper label `i.val+1`.  `TableauInsertion`/`TableauInsertionInverse` are not
modified; inverse steps use the existing strip reconstruction (`TableauStripBijection`).
-/

namespace OddMath.Frontier.EKRskBijection
open scoped BigOperators
open TableauSign TableauEvaluation TableauContent TableauStripCorners DegreeShapes
open CompleteTableauExpansion (extendTableau extend_old extend_new extend_bounded extend_content
  prefixShape prefixTableau prefix_entry prefix_bounded prefix_horizontal prefix_extend_shape
  mem_prefix)

/-! ## Basic carriers -/

abbrev Tab (n : ℕ) (la : YoungDiagram) := {T : PositiveTableau la // InAlphabet n T}
abbrev St (n : ℕ) := TableauWordInsertion.State n

/-- Pairs of tableaux of a common shape; `P` has letters `≤ n`, `Q` has labels `≤ m`. -/
abbrev Pairs (n m : ℕ) := Σ la : YoungDiagram, Tab n la × Tab m la

def Pairs.pState {n m : ℕ} (z : Pairs n m) : St n := ⟨z.1, z.2.1⟩
def Pairs.qState {n m : ℕ} (z : Pairs n m) : St m := ⟨z.1, z.2.2⟩

theorem state_ext {n : ℕ} {μ ν : YoungDiagram} (h : μ = ν) (S : Tab n μ) (T : Tab n ν)
    (he : ∀ p ∈ μ.cells, S.1.entry p.1 p.2 = T.1.entry p.1 p.2) :
    (⟨μ, S⟩ : St n) = ⟨ν, T⟩ := by
  subst h
  have hST : S = T := Subtype.ext (ext_cells he)
  subst hST
  rfl

theorem pairs_ext {n m : ℕ} {z w : Pairs n m} (hp : z.pState = w.pState)
    (hq : z.qState = w.qState) : z = w := by
  obtain ⟨a, P, Q⟩ := z
  obtain ⟨b, P', Q'⟩ := w
  simp only [Pairs.pState, Pairs.qState, Sigma.mk.inj_iff] at hp hq
  obtain ⟨rfl, hP⟩ := hp
  obtain ⟨-, hQ⟩ := hq
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hQ
  rfl

/-! ## Words of matrix rows -/

theorem rowWord_sorted {n : ℕ} (r : Fin n → ℕ) : (rowWord r).Sorted (· ≤ ·) := by
  unfold rowWord List.Sorted
  rw [List.pairwise_flatMap]
  refine ⟨fun a _ => ?_, ?_⟩
  · rw [List.pairwise_replicate]; exact Or.inr le_rfl
  · refine (List.pairwise_lt_finRange n).imp ?_
    intro a b hab x hx y hy
    rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
    exact hab.le

theorem rowWord_count {n : ℕ} (r : Fin n → ℕ) (j : Fin n) : (rowWord r).count j = r j := by
  unfold rowWord
  rw [List.count_flatMap]
  have h : (List.map (List.count j ∘ fun i => List.replicate (r i) i) (List.finRange n)) =
      (List.finRange n).map (fun i => if i = j then r i else 0) := by
    apply List.map_congr_left
    intro i _
    simp [List.count_replicate]
  rw [h, ← Fin.sum_univ_def, Finset.sum_ite_eq' Finset.univ j]
  simp

theorem rowWord_length {n : ℕ} (r : Fin n → ℕ) : (rowWord r).length = ∑ j, r j := by
  unfold rowWord
  rw [List.length_flatMap, Fin.sum_univ_def]
  simp

theorem rowWord_injective {n : ℕ} : Function.Injective (rowWord (n := n)) := by
  intro r r' h
  funext j
  rw [← rowWord_count r j, ← rowWord_count r' j, h]

theorem rowWord_count_eq {n : ℕ} (w : List (Fin n)) (hw : w.Sorted (· ≤ ·)) :
    rowWord (fun j => w.count j) = w := by
  apply List.eq_of_perm_of_sorted _ (rowWord_sorted _) hw
  rw [List.perm_iff_count]
  intro a
  rw [rowWord_count]

/-! ## Contents -/

/-- Content of a composition `c`, paper labels `1, …, k`. -/
noncomputable def compContent {k : ℕ} (c : Fin k → ℕ) : ℕ →₀ ℕ :=
  ∑ i, Finsupp.single (i.val + 1) (c i)

theorem compContent_apply {k : ℕ} (c : Fin k → ℕ) (i : Fin k) :
    compContent c (i.val + 1) = c i := by
  unfold compContent
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (Fin.ext (by omega))
  · simp

theorem compContent_injective {k : ℕ} : Function.Injective (compContent (k := k)) := by
  intro c d h
  funext i
  rw [← compContent_apply c i, ← compContent_apply d i, h]

theorem compContent_above {k : ℕ} (c : Fin k → ℕ) {e : ℕ} (he : k < e ∨ e = 0) :
    compContent c e = 0 := by
  unfold compContent
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finsupp.single_apply, if_neg]
  have := i.isLt
  omega

theorem compContent_total {k : ℕ} (c : Fin k → ℕ) :
    (compContent c).sum (fun _ x => x) = ∑ i, c i := by
  unfold compContent
  rw [← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp only [Finsupp.sum_single_index (h := fun _ x : ℕ => x) rfl]

/-- A tableau whose content is a composition of length `k` has entries `≤ k`. -/
theorem bounded_of_content {k : ℕ} {la : YoungDiagram} (T : PositiveTableau la)
    (c : Fin k → ℕ) (h : content T = compContent c) : InAlphabet k T := by
  intro p hp
  have hm := entry_mem_support T hp
  rw [h, Finsupp.mem_support_iff] at hm
  by_contra hn
  exact hm (compContent_above c (Or.inl (by omega)))

/-- Word content as a composition content. -/
theorem word_content {n : ℕ} (w : List (Fin n)) :
    (w.map fun a => Finsupp.single (a.val + 1) 1).sum =
      ∑ j : Fin n, Finsupp.single (j.val + 1) (w.count j) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons, List.sum_cons, ih]
    have h : ∀ j : Fin n, Finsupp.single (j.val + 1) ((a :: w).count j) =
        Finsupp.single (j.val + 1) (w.count j) +
          Finsupp.single (j.val + 1) (if a = j then 1 else 0) := by
      intro j
      rw [List.count_cons, Finsupp.single_add]
      simp
    simp only [h, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]
      simp
    · simp

theorem insert_content_eq (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (a : Fin n) :
    content (TableauInsertion.insert n μ T hT a).tableau =
      content T + Finsupp.single (a.val + 1) 1 := by
  ext k
  rw [Finsupp.add_apply, Finsupp.single_apply]
  rcases k with _ | i
  · simp
  · by_cases hi : i < n
    · rw [TableauInsertion.insert_content n μ T hT a ⟨i, hi⟩]
      congr 1
      by_cases h : (⟨i, hi⟩ : Fin n) = a
      · subst h; simp
      · rw [if_neg h, if_neg]
        intro h'
        exact h (Fin.ext (by simp at h' ⊢; omega))
    · have ha := a.isLt
      rw [CompleteTableauExpansion.content_above _ n (TableauInsertion.insert n μ T hT a).bounded
        (by omega), CompleteTableauExpansion.content_above _ n hT (by omega), if_neg (by omega)]
      simp

theorem run_content (n : ℕ) (S : St n) (w : List (Fin n)) :
    content (TableauWordInsertion.run n S w).1.2.1 =
      content S.2.1 + (w.map fun a => Finsupp.single (a.val + 1) 1).sum := by
  induction w generalizing S with
  | nil => simp [TableauWordInsertion.run]
  | cons a w ih =>
    change content (TableauWordInsertion.run n
        ⟨(TableauInsertion.insert n S.1 S.2.1 S.2.2 a).shape,
          ⟨(TableauInsertion.insert n S.1 S.2.1 S.2.2 a).tableau,
            (TableauInsertion.insert n S.1 S.2.1 S.2.2 a).bounded⟩⟩ w).1.2.1 = _
    rw [ih]
    change content (TableauInsertion.insert n S.1 S.2.1 S.2.2 a).tableau + _ = _
    rw [insert_content_eq, List.map_cons, List.sum_cons, add_assoc]

theorem run_card (n : ℕ) (S : St n) (w : List (Fin n)) :
    ((TableauWordInsertion.run n S w).1.1.cells \ S.1.cells).card = w.length := by
  have hs := TableauWordInsertion.run_spec n S w
  rw [← hs.2.2.2, List.toFinset_card_of_nodup hs.2.1]
  exact hs.1

/-! ## The RSK map, row block by row block -/

theorem run_horizontal' (n : ℕ) (S : St n) (r : Fin n → ℕ) :
    Horizontal S.1 (TableauWordInsertion.run n S (rowWord r)).1.1 :=
  ⟨(TableauWordInsertion.run_spec n S (rowWord r)).2.2.1,
    (TableauWordInsertion.run_horizontal n S (rowWord r) (rowWord_sorted r)).2⟩

/-- Insert one matrix row (weakly increasing word) into `P`; record label `m+1` in `Q`. -/
noncomputable def step (n m : ℕ) (z : Pairs n m) (r : Fin n → ℕ) : Pairs n (m + 1) :=
  ⟨(TableauWordInsertion.run n z.pState (rowWord r)).1.1,
    ((TableauWordInsertion.run n z.pState (rowWord r)).1.2,
      ⟨extendTableau z.2.2.1 m z.2.2.2 (run_horizontal' n z.pState r),
        extend_bounded z.2.2.1 m z.2.2.2 (run_horizontal' n z.pState r)⟩)⟩

theorem emptyBounded (k : ℕ) : InAlphabet k emptyTableau := by
  intro p hp
  exact absurd hp (by simp)

noncomputable def emptyPairs (n : ℕ) : Pairs n 0 :=
  ⟨⊥, (⟨emptyTableau, emptyBounded n⟩, ⟨emptyTableau, emptyBounded 0⟩)⟩

/-- RSK by recursion on the number of rows (last row inserted last). -/
noncomputable def rskRec (n : ℕ) : (m : ℕ) → (Fin m → Fin n → ℕ) → Pairs n m
  | 0, _ => emptyPairs n
  | m + 1, A => step n m (rskRec n m (Fin.init A)) (A (Fin.last m))

/-! ## Contents of the RSK pair -/

theorem step_Q_content (n m : ℕ) (z : Pairs n m) (r : Fin n → ℕ) :
    content (step n m z r).2.2.1 = content z.2.2.1 + Finsupp.single (m + 1) (∑ j, r j) := by
  show content (extendTableau z.2.2.1 m z.2.2.2 (run_horizontal' n z.pState r)) = _
  rw [extend_content]
  congr 2
  exact (run_card n z.pState (rowWord r)).trans (rowWord_length r)

theorem rskRec_P_content (n : ℕ) : ∀ (m : ℕ) (A : Fin m → Fin n → ℕ),
    content (rskRec n m A).2.1.1 = compContent (fun j => ∑ i, A i j)
  | 0, A => by
    change content emptyTableau = _
    rw [content_empty]
    unfold compContent
    simp
  | m + 1, A => by
    change content (TableauWordInsertion.run n (rskRec n m (Fin.init A)).pState
      (rowWord (A (Fin.last m)))).1.2.1 = _
    rw [run_content, word_content]
    change content (rskRec n m (Fin.init A)).2.1.1 + _ = _
    rw [rskRec_P_content n m (Fin.init A)]
    unfold compContent
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finsupp.single_add, rowWord_count]
    congr 1
    dsimp only
    rw [Fin.sum_univ_castSucc]
    rfl

theorem rskRec_Q_content (n : ℕ) : ∀ (m : ℕ) (A : Fin m → Fin n → ℕ),
    content (rskRec n m A).2.2.1 = compContent (fun i => ∑ j, A i j)
  | 0, A => by
    change content emptyTableau = _
    rw [content_empty]
    unfold compContent
    simp
  | m + 1, A => by
    show content (step n m (rskRec n m (Fin.init A)) (A (Fin.last m))).2.2.1 = _
    rw [step_Q_content, rskRec_Q_content n m (Fin.init A)]
    unfold compContent
    rw [Fin.sum_univ_castSucc (f := fun i => Finsupp.single (i.val + 1) (∑ j, A i j))]
    simp [Fin.init]

/-! ## Bijectivity of one row step -/

/-- Split off the largest label `m+1` of the recording tableau. -/
noncomputable def pre (m : ℕ) (Q : St (m + 1)) : St m :=
  ⟨prefixShape Q.2.1 m, ⟨prefixTableau Q.2.1 m, prefix_bounded Q.2.1 m⟩⟩

theorem pre_step (n m : ℕ) (z : Pairs n m) (r : Fin n → ℕ) :
    pre m (step n m z r).qState = z.qState := by
  apply state_ext (prefix_extend_shape _ _ _ _)
  intro p hp
  have hp' : p ∈ z.1.cells := by
    have h := prefix_extend_shape z.2.2.1 m z.2.2.2 (run_horizontal' n z.pState r)
    change p ∈ (prefixShape (extendTableau z.2.2.1 m z.2.2.2
      (run_horizontal' n z.pState r)) m).cells at hp
    rw [h] at hp
    exact hp
  change (prefixTableau (extendTableau z.2.2.1 m z.2.2.2 (run_horizontal' n z.pState r)) m).entry
    p.1 p.2 = z.2.2.1.entry p.1 p.2
  rw [prefix_entry _ _ hp, extend_old _ _ _ _ hp']

theorem step_injective (n m : ℕ) {z z' : Pairs n m} {r r' : Fin n → ℕ}
    (h : step n m z r = step n m z' r') : z = z' ∧ r = r' := by
  have hP : (TableauWordInsertion.run n z.pState (rowWord r)).1 =
      (TableauWordInsertion.run n z'.pState (rowWord r')).1 :=
    congrArg Pairs.pState h
  have hQ : z.qState = z'.qState := by
    have := congrArg (fun y => pre m (Pairs.qState y)) h
    simpa only [pre_step] using this
  have hshape : z.1 = z'.1 := congrArg (fun s : St m => s.1) hQ
  have hu := TableauStripUniqueness.weak_preimage_unique n z.pState z'.pState (rowWord r)
    (rowWord r') hshape (rowWord_sorted r) (rowWord_sorted r') hP
  simp only [Prod.mk.injEq] at hu
  exact ⟨pairs_ext hu.1 hQ, rowWord_injective hu.2⟩

theorem step_surjective (n m : ℕ) (y : Pairs n (m + 1)) :
    ∃ z r, step n m z r = y := by
  obtain ⟨la, P, Q⟩ := y
  have hh := prefix_horizontal Q.1 m Q.2
  obtain ⟨⟨S', w⟩, ⟨hS', hw, -, hrun⟩, -⟩ :=
    TableauStripBijection.strip_exists_unique n (prefixShape Q.1 m) ⟨la, P⟩ hh
  obtain ⟨μ', T'⟩ := S'
  dsimp only at hS' hw hrun
  subst hS'
  refine ⟨⟨prefixShape Q.1 m, T', ⟨prefixTableau Q.1 m, prefix_bounded Q.1 m⟩⟩,
    fun j => w.count j, ?_⟩
  have hR : (TableauWordInsertion.run n ⟨prefixShape Q.1 m, T'⟩
      (rowWord fun j => w.count j)).1 = ⟨la, P⟩ := by
    rw [rowWord_count_eq w hw]; exact hrun
  have hsh := congrArg Sigma.fst hR
  apply pairs_ext
  · exact hR
  · apply state_ext hsh
    intro p hp
    by_cases hm : p ∈ (prefixShape Q.1 m).cells
    · show (extendTableau (prefixTableau Q.1 m) m (prefix_bounded Q.1 m)
        (run_horizontal' n ⟨prefixShape Q.1 m, T'⟩ (fun j => w.count j))).entry p.1 p.2 =
        Q.1.entry p.1 p.2
      rw [extend_old _ _ _ _ hm, prefix_entry _ _ hm]
    · show (extendTableau (prefixTableau Q.1 m) m (prefix_bounded Q.1 m)
        (run_horizontal' n ⟨prefixShape Q.1 m, T'⟩ (fun j => w.count j))).entry p.1 p.2 =
        Q.1.entry p.1 p.2
      rw [extend_new _ _ _ _ (Finset.mem_sdiff.mpr ⟨hp, hm⟩)]
      have hp' : p ∈ la.cells := by
        have : p ∈ (TableauWordInsertion.run n ⟨prefixShape Q.1 m, T'⟩
          (rowWord fun j => w.count j)).1.1.cells := hp
        rw [hsh] at this; exact this
      have hb := Q.2 p hp'
      have hn : ¬ Q.1.entry p.1 p.2 ≤ m := fun he => hm ((mem_prefix Q.1 m p).mpr ⟨hp', he⟩)
      omega

/-! ## Bijectivity of RSK on all matrices -/

theorem pairs_zero_eq (n : ℕ) (z : Pairs n 0) : z = emptyPairs n := by
  have hbot : z.1 = ⊥ := by
    apply YoungDiagram.ext
    ext p
    simp only [YoungDiagram.cells_bot, Finset.not_mem_empty, iff_false]
    intro hp
    have h1 := z.2.2.1.positive (i := p.1) (j := p.2) hp
    have h2 := z.2.2.2 p hp
    omega
  apply pairs_ext
  · apply state_ext hbot
    intro p hp; rw [hbot] at hp; exact absurd hp (by simp)
  · apply state_ext hbot
    intro p hp; rw [hbot] at hp; exact absurd hp (by simp)

theorem rskRec_bijective (n : ℕ) : ∀ m : ℕ, Function.Bijective (rskRec n m)
  | 0 => by
    constructor
    · intro A B _; funext i; exact i.elim0
    · intro z; exact ⟨fun i => i.elim0, (pairs_zero_eq n z).symm⟩
  | m + 1 => by
    have ih := rskRec_bijective n m
    constructor
    · intro A B h
      obtain ⟨h1, h2⟩ := step_injective n m h
      have hi : Fin.init A = Fin.init B := ih.1 h1
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact h2
      · exact congrFun hi j
    · intro y
      obtain ⟨z, r, hz⟩ := step_surjective n m y
      obtain ⟨A', hA'⟩ := ih.2 z
      refine ⟨Fin.snoc (α := fun _ => Fin n → ℕ) A' r, ?_⟩
      change step n m (rskRec n m (Fin.init (Fin.snoc (α := fun _ => Fin n → ℕ) A' r)))
        (Fin.snoc (α := fun _ => Fin n → ℕ) A' r (Fin.last m)) = y
      rw [Fin.init_snoc, Fin.snoc_last, hA', hz]

/-! ## Agreement with the frozen entry-by-entry definition -/

/-- One frozen RSK step: existing row insertion of `v`; label `u+1` placed at the new cell. -/
noncomputable def foldStep (n : ℕ) (s : St n × (ℕ × ℕ → ℕ)) (x : ℕ × Fin n) :
    St n × (ℕ × ℕ → ℕ) :=
  let I := TableauInsertion.insert n s.1.1 s.1.2.1 s.1.2.2 x.2
  (⟨I.shape, ⟨I.tableau, I.bounded⟩⟩, fun p => if p = I.newCell then x.1 + 1 else s.2 p)

/-- The frozen RSK map: fold over EK's lexicographic two-line array. -/
noncomputable def rskFold {m n : ℕ} (A : Fin m → Fin n → ℕ) : St n × (ℕ × ℕ → ℕ) :=
  (twoLine A).foldl (foldStep n) (⟨⊥, ⟨emptyTableau, emptyBounded n⟩⟩, fun _ => 0)

theorem foldStep_block (n : ℕ) (u : ℕ) (w : List (Fin n)) (S : St n) (q : ℕ × ℕ → ℕ) :
    (w.map fun j => (u, j)).foldl (foldStep n) (S, q) =
      ((TableauWordInsertion.run n S w).1,
        fun p => if p ∈ (TableauWordInsertion.run n S w).2 then u + 1 else q p) := by
  induction w generalizing S q with
  | nil => simp [TableauWordInsertion.run]
  | cons a w ih =>
    rw [List.map_cons, List.foldl_cons]
    change (w.map fun j => (u, j)).foldl (foldStep n)
      (⟨(TableauInsertion.insert n S.1 S.2.1 S.2.2 a).shape,
        ⟨(TableauInsertion.insert n S.1 S.2.1 S.2.2 a).tableau,
          (TableauInsertion.insert n S.1 S.2.1 S.2.2 a).bounded⟩⟩,
        fun p => if p = (TableauInsertion.insert n S.1 S.2.1 S.2.2 a).newCell
          then u + 1 else q p) = _
    rw [ih]
    simp only [TableauWordInsertion.run, List.mem_cons]
    congr 1
    funext p
    by_cases h1 : p ∈ (TableauWordInsertion.run n
      ⟨(TableauInsertion.insert n S.1 S.2.1 S.2.2 a).shape,
        ⟨(TableauInsertion.insert n S.1 S.2.1 S.2.2 a).tableau,
          (TableauInsertion.insert n S.1 S.2.1 S.2.2 a).bounded⟩⟩ w).2
    · simp [h1]
    · by_cases h2 : p = (TableauInsertion.insert n S.1 S.2.1 S.2.2 a).newCell
      · simp [h2]
      · simp [h1, h2]

theorem twoLine_succ {m n : ℕ} (A : Fin (m + 1) → Fin n → ℕ) :
    twoLine A = twoLine (Fin.init A) ++ (rowWord (A (Fin.last m))).map fun j => (m, j) := by
  unfold twoLine
  rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
  simp [Fin.init]

theorem rsk_eq_frozen (n : ℕ) : ∀ (m : ℕ) (A : Fin m → Fin n → ℕ),
    (rskFold A).1 = (rskRec n m A).pState ∧
      ∀ p : ℕ × ℕ, (rskFold A).2 p = (rskRec n m A).2.2.1.entry p.1 p.2
  | 0, A => by
    refine ⟨rfl, fun p => ?_⟩
    change 0 = (emptyTableau).entry p.1 p.2
    rfl
  | m + 1, A => by
    obtain ⟨ih1, ih2⟩ := rsk_eq_frozen n m (Fin.init A)
    have hf : rskFold A =
        ((TableauWordInsertion.run n (rskFold (Fin.init A)).1 (rowWord (A (Fin.last m)))).1,
          fun p => if p ∈ (TableauWordInsertion.run n (rskFold (Fin.init A)).1
            (rowWord (A (Fin.last m)))).2 then m + 1 else (rskFold (Fin.init A)).2 p) := by
      unfold rskFold
      rw [twoLine_succ, List.foldl_append]
      exact foldStep_block n m _ _ _
    rw [hf]
    refine ⟨?_, fun p => ?_⟩
    · show (TableauWordInsertion.run n (rskFold (Fin.init A)).1 (rowWord (A (Fin.last m)))).1 = _
      rw [ih1]
      rfl
    show (if p ∈ (TableauWordInsertion.run n (rskFold (Fin.init A)).1
        (rowWord (A (Fin.last m)))).2 then m + 1 else (rskFold (Fin.init A)).2 p) =
      (extendTableau (rskRec n m (Fin.init A)).2.2.1 m (rskRec n m (Fin.init A)).2.2.2
        (run_horizontal' n (rskRec n m (Fin.init A)).pState (A (Fin.last m)))).entry p.1 p.2
    rw [ih1, ih2 p]
    have hs := (TableauWordInsertion.run_spec n (rskRec n m (Fin.init A)).pState
      (rowWord (A (Fin.last m)))).2.2.2
    have hmem : p ∈ (TableauWordInsertion.run n (rskRec n m (Fin.init A)).pState
        (rowWord (A (Fin.last m)))).2 ↔
        p ∈ (TableauWordInsertion.run n (rskRec n m (Fin.init A)).pState
          (rowWord (A (Fin.last m)))).1.1.cells \ (rskRec n m (Fin.init A)).1.cells := by
      rw [← List.mem_toFinset, hs]
      rfl
    by_cases hold : p ∈ (rskRec n m (Fin.init A)).1.cells
    · rw [extend_old _ _ _ _ hold, if_neg (fun h => (Finset.mem_sdiff.mp (hmem.mp h)).2 hold)]
    · by_cases hnew : p ∈ (TableauWordInsertion.run n (rskRec n m (Fin.init A)).pState
          (rowWord (A (Fin.last m)))).1.1.cells
      · rw [extend_new _ _ _ _ (Finset.mem_sdiff.mpr ⟨hnew, hold⟩),
          if_pos (hmem.mpr (Finset.mem_sdiff.mpr ⟨hnew, hold⟩))]
      · rw [if_neg (fun h => hnew (Finset.mem_sdiff.mp (hmem.mp h)).1)]
        rw [(rskRec n m (Fin.init A)).2.2.1.zeros' (by simpa using hold)]
        rw [(extendTableau (rskRec n m (Fin.init A)).2.2.1 m _ _).zeros' (by simpa using hnew)]

/-! ## Agreement with the computable list-level mirror used by the controls -/

/-- Invariant relating a frozen-fold state to a list-level mirror state. -/
def MirrorRel (n : ℕ) (s : St n × (ℕ × ℕ → ℕ)) (t : List (List (Fin n)) × List ((ℕ × ℕ) × ℕ)) :
    Prop :=
  TableauRowRecursion.rows n s.1.2.1 s.1.2.2 = t.1 ∧ ∀ p, s.2 p = qLook t.2 p

theorem mirrorRel_step (n : ℕ) (s : St n × (ℕ × ℕ → ℕ))
    (t : List (List (Fin n)) × List ((ℕ × ℕ) × ℕ)) (x : ℕ × Fin n) (h : MirrorRel n s t) :
    MirrorRel n (foldStep n s x) (mirrorStep t x) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · show TableauRowRecursion.rows n (TableauInsertion.insert n s.1.1 s.1.2.1 s.1.2.2 x.2).tableau
      (TableauInsertion.insert n s.1.1 s.1.2.1 s.1.2.2 x.2).bounded = _
    rw [TableauInsertion.insert_rows, h1]
    rfl
  · intro p
    show (if p = (TableauInsertion.insert n s.1.1 s.1.2.1 s.1.2.2 x.2).newCell then x.1 + 1
      else s.2 p) = qLook (t.2 ++ [(TableauRowRecursion.newCell n t.1 x.2, x.1 + 1)]) p
    rw [TableauInsertion.insert_newCell, h1]
    unfold qLook
    rw [List.reverse_append]
    by_cases hp : p = TableauRowRecursion.newCell n t.1 x.2
    · subst hp; simp
    · rw [if_neg hp, h2 p]
      unfold qLook
      have hne : ¬ (TableauRowRecursion.newCell n t.1 x.2 = p) := fun h => hp h.symm
      simp [hne]

theorem mirrorRel_fold (n : ℕ) (L : List (ℕ × Fin n)) :
    ∀ s t, MirrorRel n s t → MirrorRel n (L.foldl (foldStep n) s) (L.foldl mirrorStep t) := by
  induction L with
  | nil => intro s t h; exact h
  | cons x L ih => intro s t h; exact ih _ _ (mirrorRel_step n s t x h)

theorem rskFold_mirror {m n : ℕ} (A : Fin m → Fin n → ℕ) :
    MirrorRel n (rskFold A) (rskMirror A) := by
  apply mirrorRel_fold
  constructor
  · have h0 : (⊥ : YoungDiagram).colLen 0 = 0 := by
      have : ¬ (0 < (⊥ : YoungDiagram).colLen 0) := fun h =>
        YoungDiagram.not_mem_bot _ (YoungDiagram.mem_iff_lt_colLen.mpr h)
      omega
    simp [TableauRowRecursion.rows, h0]
  · intro p; simp [qLook]

theorem rows_congr {n : ℕ} (S S' : St n) (h : S = S') :
    TableauRowRecursion.rows n S.2.1 S.2.2 = TableauRowRecursion.rows n S'.2.1 S'.2.2 := by
  subst h; rfl

/-- The production RSK pair, read as row lists / recorded labels, is the controls' mirror. -/
theorem rskRec_mirror {m n : ℕ} (A : Fin m → Fin n → ℕ) :
    TableauRowRecursion.rows n (rskRec n m A).2.1.1 (rskRec n m A).2.1.2 = (rskMirror A).1 ∧
      ∀ p : ℕ × ℕ, (rskRec n m A).2.2.1.entry p.1 p.2 = qLook (rskMirror A).2 p := by
  obtain ⟨h1, h2⟩ := rskFold_mirror A
  obtain ⟨e1, e2⟩ := rsk_eq_frozen n m A
  refine ⟨?_, fun p => ?_⟩
  · rw [← h1]; exact (rows_congr _ _ e1).symm
  · rw [← e2 p, h2 p]

/-- Example 4.5, first printed matrix, for the PRODUCTION map: `P = 1 1 2 3`, `Q = 1 1 2 2`. -/
theorem ex45a_production :
    (TableauRowRecursion.rows 3 (rskRec 3 2 ex45a).2.1.1 (rskRec 3 2 ex45a).2.1.2).map
        (fun w => w.map fun a => a.val + 1) = [[1, 1, 2, 3]] ∧
      ((rskRec 3 2 ex45a).2.2.1.entry 0 0, (rskRec 3 2 ex45a).2.2.1.entry 0 1,
        (rskRec 3 2 ex45a).2.2.1.entry 0 2, (rskRec 3 2 ex45a).2.2.1.entry 0 3) = (1, 1, 2, 2) := by
  obtain ⟨h1, h2⟩ := rskRec_mirror ex45a
  rw [h1, h2 (0, 0), h2 (0, 1), h2 (0, 2), h2 (0, 3)]
  decide

theorem ex45d_production :
    (TableauRowRecursion.rows 3 (rskRec 3 2 ex45d).2.1.1 (rskRec 3 2 ex45d).2.1.2).map
        (fun w => w.map fun a => a.val + 1) = [[1, 1], [2, 3]] ∧
      ((rskRec 3 2 ex45d).2.2.1.entry 0 0, (rskRec 3 2 ex45d).2.2.1.entry 0 1,
        (rskRec 3 2 ex45d).2.2.1.entry 1 0, (rskRec 3 2 ex45d).2.2.1.entry 1 1) = (1, 1, 2, 2) := by
  obtain ⟨h1, h2⟩ := rskRec_mirror ex45d
  rw [h1, h2 (0, 0), h2 (0, 1), h2 (1, 0), h2 (1, 1)]
  decide

theorem ex45b_production :
    (TableauRowRecursion.rows 3 (rskRec 3 2 ex45b).2.1.1 (rskRec 3 2 ex45b).2.1.2).map
        (fun w => w.map fun a => a.val + 1) = [[1, 1, 3], [2]] ∧
      ((rskRec 3 2 ex45b).2.2.1.entry 0 0, (rskRec 3 2 ex45b).2.2.1.entry 0 1,
        (rskRec 3 2 ex45b).2.2.1.entry 0 2, (rskRec 3 2 ex45b).2.2.1.entry 1 0) = (1, 1, 2, 2) := by
  obtain ⟨h1, h2⟩ := rskRec_mirror ex45b
  rw [h1, h2 (0, 0), h2 (0, 1), h2 (0, 2), h2 (1, 0)]
  decide

theorem ex45c_production :
    (TableauRowRecursion.rows 3 (rskRec 3 2 ex45c).2.1.1 (rskRec 3 2 ex45c).2.1.2).map
        (fun w => w.map fun a => a.val + 1) = [[1, 1, 2], [3]] ∧
      ((rskRec 3 2 ex45c).2.2.1.entry 0 0, (rskRec 3 2 ex45c).2.2.1.entry 0 1,
        (rskRec 3 2 ex45c).2.2.1.entry 0 2, (rskRec 3 2 ex45c).2.2.1.entry 1 0) = (1, 1, 2, 2) := by
  obtain ⟨h1, h2⟩ := rskRec_mirror ex45c
  rw [h1, h2 (0, 0), h2 (0, 1), h2 (0, 2), h2 (1, 0)]
  decide

/-! ## Theorem 4.3 with fixed margins -/

variable {m n : ℕ}

/-- N-matrices with row sums `µ` and column sums `ρ` (EK: row(A) = µ, col(A) = ρ). -/
def Mat (μ : Fin m → ℕ) (ρ : Fin n → ℕ) :=
  {A : Fin m → Fin n → ℕ // (∀ i, ∑ j, A i j = μ i) ∧ ∀ j, ∑ i, A i j = ρ j}

/-- Codomain actually hit by the (frozen, EK-described) RSK map: `cont(P) = ρ`, `cont(Q) = µ`. -/
def Target (μ : Fin m → ℕ) (ρ : Fin n → ℕ) :=
  Σ la : YoungDiagram, {P : PositiveTableau la // content P = compContent ρ} ×
    {Q : PositiveTableau la // content Q = compContent μ}

/-- Codomain exactly as printed in EK (4.3): `cont(P) = µ`, `cont(Q) = ρ`. -/
def PrintedTarget (μ : Fin m → ℕ) (ρ : Fin n → ℕ) :=
  Σ la : YoungDiagram, {P : PositiveTableau la // content P = compContent μ} ×
    {Q : PositiveTableau la // content Q = compContent ρ}

/-- Forget bounds/contents: the raw pair of tableaux. -/
abbrev Raw := Σ la : YoungDiagram, PositiveTableau la × PositiveTableau la

def Pairs.raw (z : Pairs n m) : Raw := ⟨z.1, (z.2.1.1, z.2.2.1)⟩
def Target.raw {μ : Fin m → ℕ} {ρ : Fin n → ℕ} (t : Target μ ρ) : Raw := ⟨t.1, (t.2.1.1, t.2.2.1)⟩

theorem Pairs.raw_injective : Function.Injective (Pairs.raw (n := n) (m := m)) := by
  rintro ⟨a, P, Q⟩ ⟨b, P', Q'⟩ h
  simp only [Pairs.raw, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h⟩ := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj (eq_of_heq h)
  obtain rfl := Subtype.ext h1
  obtain rfl := Subtype.ext h2
  rfl

theorem Target.raw_injective {μ : Fin m → ℕ} {ρ : Fin n → ℕ} :
    Function.Injective (Target.raw (μ := μ) (ρ := ρ)) := by
  rintro ⟨a, P, Q⟩ ⟨b, P', Q'⟩ h
  simp only [Target.raw, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h⟩ := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj (eq_of_heq h)
  obtain rfl := Subtype.ext h1
  obtain rfl := Subtype.ext h2
  rfl

/-- The RSK map on fixed margins (frozen definition; see `rsk_eq_frozen`). -/
noncomputable def rsk (μ : Fin m → ℕ) (ρ : Fin n → ℕ) (A : Mat μ ρ) : Target μ ρ :=
  ⟨(rskRec n m A.1).1,
    (⟨(rskRec n m A.1).2.1.1, by
        rw [rskRec_P_content]; congr 1; funext j; exact A.2.2 j⟩,
      ⟨(rskRec n m A.1).2.2.1, by
        rw [rskRec_Q_content]; congr 1; funext i; exact A.2.1 i⟩)⟩

theorem rsk_raw (μ : Fin m → ℕ) (ρ : Fin n → ℕ) (A : Mat μ ρ) :
    (rsk μ ρ A).raw = (rskRec n m A.1).raw := rfl

/-- **EK Theorem 4.3 (corrected contents).** RSK is a bijection from N-matrices with
`row(A) = µ`, `col(A) = ρ` onto pairs of semistandard tableaux of a common shape with
`cont(P) = ρ = col(A)` and `cont(Q) = µ = row(A)`. -/
theorem rsk_bijective (μ : Fin m → ℕ) (ρ : Fin n → ℕ) : Function.Bijective (rsk μ ρ) := by
  constructor
  · intro A B h
    have h' := congrArg Target.raw h
    rw [rsk_raw, rsk_raw] at h'
    exact Subtype.ext ((rskRec_bijective n m).1 (Pairs.raw_injective h'))
  · rintro ⟨la, P, Q⟩
    let z : Pairs n m := ⟨la, (⟨P.1, bounded_of_content P.1 ρ P.2⟩,
      ⟨Q.1, bounded_of_content Q.1 μ Q.2⟩)⟩
    obtain ⟨A, hA⟩ := (rskRec_bijective n m).2 z
    have hrow : ∀ i, ∑ j, A i j = μ i := by
      have h := rskRec_Q_content n m A
      rw [hA] at h
      have h' := compContent_injective (h.symm.trans Q.2)
      exact fun i => congrFun h' i
    have hcol : ∀ j, ∑ i, A i j = ρ j := by
      have h := rskRec_P_content n m A
      rw [hA] at h
      have h' := compContent_injective (h.symm.trans P.2)
      exact fun j => congrFun h' j
    refine ⟨⟨A, hrow, hcol⟩, Target.raw_injective ?_⟩
    rw [rsk_raw]
    change (rskRec n m A).raw = z.raw
    rw [hA]

noncomputable def rskEquiv (μ : Fin m → ℕ) (ρ : Fin n → ℕ) : Mat μ ρ ≃ Target μ ρ :=
  Equiv.ofBijective _ (rsk_bijective μ ρ)

/-! ## The printed codomain: machine-checked obstruction -/

/-- Whenever µ ≠ ρ as contents, no matrix with row(A)=µ, col(A)=ρ is sent by RSK into the
printed codomain: its `P` has content ρ ≠ µ. -/
theorem printed_codomain_obstruction (μ : Fin m → ℕ) (ρ : Fin n → ℕ)
    (hne : compContent μ ≠ compContent ρ) (A : Mat μ ρ) :
    ¬ (content (rsk μ ρ A).2.1.1 = compContent μ ∧ content (rsk μ ρ A).2.2.1 = compContent ρ) := by
  rintro ⟨hP, -⟩
  exact hne (hP.symm.trans (rsk μ ρ A).2.1.2)

theorem ex45_contents_ne : compContent (![2, 2] : Fin 2 → ℕ) ≠ compContent (![2, 1, 1] : Fin 3 → ℕ) := by
  intro h
  have h3 := congrArg (fun c : ℕ →₀ ℕ => c 3) h
  simp only at h3
  rw [compContent_above _ (Or.inl (by norm_num)), show (3 : ℕ) = (2 : Fin 3).val + 1 from rfl,
    compContent_apply] at h3
  simp at h3

/-- EK Example 4.5 data (µ = (2,2) row sums, ρ = (2,1,1) column sums): the matrix set is
nonempty (the printed matrix `[[2,0,0],[0,1,1]]`) and EVERY such matrix is sent by the RSK map
outside the printed (4.3) codomain `cont(P) = µ, cont(Q) = ρ`. -/
theorem ex45_printed_obstruction :
    Nonempty (Mat (![2, 2] : Fin 2 → ℕ) (![2, 1, 1] : Fin 3 → ℕ)) ∧
    ∀ A : Mat (![2, 2] : Fin 2 → ℕ) (![2, 1, 1] : Fin 3 → ℕ),
      ¬ (content (rsk _ _ A).2.1.1 = compContent (![2, 2] : Fin 2 → ℕ) ∧
        content (rsk _ _ A).2.2.1 = compContent (![2, 1, 1] : Fin 3 → ℕ)) :=
  ⟨⟨⟨ex45a, by decide⟩⟩, printed_codomain_obstruction _ _ ex45_contents_ne⟩

/-- The printed codomain is equinumerous with the matrices (via swapping `P` and `Q` after RSK);
the printed failure is of the map, not of cardinality.  This swap is NOT the printed map. -/
noncomputable def swapEquiv (μ : Fin m → ℕ) (ρ : Fin n → ℕ) : Target μ ρ ≃ PrintedTarget μ ρ where
  toFun t := ⟨t.1, (t.2.2, t.2.1)⟩
  invFun t := ⟨t.1, (t.2.2, t.2.1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## (4.4) exactly as printed, unsigned Kostka numbers -/

/-- Unsigned Kostka number `K⁰_{λ c}`: semistandard tableaux of shape λ and content `c`. -/
noncomputable def kostka0 (la : YoungDiagram) {k : ℕ} (c : Fin k → ℕ) : ℕ :=
  (tableauxOfContent la (compContent c)).card

attribute [local instance] degreeFintype

noncomputable def targetDegreeEquiv (μ : Fin m → ℕ) (ρ : Fin n → ℕ) :
    Target μ ρ ≃ Σ la : DegreeShape (∑ i, μ i),
      {P : PositiveTableau la.val // content P = compContent ρ} ×
      {Q : PositiveTableau la.val // content Q = compContent μ} where
  toFun t := ⟨⟨t.1, by
    have h := content_total t.2.2.1
    rw [t.2.2.2, compContent_total] at h
    exact h.symm⟩, t.2⟩
  invFun s := ⟨s.1.val, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_fiber (la : YoungDiagram) (c : ℕ →₀ ℕ) :
    Nat.card {T : PositiveTableau la // content T = c} = (tableauxOfContent la c).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun T => (mem_tableauxOfContent T c).symm))

instance fiberFinite' (la : YoungDiagram) (c : ℕ →₀ ℕ) :
    Finite {T : PositiveTableau la // content T = c} :=
  (finite_content la c).to_subtype

/-- **EK (4.4), as printed:** `N_{µρ} = ∑_{λ ⊢ |µ|} K⁰_{λµ} K⁰_{λρ}` (unsigned Kostka numbers;
λ ranges over all Young diagrams with `|µ|` cells). -/
theorem ek_eq_4_4 (μ : Fin m → ℕ) (ρ : Fin n → ℕ) :
    Nat.card (Mat μ ρ) = ∑ la : DegreeShape (∑ i, μ i), kostka0 la.val μ * kostka0 la.val ρ := by
  rw [Nat.card_congr ((rskEquiv μ ρ).trans (targetDegreeEquiv μ ρ)), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro la _
  rw [Nat.card_prod, card_fiber, card_fiber, kostka0, kostka0, mul_comm]

end OddMath.Frontier.EKRskBijection
