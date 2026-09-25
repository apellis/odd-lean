import OddMath.Frontier.TableauOfRows
import OddMath.Frontier.TableauDominance
import OddMath.Frontier.EKDualBases
import OddMath.Frontier.EKRadicalQuotient
import Mathlib.Data.List.GetD

/-! # EK1107.5610v2 Appendix: Data, Secs. 5.1-5.2 (pp.36-39), degrees <= 5

Every printed entry of

* Sec. 5.1 odd Kostka tables, degrees 1-5 (rows = shape, columns = content,
  partitions in the printed lexicographic order), is proved equal to the existing
  `TableauDominance.signedKostka`;
* Sec. 5.2 q = -1 quotient tables, degrees 1-5 (h-basis, printed order), is proved
  equal to the existing Gram matrix `EKDualBases.Mh` (= `quotientPairing` of
  `hPartition`s);
* Sec. 5.2 unspecialized-q tables, degrees 1-4 (compositions, printed order): the
  printed polynomial evaluated at q = -1 is proved equal to the existing
  `EKRadicalQuotient.quotientPairing` of the printed composition words
  (`EKMixedPairing.mixed`, all colours h). Only q = -1 is existing; the general-q
  identity itself is NOT claimed here (no existing general-q object).

Method (no `native_decide`): two generic certified evaluators proved once from the
existing definitions,
* `fiber_sum` : the literal fixed-content fiber sign sum defining `signedKostka`
  equals `kEval`, an explicit finite enumeration of row lists (bijection via
  `TableauOfRows.tableau` / `TableauRowRecursion.rows`);
* `mat_sum` / `pairing_eval` : the margin-matrix sum of `proposition_3_1_Mh`
  equals `mhEval`, an explicit enumeration of row-composition matrices;
then each finite value is closed by kernel reduction (`decide +kernel`).
Degree 6 and the minimal polynomials are non-goals. Sign conventions untouched.
-/
set_option maxRecDepth 100000

namespace OddMath.Frontier.EKAppendixData
open TableauSign TableauContent TableauRowWord TableauEvaluation TableauRowRecursion
open TableauOfRows TableauBumpBoundary TableauRowStep
open scoped BigOperators

/-! ## Certified evaluator I: signed Kostka fibers -/

/-- Weakly increasing words of length `k` over `Fin n`, all letters `≥ lo`. -/
def incWords (n : ℕ) : ℕ → ℕ → List (List (Fin n))
  | 0, _ => [[]]
  | k+1, lo => (List.finRange n).flatMap
      (fun a => if lo ≤ a.val then (incWords n k a.val).map (a :: ·) else [])

theorem mem_incWords (n : ℕ) : ∀ (w : List (Fin n)) (lo : ℕ), w.Sorted (· ≤ ·) →
    (∀ a ∈ w, lo ≤ a.val) → w ∈ incWords n w.length lo
  | [], _, _, _ => by simp [incWords]
  | a :: w, lo, hs, hlo => by
    have hs' := List.sorted_cons.mp hs
    have ih := mem_incWords n w a.val hs'.2 (fun b hb => hs'.1 b hb)
    simp only [List.length_cons, incWords, List.mem_flatMap, List.mem_finRange, true_and]
    exact ⟨a, by rw [if_pos (hlo a (by simp))]; exact List.mem_map.mpr ⟨w, ih, rfl⟩⟩

/-- All row lists with prescribed row lengths and weakly increasing rows. -/
def rowCands (n : ℕ) (r : ℕ) : List ℕ → List (List (List (Fin n)))
  | [] => [[]]
  | l :: ls => (incWords n l r).flatMap (fun w => (rowCands n (r+1) ls).map (w :: ·))

/-- Decidable validity of a row list: shape `wl`, content `cl` (label i+1 used cl[i] times). -/
def Valid (n : ℕ) (wl cl : List ℕ) (rs : List (List (Fin n))) : Prop :=
  (∀ w ∈ rs, w.Sorted (· ≤ ·)) ∧
  (∀ r < rs.length, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) ∧
  rs.map List.length = wl ∧ (∀ w ∈ rs, w ≠ []) ∧
  ∀ i : Fin n, (readRows rs).count i = cl.getD i.val 0

instance decColumnBelow (n : ℕ) (u l : List (Fin n)) : Decidable (ColumnBelow u l) := by
  unfold ColumnBelow; infer_instance

instance decValid (n : ℕ) (wl cl : List ℕ) : DecidablePred (Valid n wl cl) := by
  intro rs; unfold Valid; infer_instance

/-- The computable signed count: an explicit finite set with its row-reading sign. -/
def kEval (n : ℕ) (wl cl : List ℕ) : ℤ :=
  ∑ rs ∈ ((rowCands n 0 wl).filter (fun rs => decide (Valid n wl cl rs))).toFinset,
    (-1 : ℤ) ^ inversions ((readRows rs).map Fin.val)


theorem mem_rowCands (n : ℕ) : ∀ (rs : List (List (Fin n))) (r : ℕ),
    (∀ w ∈ rs, w.Sorted (· ≤ ·)) →
    (∀ k (hk : k < rs.length), ∀ a ∈ rs[k], r + k ≤ a.val) →
    rs ∈ rowCands n r (rs.map List.length)
  | [], _, _, _ => by simp [rowCands]
  | w :: rs, r, hs, hb => by
    simp only [List.map_cons, rowCands, List.mem_flatMap, List.mem_map]
    refine ⟨w, ?_, rs, mem_rowCands n rs (r+1) (fun v hv => hs v (by simp [hv])) ?_, rfl⟩
    · exact mem_incWords n w r (hs w (by simp)) (fun a ha => by
        simpa using hb 0 (by simp) a (by simpa using ha))
    · intro k hk a ha
      have := hb (k+1) (by simp; omega) a (by simpa using ha)
      omega

theorem columnBelow_nil {n : ℕ} (u : List (Fin n)) : ColumnBelow u [] :=
  ⟨Nat.zero_le _, fun _ hc => absurd hc (Nat.not_lt_zero _)⟩

theorem columns_all {n : ℕ} (rs : List (List (Fin n)))
    (h : ∀ r < rs.length, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD [])) :
    ∀ r : ℕ, ColumnBelow (rs[r]?.getD []) (rs[r+1]?.getD []) := by
  intro r
  by_cases hr : r < rs.length
  · exact h r hr
  · have : rs[r+1]? = none := List.getElem?_eq_none (by omega)
    rw [this]
    exact columnBelow_nil _

/-- The entries of a tableau are read back from its extracted rows. -/
theorem entry_of_rows (n : ℕ) {μ : YoungDiagram} (T : PositiveTableau μ) (hT : InAlphabet n T)
    (r c : ℕ) : T.entry r c =
      ((((rows n T hT)[r]?.getD [])[c]?).map (fun x : Fin n => x.val + 1)).getD 0 := by
  obtain ⟨hs, hc, _, _, he⟩ := genuine_roundtrip n μ T hT
  rw [← he r c, tableau_entry]

theorem rows_injective (n : ℕ) {μ : YoungDiagram} (S T : PositiveTableau μ)
    (hS : InAlphabet n S) (hT : InAlphabet n T) (h : rows n S hS = rows n T hT) : S = T := by
  apply ext_cells
  intro p _
  rw [entry_of_rows n S hS, entry_of_rows n T hT, h]

theorem row_entry_ge (n : ℕ) {μ : YoungDiagram} (T : PositiveTableau μ) (hT : InAlphabet n T)
    (k : ℕ) (hk : k < (rows n T hT).length) : ∀ a ∈ (rows n T hT)[k], k ≤ a.val := by
  intro a ha
  have hk' : k < μ.colLen 0 := by rwa [rows_length] at hk
  rw [rows_get n μ T hT k hk'] at ha
  have hl := row_labels n μ T hT k
  have hm : a.val + 1 ∈ (row n T hT k).map (fun i => i.val + 1) := List.mem_map.mpr ⟨a, ha, rfl⟩
  rw [hl] at hm
  obtain ⟨c, hc, hce⟩ := List.mem_map.mp hm
  have hcell : (k, c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (List.mem_range.mp hc)
  have := TableauDominance.entry_ge_row T hcell
  omega

theorem count_rows (n : ℕ) {μ : YoungDiagram} (T : PositiveTableau μ) (hT : InAlphabet n T)
    (i : Fin n) : (readRows (rows n T hT)).count i = content T (i.val + 1) := by
  rw [readRows_rows, rowFinWord_count]
  rfl

theorem content_above (n : ℕ) {μ : YoungDiagram} (T : PositiveTableau μ) (hT : InAlphabet n T)
    (k : ℕ) (hk : n < k) : content T k = 0 := by
  rw [content_apply]
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro p hp he
  have := hT p hp
  omega

theorem sign_rows (n : ℕ) {μ : YoungDiagram} (T : PositiveTableau μ) (hT : InAlphabet n T) :
    TableauDominance.tableauSign T = (-1 : ℤ) ^ inversions ((readRows (rows n T hT)).map Fin.val) := by
  rw [readRows_rows, rowFinWord_inversions]
  rfl

theorem shape_eq_of_rowLens {μ ν : YoungDiagram} (h : μ.rowLens = ν.rowLens) : μ = ν := by
  apply YoungDiagram.equivListRowLens.injective
  exact Subtype.ext h

/-- Certified evaluator: the literal fixed-content fiber sign sum equals `kEval`. -/
theorem fiber_sum (lam : YoungDiagram) (c : ℕ →₀ ℕ) (n : ℕ) (cl : List ℕ)
    (hc0 : c 0 = 0) (hcl : ∀ i, c (i+1) = cl.getD i 0) (hlen : cl.length ≤ n) :
    ∑ T ∈ tableauxOfContent lam c, TableauDominance.tableauSign T = kEval n lam.rowLens cl := by
  classical
  have hsupp : ∀ k ∈ c.support, k ≤ n := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk
    by_contra hkn
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    exact hk (by rw [hcl]; exact List.getD_eq_default _ _ (by omega))
  unfold kEval
  apply Finset.sum_bij (fun T hT => rows n T (inAlphabet_of_mem n c hsupp T hT))
  · intro T hT
    have hT' := inAlphabet_of_mem n c hsupp T hT
    obtain ⟨hs, hc, hn, _, _⟩ := genuine_roundtrip n lam T hT'
    rw [List.mem_toFinset, List.mem_filter, decide_eq_true_iff]
    have hlens := rows_lengths n lam T hT'
    refine ⟨?_, hs, fun r _ => hc r, hlens, hn, ?_⟩
    · have := mem_rowCands n (rows n T hT') 0 hs (fun k hk a ha => by
        simpa using row_entry_ge n T hT' k hk a ha)
      rwa [hlens] at this
    · intro i
      rw [count_rows, (mem_tableauxOfContent T c).mp hT, hcl]
  · intro S hS T hT h
    exact rows_injective n S T _ _ h
  · intro rs hrs
    rw [List.mem_toFinset, List.mem_filter, decide_eq_true_iff] at hrs
    obtain ⟨_, hs, hc', hlens, hn, hcount⟩ := hrs
    have hc := columns_all rs hc'
    have hshape : shape n rs hc = lam := shape_eq_of_rowLens (by rw [shape_rowLens n rs hc hn, hlens])
    subst hshape
    refine ⟨tableau n rs hs hc, ?_, rows_tableau n rs hs hc hn⟩
    rw [mem_tableauxOfContent]
    ext k
    rcases k with _ | i
    · rw [content_zero, hc0]
    · by_cases hi : i < n
      · have := count_rows n (tableau n rs hs hc) (bounded n rs hs hc) ⟨i, hi⟩
        rw [rows_tableau n rs hs hc hn, hcount] at this
        rw [← this, hcl]
      · rw [content_above n _ (bounded n rs hs hc) (i+1) (by omega), hcl,
          List.getD_eq_default _ _ (by omega)]
  · intro T hT
    exact sign_rows n T _


theorem rowLen_eq_getD (μ : YoungDiagram) (i : ℕ) : μ.rowLen i = μ.rowLens.getD i 0 := by
  by_cases h : i < μ.colLen 0
  · rw [List.getD_eq_getElem _ _ (by simpa [YoungDiagram.length_rowLens] using h)]
    simp [YoungDiagram.get_rowLens]
  · rw [List.getD_eq_default _ _ (by simp [YoungDiagram.length_rowLens]; omega)]
    by_contra hne
    have hm : (i, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    exact h (YoungDiagram.mem_iff_lt_colLen.mp hm)

theorem shapeContent_apply (μ : YoungDiagram) (k : ℕ) :
    TableauDominance.shapeContent μ k = (μ.cells.filter (fun p => p.1 + 1 = k)).card := by
  classical
  rw [← TableauDominance.content_canonical, content_apply]
  congr 1
  apply Finset.filter_congr
  intro p hp
  rw [TableauDominance.canonical_entry hp]

theorem shapeContent_zero (μ : YoungDiagram) : TableauDominance.shapeContent μ 0 = 0 := by
  rw [shapeContent_apply]; simp

theorem shapeContent_succ (μ : YoungDiagram) (i : ℕ) :
    TableauDominance.shapeContent μ (i+1) = μ.rowLens.getD i 0 := by
  rw [shapeContent_apply, ← rowLen_eq_getD, YoungDiagram.rowLen_eq_card]
  unfold YoungDiagram.row
  congr 1
  apply Finset.filter_congr
  intro p _
  omega

theorem fiberSum_shape (lam mu : YoungDiagram) (n : ℕ) (h : mu.rowLens.length ≤ n) :
    ∑ T ∈ tableauxOfContent lam (TableauDominance.shapeContent mu), TableauDominance.tableauSign T
      = kEval n lam.rowLens mu.rowLens :=
  fiber_sum lam _ n mu.rowLens (shapeContent_zero mu) (shapeContent_succ mu) h

/-- `signedKostka` = (sign of the canonical tableau) * (fiber sign sum), both evaluated. -/
theorem signedKostka_eval (lam mu : YoungDiagram) :
    TableauDominance.signedKostka lam mu =
      kEval lam.rowLens.length lam.rowLens lam.rowLens *
        kEval mu.rowLens.length lam.rowLens mu.rowLens := by
  classical
  have hc : TableauDominance.tableauSign (TableauDominance.canonicalTableau lam) =
      kEval lam.rowLens.length lam.rowLens lam.rowLens := by
    rw [← fiberSum_shape lam lam _ le_rfl, TableauDominance.diagonal_fiber, Finset.sum_singleton]
  rw [TableauDominance.signedKostka, hc, fiberSum_shape lam mu _ le_rfl]

theorem signedKostka_ofRowLens (w v : List ℕ) (hw : w.Sorted (· ≥ ·)) (hv : v.Sorted (· ≥ ·))
    (hwp : ∀ x ∈ w, 0 < x) (hvp : ∀ x ∈ v, 0 < x) :
    TableauDominance.signedKostka (YoungDiagram.ofRowLens w hw) (YoungDiagram.ofRowLens v hv) =
      kEval w.length w w * kEval v.length w v := by
  rw [signedKostka_eval, YoungDiagram.rowLens_ofRowLens_eq_self hwp,
    YoungDiagram.rowLens_ofRowLens_eq_self hvp]

/-! ## Certified evaluator II: margin-matrix Gram sums -/
open EKPairingMatrices

/-- All length-`c` lists of naturals with sum `s`. -/
def comps : ℕ → ℕ → List (List ℕ)
  | s, 0 => if s = 0 then [[]] else []
  | s, c+1 => (List.range (s+1)).flatMap (fun a => (comps (s-a) c).map (a :: ·))

theorem mem_comps : ∀ (c s : ℕ) (l : List ℕ), l ∈ comps s c ↔ l.length = c ∧ l.sum = s
  | 0, s, l => by
    cases l with
    | nil => by_cases h : s = 0 <;> simp [comps, h, eq_comm]
    | cons a l => by_cases h : s = 0 <;> simp [comps, h]
  | c+1, s, l => by
    cases l with
    | nil => simp [comps]
    | cons a l =>
      simp only [comps, List.mem_flatMap, List.mem_range, List.mem_map, List.cons.injEq,
        List.length_cons, List.sum_cons, mem_comps c]
      constructor
      · rintro ⟨b, hb, l', ⟨hl1, hl2⟩, rfl, rfl⟩; omega
      · rintro ⟨h1, h2⟩; exact ⟨a, by omega, l, ⟨by omega, by omega⟩, rfl, rfl⟩

/-- Row-by-row candidates: row i is a composition of `bl[i]` into `c` parts. -/
def matCands (c : ℕ) : List ℕ → List (List (List ℕ))
  | [] => [[]]
  | b :: bl => (comps b c).flatMap (fun w => (matCands c bl).map (w :: ·))

theorem mem_matCands (c : ℕ) : ∀ (bl : List ℕ) (L : List (List ℕ)),
    L ∈ matCands c bl ↔ List.Forall₂ (fun w b => w ∈ comps b c) L bl
  | [], L => by cases L <;> simp [matCands]
  | b :: bl, L => by
    cases L with
    | nil => simp [matCands]
    | cons w L =>
      simp only [matCands, List.mem_flatMap, List.mem_map, List.cons.injEq, List.forall₂_cons,
        mem_matCands c bl]
      constructor
      · rintro ⟨w', hw', L', hL', rfl, rfl⟩; exact ⟨hw', hL'⟩
      · rintro ⟨hw, hL⟩; exact ⟨w, hw, L, hL, rfl, rfl⟩

def ent (L : List (List ℕ)) (i j : ℕ) : ℕ := (L.getD i []).getD j 0

def colSumsL (L : List (List ℕ)) (c : ℕ) : List ℕ :=
  (List.range c).map (fun j => ((List.range L.length).map (fun i => ent L i j)).sum)

def matSet (bl al : List ℕ) : Finset (List (List ℕ)) :=
  ((matCands al.length bl).filter (fun L => decide (colSumsL L al.length = al))).toFinset

def toL {r c : ℕ} (A : Raw r c) : List (List ℕ) := List.ofFn (fun i => List.ofFn (A i))

theorem ent_toL {r c : ℕ} (A : Raw r c) (i : Fin r) (j : Fin c) : ent (toL A) i j = A i j := by
  simp [ent, toL, List.getD_eq_getElem?_getD]

theorem toL_injective {r c : ℕ} : Function.Injective (toL (r := r) (c := c)) := by
  intro A B h
  funext i j
  rw [← ent_toL A, ← ent_toL B, h]

theorem list_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem forall₂_ofFn {α β : Type*} {R : α → β → Prop} {r : ℕ} (f : Fin r → α) (g : Fin r → β)
    (h : ∀ i, R (f i) (g i)) : List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih _ _ (fun i => h i.succ))

/-- Generic certified evaluator for sums over margin matrices. -/
theorem mat_sum {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) (F : List (List ℕ) → ℤ) :
    ∑ A : Mat β α, F (toL A.val) = ∑ L ∈ matSet (List.ofFn β) (List.ofFn α), F L := by
  classical
  apply Finset.sum_bij (fun A _ => toL A.val)
  · intro A _
    simp only [matSet, List.mem_toFinset, List.mem_filter, decide_eq_true_iff, List.length_ofFn]
    refine ⟨(mem_matCands c _ _).mpr (forall₂_ofFn _ _ (fun i => (mem_comps c _ _).mpr ⟨by simp, ?_⟩)), ?_⟩
    · rw [List.sum_ofFn]; exact congrFun A.property.1 i
    · apply List.ext_getElem
      · simp [colSumsL]
      · intro j h1 h2
        simp only [colSumsL, List.getElem_map, List.getElem_range, List.getElem_ofFn]
        rw [list_sum_range, show (toL A.val).length = r by simp [toL], ← Fin.sum_univ_eq_sum_range
          (fun i => ent (toL A.val) i j) r]
        have hj : j < c := by simpa [colSumsL] using h1
        simp only [ent_toL A.val _ ⟨j, hj⟩]
        exact congrFun A.property.2 ⟨j, hj⟩
  · intro A _ B _ h
    exact Subtype.ext (toL_injective h)
  · intro L hL
    simp only [matSet, List.mem_toFinset, List.mem_filter, decide_eq_true_iff, List.length_ofFn,
      mem_matCands] at hL
    obtain ⟨hF, hcol⟩ := hL
    have hlen : L.length = r := by simpa using hF.length_eq
    have hrow : ∀ (i : ℕ) (hi : i < L.length), L[i].length = c ∧ L[i].sum = β ⟨i, by omega⟩ := by
      intro i hi
      have := (List.forall₂_iff_get.mp hF).2 i hi (by simp; omega)
      simpa using (mem_comps c _ _).mp this
    let A : Raw r c := fun i j => ent L i j
    have hA : toL A = L := by
      apply List.ext_getElem
      · simp [toL, hlen]
      · intro i h1 h2
        simp only [toL, List.getElem_ofFn]
        apply List.ext_getElem
        · simp [(hrow i h2).1]
        · intro j h3 h4
          simp [A, ent, List.getD_eq_getElem?_getD, h2, h4]
    refine ⟨⟨A, ?_, ?_⟩, Finset.mem_univ _, hA⟩
    · funext i
      have hi : i.val < L.length := by omega
      rw [← (hrow i hi).2]
      show ∑ j, A i j = _
      rw [← List.sum_ofFn]
      congr 1
      apply List.ext_getElem
      · simp [(hrow i hi).1]
      · intro j h1 h2
        simp [A, ent, List.getD_eq_getElem?_getD, hi, h2]
    · funext j
      have h := congrArg (fun l => l[j.val]?) hcol
      simp only [colSumsL, List.getElem?_map, List.getElem?_range j.isLt, List.getElem?_ofFn,
        Option.map_some'] at h
      have h' : ((List.range L.length).map (fun i => ent L i j)).sum = α j := by
        simpa using h
      rw [list_sum_range, hlen, ← Fin.sum_univ_eq_sum_range (fun i => ent L i j) r] at h'
      exact h'
  · intro A _; rfl


def crossL (L : List (List ℕ)) (r c : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, ∑ k ∈ Finset.range r, if i < k then
    ∑ j ∈ Finset.range c, ∑ l ∈ Finset.range c, if l < j then ent L i j * ent L k l else 0 else 0

theorem crossing_toL {r c : ℕ} (A : Raw r c) : crossing A = crossL (toL A) r c := by
  simp only [crossing, crossL, Finset.sum_range, ent_toL, Fin.val_fin_lt]

def mhEval (bl al : List ℕ) : ℤ :=
  ∑ L ∈ matSet bl al, (-1 : ℤ) ^ crossL L bl.length al.length

theorem pairing_eval {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    ∑ A : Mat β α, (-1 : ℤ) ^ crossing A.val = mhEval (List.ofFn β) (List.ofFn α) := by
  have h := mat_sum β α (fun L => (-1 : ℤ) ^ crossL L r c)
  simp only [← crossing_toL] at h
  rw [h, mhEval, List.length_ofFn, List.length_ofFn]

open EKDualBases DegreeShapes in
theorem Mh_eval (d : ℕ) (ν μ : DegreeShape d) : Mh d ν μ = mhEval ν.val.rowLens μ.val.rowLens := by
  rw [proposition_3_1_Mh, EKSemiorthogonality.rowLens_eq_ofFn, EKSemiorthogonality.rowLens_eq_ofFn]
  exact pairing_eval _ _


open EKDualBases DegreeShapes in
theorem Mh_ofRowLens (d : ℕ) (w v : List ℕ) (hw : w.Sorted (· ≥ ·)) (hv : v.Sorted (· ≥ ·))
    (hwp : ∀ x ∈ w, 0 < x) (hvp : ∀ x ∈ v, 0 < x)
    (hwd : (YoungDiagram.ofRowLens w hw).card = d) (hvd : (YoungDiagram.ofRowLens v hv).card = d) :
    Mh d ⟨YoungDiagram.ofRowLens w hw, hwd⟩ ⟨YoungDiagram.ofRowLens v hv, hvd⟩ = mhEval w v := by
  rw [Mh_eval]
  show mhEval (YoungDiagram.ofRowLens w hw).rowLens (YoungDiagram.ofRowLens v hv).rowLens = _
  rw [YoungDiagram.rowLens_ofRowLens_eq_self hwp, YoungDiagram.rowLens_ofRowLens_eq_self hvp]

/-- Composition words (all colours h): the existing quotient pairing is the
(unrestricted) margin-matrix sum, evaluated by `mhEval`. -/
theorem compPairing_eval {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    EKRadicalQuotient.quotientPairing (EKMixedPairing.mixed β (fun _ => false))
      (EKMixedPairing.mixed α (fun _ => false)) = mhEval (List.ofFn β) (List.ofFn α) := by
  rw [EKMixedPairing.quotientPairing_eq_matrixSum, ← pairing_eval]
  unfold EKMixedPairing.matrixSum EKMixedPairing.matrixWeight
  congr 1; funext A
  simp [EKMixedPairing.cell]

theorem card_yd (w : List ℕ) (hw : w.Sorted (· ≥ ·)) (d : ℕ) (h : w.sum = d) :
    (YoungDiagram.ofRowLens w hw).card = d := by
  rw [EKPartitionSpanning.card_ofRowLens, h]

/-! ## Printed data, Sec. 5.1: odd Kostka numbers (rows = shape, columns = content) -/

/-- Printed degree-1 shapes, printed order (1). -/
def shapes1 : Fin 1 → YoungDiagram := ![YoungDiagram.ofRowLens [1] (by decide)]
/-- Printed Sec. 5.1 degree-1 odd Kostka table, verbatim. -/
def printedKostka1 : Matrix (Fin 1) (Fin 1) ℤ := !![1]
theorem kostka1_1_1 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1] (by decide)) (YoungDiagram.ofRowLens [1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
/-- Sec. 5.1 degree 1: every printed entry equals the existing `signedKostka`. -/
theorem kostka_table1 : ∀ i j, TableauDominance.signedKostka (shapes1 i) (shapes1 j) = printedKostka1 i j := by
  intro i j; fin_cases i; fin_cases j
  exacts [kostka1_1_1]

/-- Printed degree-2 shapes, printed order (11), (2). -/
def shapes2 : Fin 2 → YoungDiagram := ![YoungDiagram.ofRowLens [1,1] (by decide), YoungDiagram.ofRowLens [2] (by decide)]
/-- Printed Sec. 5.1 degree-2 odd Kostka table, verbatim. -/
def printedKostka2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0;
    1, 1]
theorem kostka2_11_11 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1] (by decide)) (YoungDiagram.ofRowLens [1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka2_11_2 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1] (by decide)) (YoungDiagram.ofRowLens [2] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka2_2_11 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2] (by decide)) (YoungDiagram.ofRowLens [1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka2_2_2 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2] (by decide)) (YoungDiagram.ofRowLens [2] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
/-- Sec. 5.1 degree 2: every printed entry equals the existing `signedKostka`. -/
theorem kostka_table2 : ∀ i j, TableauDominance.signedKostka (shapes2 i) (shapes2 j) = printedKostka2 i j := by
  intro i j; fin_cases i <;> fin_cases j
  exacts [kostka2_11_11, kostka2_11_2, kostka2_2_11, kostka2_2_2]

/-- Printed degree-3 shapes, printed order (111), (21), (3). -/
def shapes3 : Fin 3 → YoungDiagram := ![YoungDiagram.ofRowLens [1,1,1] (by decide), YoungDiagram.ofRowLens [2,1] (by decide), YoungDiagram.ofRowLens [3] (by decide)]
/-- Printed Sec. 5.1 degree-3 odd Kostka table, verbatim. -/
def printedKostka3 : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0;
    0, 1, 0;
    1, 1, 1]
theorem kostka3_111_111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1] (by decide)) (YoungDiagram.ofRowLens [1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka3_111_21 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1] (by decide)) (YoungDiagram.ofRowLens [2,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka3_111_3 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1] (by decide)) (YoungDiagram.ofRowLens [3] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka3_21_111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1] (by decide)) (YoungDiagram.ofRowLens [1,1,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka3_21_21 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1] (by decide)) (YoungDiagram.ofRowLens [2,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka3_21_3 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1] (by decide)) (YoungDiagram.ofRowLens [3] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka3_3_111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3] (by decide)) (YoungDiagram.ofRowLens [1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka3_3_21 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3] (by decide)) (YoungDiagram.ofRowLens [2,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka3_3_3 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3] (by decide)) (YoungDiagram.ofRowLens [3] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
/-- Sec. 5.1 degree 3: every printed entry equals the existing `signedKostka`. -/
theorem kostka_table3 : ∀ i j, TableauDominance.signedKostka (shapes3 i) (shapes3 j) = printedKostka3 i j := by
  intro i j; fin_cases i <;> fin_cases j
  exacts [kostka3_111_111, kostka3_111_21, kostka3_111_3, kostka3_21_111, kostka3_21_21, kostka3_21_3, kostka3_3_111, kostka3_3_21, kostka3_3_3]

/-- Printed degree-4 shapes, printed order (1111), (211), (22), (31), (4). -/
def shapes4 : Fin 5 → YoungDiagram := ![YoungDiagram.ofRowLens [1,1,1,1] (by decide), YoungDiagram.ofRowLens [2,1,1] (by decide), YoungDiagram.ofRowLens [2,2] (by decide), YoungDiagram.ofRowLens [3,1] (by decide), YoungDiagram.ofRowLens [4] (by decide)]
/-- Printed Sec. 5.1 degree-4 odd Kostka table, verbatim. -/
def printedKostka4 : Matrix (Fin 5) (Fin 5) ℤ := !![1, 0, 0, 0, 0;
    1, 1, 0, 0, 0;
    0, 1, 1, 0, 0;
    1, 0, (-1), 1, 0;
    1, 1, 1, 1, 1]
theorem kostka4_1111_1111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1,1] (by decide)) (YoungDiagram.ofRowLens [1,1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_1111_211 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1,1] (by decide)) (YoungDiagram.ofRowLens [2,1,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_1111_22 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1,1] (by decide)) (YoungDiagram.ofRowLens [2,2] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_1111_31 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1,1] (by decide)) (YoungDiagram.ofRowLens [3,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_1111_4 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1,1] (by decide)) (YoungDiagram.ofRowLens [4] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_211_1111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1,1] (by decide)) (YoungDiagram.ofRowLens [1,1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_211_211 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1,1] (by decide)) (YoungDiagram.ofRowLens [2,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_211_22 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1,1] (by decide)) (YoungDiagram.ofRowLens [2,2] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_211_31 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1,1] (by decide)) (YoungDiagram.ofRowLens [3,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_211_4 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1,1] (by decide)) (YoungDiagram.ofRowLens [4] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_22_1111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,2] (by decide)) (YoungDiagram.ofRowLens [1,1,1,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_22_211 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,2] (by decide)) (YoungDiagram.ofRowLens [2,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_22_22 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,2] (by decide)) (YoungDiagram.ofRowLens [2,2] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_22_31 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,2] (by decide)) (YoungDiagram.ofRowLens [3,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_22_4 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,2] (by decide)) (YoungDiagram.ofRowLens [4] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_31_1111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,1] (by decide)) (YoungDiagram.ofRowLens [1,1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_31_211 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,1] (by decide)) (YoungDiagram.ofRowLens [2,1,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_31_22 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,1] (by decide)) (YoungDiagram.ofRowLens [2,2] (by decide)) = (-1) := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_31_31 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,1] (by decide)) (YoungDiagram.ofRowLens [3,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_31_4 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,1] (by decide)) (YoungDiagram.ofRowLens [4] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_4_1111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [4] (by decide)) (YoungDiagram.ofRowLens [1,1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_4_211 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [4] (by decide)) (YoungDiagram.ofRowLens [2,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_4_22 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [4] (by decide)) (YoungDiagram.ofRowLens [2,2] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_4_31 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [4] (by decide)) (YoungDiagram.ofRowLens [3,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka4_4_4 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [4] (by decide)) (YoungDiagram.ofRowLens [4] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
/-- Sec. 5.1 degree 4: every printed entry equals the existing `signedKostka`. -/
theorem kostka_table4 : ∀ i j, TableauDominance.signedKostka (shapes4 i) (shapes4 j) = printedKostka4 i j := by
  intro i j; fin_cases i <;> fin_cases j
  exacts [kostka4_1111_1111, kostka4_1111_211, kostka4_1111_22, kostka4_1111_31, kostka4_1111_4, kostka4_211_1111, kostka4_211_211, kostka4_211_22, kostka4_211_31, kostka4_211_4, kostka4_22_1111, kostka4_22_211, kostka4_22_22, kostka4_22_31, kostka4_22_4, kostka4_31_1111, kostka4_31_211, kostka4_31_22, kostka4_31_31, kostka4_31_4, kostka4_4_1111, kostka4_4_211, kostka4_4_22, kostka4_4_31, kostka4_4_4]

/-- Printed degree-5 shapes, printed order (11111), (2111), (221), (311), (32), (41), (5). -/
def shapes5 : Fin 7 → YoungDiagram := ![YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), YoungDiagram.ofRowLens [2,1,1,1] (by decide), YoungDiagram.ofRowLens [2,2,1] (by decide), YoungDiagram.ofRowLens [3,1,1] (by decide), YoungDiagram.ofRowLens [3,2] (by decide), YoungDiagram.ofRowLens [4,1] (by decide), YoungDiagram.ofRowLens [5] (by decide)]
/-- Printed Sec. 5.1 degree-5 odd Kostka table, verbatim. -/
def printedKostka5 : Matrix (Fin 7) (Fin 7) ℤ := !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    (-1), 0, 1, 0, 0, 0, 0;
    2, 1, (-1), 1, 0, 0, 0;
    1, 1, 0, 1, 1, 0, 0;
    0, 1, 2, 0, (-1), 1, 0;
    1, 1, 1, 1, 1, 1, 1]
theorem kostka5_11111_11111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_11111_2111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_11111_221 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) (YoungDiagram.ofRowLens [2,2,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_11111_311 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) (YoungDiagram.ofRowLens [3,1,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_11111_32 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) (YoungDiagram.ofRowLens [3,2] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_11111_41 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) (YoungDiagram.ofRowLens [4,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_11111_5 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) (YoungDiagram.ofRowLens [5] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_2111_11111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_2111_2111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_2111_221 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) (YoungDiagram.ofRowLens [2,2,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_2111_311 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) (YoungDiagram.ofRowLens [3,1,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_2111_32 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) (YoungDiagram.ofRowLens [3,2] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_2111_41 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) (YoungDiagram.ofRowLens [4,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_2111_5 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) (YoungDiagram.ofRowLens [5] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_221_11111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,2,1] (by decide)) (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) = (-1) := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_221_2111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,2,1] (by decide)) (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_221_221 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,2,1] (by decide)) (YoungDiagram.ofRowLens [2,2,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_221_311 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,2,1] (by decide)) (YoungDiagram.ofRowLens [3,1,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_221_32 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,2,1] (by decide)) (YoungDiagram.ofRowLens [3,2] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_221_41 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,2,1] (by decide)) (YoungDiagram.ofRowLens [4,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_221_5 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [2,2,1] (by decide)) (YoungDiagram.ofRowLens [5] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_311_11111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,1,1] (by decide)) (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) = 2 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_311_2111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,1,1] (by decide)) (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_311_221 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,1,1] (by decide)) (YoungDiagram.ofRowLens [2,2,1] (by decide)) = (-1) := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_311_311 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,1,1] (by decide)) (YoungDiagram.ofRowLens [3,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_311_32 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,1,1] (by decide)) (YoungDiagram.ofRowLens [3,2] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_311_41 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,1,1] (by decide)) (YoungDiagram.ofRowLens [4,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_311_5 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,1,1] (by decide)) (YoungDiagram.ofRowLens [5] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_32_11111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,2] (by decide)) (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_32_2111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,2] (by decide)) (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_32_221 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,2] (by decide)) (YoungDiagram.ofRowLens [2,2,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_32_311 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,2] (by decide)) (YoungDiagram.ofRowLens [3,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_32_32 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,2] (by decide)) (YoungDiagram.ofRowLens [3,2] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_32_41 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,2] (by decide)) (YoungDiagram.ofRowLens [4,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_32_5 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [3,2] (by decide)) (YoungDiagram.ofRowLens [5] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_41_11111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [4,1] (by decide)) (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_41_2111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [4,1] (by decide)) (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_41_221 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [4,1] (by decide)) (YoungDiagram.ofRowLens [2,2,1] (by decide)) = 2 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_41_311 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [4,1] (by decide)) (YoungDiagram.ofRowLens [3,1,1] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_41_32 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [4,1] (by decide)) (YoungDiagram.ofRowLens [3,2] (by decide)) = (-1) := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_41_41 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [4,1] (by decide)) (YoungDiagram.ofRowLens [4,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_41_5 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [4,1] (by decide)) (YoungDiagram.ofRowLens [5] (by decide)) = 0 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_5_11111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [5] (by decide)) (YoungDiagram.ofRowLens [1,1,1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_5_2111 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [5] (by decide)) (YoungDiagram.ofRowLens [2,1,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_5_221 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [5] (by decide)) (YoungDiagram.ofRowLens [2,2,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_5_311 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [5] (by decide)) (YoungDiagram.ofRowLens [3,1,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_5_32 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [5] (by decide)) (YoungDiagram.ofRowLens [3,2] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_5_41 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [5] (by decide)) (YoungDiagram.ofRowLens [4,1] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem kostka5_5_5 : TableauDominance.signedKostka (YoungDiagram.ofRowLens [5] (by decide)) (YoungDiagram.ofRowLens [5] (by decide)) = 1 := by
  rw [signedKostka_ofRowLens _ _ _ _ (by decide) (by decide)]; decide +kernel
/-- Sec. 5.1 degree 5: every printed entry equals the existing `signedKostka`. -/
theorem kostka_table5 : ∀ i j, TableauDominance.signedKostka (shapes5 i) (shapes5 j) = printedKostka5 i j := by
  intro i j; fin_cases i <;> fin_cases j
  exacts [kostka5_11111_11111, kostka5_11111_2111, kostka5_11111_221, kostka5_11111_311, kostka5_11111_32, kostka5_11111_41, kostka5_11111_5, kostka5_2111_11111, kostka5_2111_2111, kostka5_2111_221, kostka5_2111_311, kostka5_2111_32, kostka5_2111_41, kostka5_2111_5, kostka5_221_11111, kostka5_221_2111, kostka5_221_221, kostka5_221_311, kostka5_221_32, kostka5_221_41, kostka5_221_5, kostka5_311_11111, kostka5_311_2111, kostka5_311_221, kostka5_311_311, kostka5_311_32, kostka5_311_41, kostka5_311_5, kostka5_32_11111, kostka5_32_2111, kostka5_32_221, kostka5_32_311, kostka5_32_32, kostka5_32_41, kostka5_32_5, kostka5_41_11111, kostka5_41_2111, kostka5_41_221, kostka5_41_311, kostka5_41_32, kostka5_41_41, kostka5_41_5, kostka5_5_11111, kostka5_5_2111, kostka5_5_221, kostka5_5_311, kostka5_5_32, kostka5_5_41, kostka5_5_5]

/-! ## Printed data, Sec. 5.2: q = -1 bilinear form on the quotient (h-basis) -/

/-- Printed degree-1 h-basis, printed order h1. -/
def hshapes1 : Fin 1 → DegreeShapes.DegreeShape 1 := ![(⟨YoungDiagram.ofRowLens [1] (by decide), card_yd _ _ 1 rfl⟩ : DegreeShapes.DegreeShape 1)]
/-- Printed Sec. 5.2 degree-1 q = -1 quotient table, verbatim. -/
def printedGram1 : Matrix (Fin 1) (Fin 1) ℤ := !![1]
theorem gram1_1_1 : EKDualBases.Mh 1 (⟨YoungDiagram.ofRowLens [1] (by decide), card_yd _ _ 1 rfl⟩ : DegreeShapes.DegreeShape 1) (⟨YoungDiagram.ofRowLens [1] (by decide), card_yd _ _ 1 rfl⟩ : DegreeShapes.DegreeShape 1) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
/-- Sec. 5.2 degree 1: the printed q = -1 table is the existing Gram matrix `Mh`. -/
theorem gram_table1 : ∀ i j, EKDualBases.Mh 1 (hshapes1 i) (hshapes1 j) = printedGram1 i j := by
  intro i j; fin_cases i; fin_cases j
  exacts [gram1_1_1]

/-- Printed degree-2 h-basis, printed order h11, h2. -/
def hshapes2 : Fin 2 → DegreeShapes.DegreeShape 2 := ![(⟨YoungDiagram.ofRowLens [1,1] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2), (⟨YoungDiagram.ofRowLens [2] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2)]
/-- Printed Sec. 5.2 degree-2 q = -1 quotient table, verbatim. -/
def printedGram2 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1;
    1, 1]
theorem gram2_11_11 : EKDualBases.Mh 2 (⟨YoungDiagram.ofRowLens [1,1] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) (⟨YoungDiagram.ofRowLens [1,1] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram2_11_2 : EKDualBases.Mh 2 (⟨YoungDiagram.ofRowLens [1,1] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) (⟨YoungDiagram.ofRowLens [2] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram2_2_11 : EKDualBases.Mh 2 (⟨YoungDiagram.ofRowLens [2] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) (⟨YoungDiagram.ofRowLens [1,1] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram2_2_2 : EKDualBases.Mh 2 (⟨YoungDiagram.ofRowLens [2] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) (⟨YoungDiagram.ofRowLens [2] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
/-- Sec. 5.2 degree 2: the printed q = -1 table is the existing Gram matrix `Mh`. -/
theorem gram_table2 : ∀ i j, EKDualBases.Mh 2 (hshapes2 i) (hshapes2 j) = printedGram2 i j := by
  intro i j; fin_cases i <;> fin_cases j
  exacts [gram2_11_11, gram2_11_2, gram2_2_11, gram2_2_2]

/-- Printed degree-3 h-basis, printed order h111, h21, h3. -/
def hshapes3 : Fin 3 → DegreeShapes.DegreeShape 3 := ![(⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3), (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3), (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3)]
/-- Printed Sec. 5.2 degree-3 q = -1 quotient table, verbatim. -/
def printedGram3 : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 1;
    1, 0, 1;
    1, 1, 1]
theorem gram3_111_111 : EKDualBases.Mh 3 (⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram3_111_21 : EKDualBases.Mh 3 (⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram3_111_3 : EKDualBases.Mh 3 (⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram3_21_111 : EKDualBases.Mh 3 (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram3_21_21 : EKDualBases.Mh 3 (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram3_21_3 : EKDualBases.Mh 3 (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram3_3_111 : EKDualBases.Mh 3 (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram3_3_21 : EKDualBases.Mh 3 (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram3_3_3 : EKDualBases.Mh 3 (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
/-- Sec. 5.2 degree 3: the printed q = -1 table is the existing Gram matrix `Mh`. -/
theorem gram_table3 : ∀ i j, EKDualBases.Mh 3 (hshapes3 i) (hshapes3 j) = printedGram3 i j := by
  intro i j; fin_cases i <;> fin_cases j
  exacts [gram3_111_111, gram3_111_21, gram3_111_3, gram3_21_111, gram3_21_21, gram3_21_3, gram3_3_111, gram3_3_21, gram3_3_3]

/-- Printed degree-4 h-basis, printed order h1111, h211, h22, h31, h4. -/
def hshapes4 : Fin 5 → DegreeShapes.DegreeShape 4 := ![(⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4), (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4), (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4), (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4), (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4)]
/-- Printed Sec. 5.2 degree-4 q = -1 quotient table, verbatim. -/
def printedGram4 : Matrix (Fin 5) (Fin 5) ℤ := !![0, 0, 2, 0, 1;
    0, 1, 2, 1, 1;
    2, 2, 1, 2, 1;
    0, 1, 2, 0, 1;
    1, 1, 1, 1, 1]
theorem gram4_1111_1111 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_1111_211 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_1111_22 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_1111_31 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_1111_4 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_211_1111 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_211_211 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_211_22 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_211_31 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_211_4 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_22_1111 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_22_211 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_22_22 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_22_31 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_22_4 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_31_1111 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_31_211 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_31_22 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_31_31 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_31_4 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_4_1111 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_4_211 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_4_22 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_4_31 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram4_4_4 : EKDualBases.Mh 4 (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
/-- Sec. 5.2 degree 4: the printed q = -1 table is the existing Gram matrix `Mh`. -/
theorem gram_table4 : ∀ i j, EKDualBases.Mh 4 (hshapes4 i) (hshapes4 j) = printedGram4 i j := by
  intro i j; fin_cases i <;> fin_cases j
  exacts [gram4_1111_1111, gram4_1111_211, gram4_1111_22, gram4_1111_31, gram4_1111_4, gram4_211_1111, gram4_211_211, gram4_211_22, gram4_211_31, gram4_211_4, gram4_22_1111, gram4_22_211, gram4_22_22, gram4_22_31, gram4_22_4, gram4_31_1111, gram4_31_211, gram4_31_22, gram4_31_31, gram4_31_4, gram4_4_1111, gram4_4_211, gram4_4_22, gram4_4_31, gram4_4_4]

/-- Printed degree-5 h-basis, printed order h11111, h2111, h221, h311, h32, h41, h5. -/
def hshapes5 : Fin 7 → DegreeShapes.DegreeShape 5 := ![(⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5), (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5), (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5), (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5), (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5), (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5), (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5)]
/-- Printed Sec. 5.2 degree-5 q = -1 quotient table, verbatim. -/
def printedGram5 : Matrix (Fin 7) (Fin 7) ℤ := !![0, 0, 2, 0, 2, 1, 1;
    0, 1, 0, 1, 3, 0, 1;
    2, 0, (-3), 2, 3, (-1), 1;
    0, 1, 2, 1, 2, 1, 1;
    2, 3, 3, 2, 1, 2, 1;
    1, 0, (-1), 1, 2, 0, 1;
    1, 1, 1, 1, 1, 1, 1]
theorem gram5_11111_11111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_11111_2111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_11111_221 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_11111_311 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_11111_32 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_11111_41 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_11111_5 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_2111_11111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_2111_2111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_2111_221 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_2111_311 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_2111_32 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 3 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_2111_41 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_2111_5 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_221_11111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_221_2111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_221_221 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = (-3) := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_221_311 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_221_32 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 3 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_221_41 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = (-1) := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_221_5 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_311_11111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_311_2111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_311_221 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_311_311 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_311_32 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_311_41 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_311_5 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_32_11111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_32_2111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 3 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_32_221 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 3 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_32_311 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_32_32 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_32_41 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_32_5 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_41_11111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_41_2111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_41_221 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = (-1) := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_41_311 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_41_32 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 2 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_41_41 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 0 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_41_5 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_5_11111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [1,1,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_5_2111 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,1,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_5_221 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [2,2,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_5_311 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,1,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_5_32 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [3,2] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_5_41 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [4,1] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gram5_5_5 : EKDualBases.Mh 5 (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) (⟨YoungDiagram.ofRowLens [5] (by decide), card_yd _ _ 5 rfl⟩ : DegreeShapes.DegreeShape 5) = 1 := by
  rw [Mh_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
/-- Sec. 5.2 degree 5: the printed q = -1 table is the existing Gram matrix `Mh`. -/
theorem gram_table5 : ∀ i j, EKDualBases.Mh 5 (hshapes5 i) (hshapes5 j) = printedGram5 i j := by
  intro i j; fin_cases i <;> fin_cases j
  exacts [gram5_11111_11111, gram5_11111_2111, gram5_11111_221, gram5_11111_311, gram5_11111_32, gram5_11111_41, gram5_11111_5, gram5_2111_11111, gram5_2111_2111, gram5_2111_221, gram5_2111_311, gram5_2111_32, gram5_2111_41, gram5_2111_5, gram5_221_11111, gram5_221_2111, gram5_221_221, gram5_221_311, gram5_221_32, gram5_221_41, gram5_221_5, gram5_311_11111, gram5_311_2111, gram5_311_221, gram5_311_311, gram5_311_32, gram5_311_41, gram5_311_5, gram5_32_11111, gram5_32_2111, gram5_32_221, gram5_32_311, gram5_32_32, gram5_32_41, gram5_32_5, gram5_41_11111, gram5_41_2111, gram5_41_221, gram5_41_311, gram5_41_32, gram5_41_41, gram5_41_5, gram5_5_11111, gram5_5_2111, gram5_5_221, gram5_5_311, gram5_5_32, gram5_5_41, gram5_5_5]

/-! ## Printed data, Sec. 5.2: unspecialized q, specialised at q = -1 -/

open Polynomial in
/-- The printed (unbalanced) q-number `[n] = 1 + q + ... + q^(n-1)`. -/
noncomputable def qi (n : ℕ) : Polynomial ℤ := ∑ i ∈ Finset.range n, X ^ i
open Polynomial in
/-- The printed q-factorial `[n]! = [n][n-1]...[1]`. -/
noncomputable def qf (n : ℕ) : Polynomial ℤ := ∏ i ∈ Finset.range n, qi (i+1)

/-- `mixed` of an explicit composition, all colours h. -/
noncomputable def hword (l : List ℕ) : EKRadicalQuotient.Q :=
  EKMixedPairing.mixed (fun i : Fin l.length => l.get i) (fun _ => false)

theorem hword_pairing (a b : List ℕ) :
    EKRadicalQuotient.quotientPairing (hword a) (hword b) = mhEval a b := by
  rw [hword, hword, compPairing_eval, List.ofFn_get, List.ofFn_get]

open Polynomial in
/-- Printed entry (h1, h1) = `1`, at q = -1. -/
theorem qgen1_1_1 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1]) (hword [1]) := by
  rw [hword_pairing, show mhEval [1] [1] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]

open Polynomial in
/-- Printed entry (h11, h11) = `[2]`, at q = -1. -/
theorem qgen2_11_11 : (qi 2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1]) (hword [1,1]) := by
  rw [hword_pairing, show mhEval [1,1] [1,1] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h11, h2) = `1`, at q = -1. -/
theorem qgen2_11_2 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1]) (hword [2]) := by
  rw [hword_pairing, show mhEval [1,1] [2] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h2, h2) = `1`, at q = -1. -/
theorem qgen2_2_2 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [2]) (hword [2]) := by
  rw [hword_pairing, show mhEval [2] [2] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]

open Polynomial in
/-- Printed entry (h111, h111) = `[3]!`, at q = -1. -/
theorem qgen3_111_111 : (qf 3).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,1]) (hword [1,1,1]) := by
  rw [hword_pairing, show mhEval [1,1,1] [1,1,1] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h111, h12) = `[3]`, at q = -1. -/
theorem qgen3_111_12 : (qi 3).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,1]) (hword [1,2]) := by
  rw [hword_pairing, show mhEval [1,1,1] [1,2] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h111, h21) = `[3]`, at q = -1. -/
theorem qgen3_111_21 : (qi 3).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,1]) (hword [2,1]) := by
  rw [hword_pairing, show mhEval [1,1,1] [2,1] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h111, h3) = `1`, at q = -1. -/
theorem qgen3_111_3 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,1]) (hword [3]) := by
  rw [hword_pairing, show mhEval [1,1,1] [3] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h12, h12) = `[2]`, at q = -1. -/
theorem qgen3_12_12 : (qi 2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,2]) (hword [1,2]) := by
  rw [hword_pairing, show mhEval [1,2] [1,2] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h12, h21) = `1+q^2`, at q = -1. -/
theorem qgen3_12_21 : ((1 : Polynomial ℤ) + X^2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,2]) (hword [2,1]) := by
  rw [hword_pairing, show mhEval [1,2] [2,1] = 2 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h12, h3) = `1`, at q = -1. -/
theorem qgen3_12_3 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,2]) (hword [3]) := by
  rw [hword_pairing, show mhEval [1,2] [3] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h21, h21) = `[2]`, at q = -1. -/
theorem qgen3_21_21 : (qi 2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [2,1]) (hword [2,1]) := by
  rw [hword_pairing, show mhEval [2,1] [2,1] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h21, h3) = `1`, at q = -1. -/
theorem qgen3_21_3 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [2,1]) (hword [3]) := by
  rw [hword_pairing, show mhEval [2,1] [3] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h3, h3) = `1`, at q = -1. -/
theorem qgen3_3_3 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [3]) (hword [3]) := by
  rw [hword_pairing, show mhEval [3] [3] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]

open Polynomial in
/-- Printed entry (h1111, h1111) = `[4]!`, at q = -1. -/
theorem qgen4_1111_1111 : (qf 4).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,1,1]) (hword [1,1,1,1]) := by
  rw [hword_pairing, show mhEval [1,1,1,1] [1,1,1,1] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h1111, h112) = `[4][3]`, at q = -1. -/
theorem qgen4_1111_112 : (qi 4 * qi 3).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,1,1]) (hword [1,1,2]) := by
  rw [hword_pairing, show mhEval [1,1,1,1] [1,1,2] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h1111, h121) = `[4][3]`, at q = -1. -/
theorem qgen4_1111_121 : (qi 4 * qi 3).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,1,1]) (hword [1,2,1]) := by
  rw [hword_pairing, show mhEval [1,1,1,1] [1,2,1] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h1111, h211) = `[4][3]`, at q = -1. -/
theorem qgen4_1111_211 : (qi 4 * qi 3).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,1,1]) (hword [2,1,1]) := by
  rw [hword_pairing, show mhEval [1,1,1,1] [2,1,1] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h1111, h22) = `[5]+q^2`, at q = -1. -/
theorem qgen4_1111_22 : (qi 5 + X^2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,1,1]) (hword [2,2]) := by
  rw [hword_pairing, show mhEval [1,1,1,1] [2,2] = 2 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h1111, h13) = `[4]`, at q = -1. -/
theorem qgen4_1111_13 : (qi 4).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,1,1]) (hword [1,3]) := by
  rw [hword_pairing, show mhEval [1,1,1,1] [1,3] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h1111, h31) = `[4]`, at q = -1. -/
theorem qgen4_1111_31 : (qi 4).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,1,1]) (hword [3,1]) := by
  rw [hword_pairing, show mhEval [1,1,1,1] [3,1] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h1111, h4) = `1`, at q = -1. -/
theorem qgen4_1111_4 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,1,1]) (hword [4]) := by
  rw [hword_pairing, show mhEval [1,1,1,1] [4] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h112, h112) = `[5]+q[2]`, at q = -1. -/
theorem qgen4_112_112 : (qi 5 + X * qi 2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,2]) (hword [1,1,2]) := by
  rw [hword_pairing, show mhEval [1,1,2] [1,1,2] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h112, h121) = `[5]+q^2[2]`, at q = -1. -/
theorem qgen4_112_121 : (qi 5 + X^2 * qi 2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,2]) (hword [1,2,1]) := by
  rw [hword_pairing, show mhEval [1,1,2] [1,2,1] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h112, h211) = `[6]+q^2`, at q = -1. -/
theorem qgen4_112_211 : (qi 6 + X^2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,2]) (hword [2,1,1]) := by
  rw [hword_pairing, show mhEval [1,1,2] [2,1,1] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h112, h22) = `[3]+q^4`, at q = -1. -/
theorem qgen4_112_22 : (qi 3 + X^4).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,2]) (hword [2,2]) := by
  rw [hword_pairing, show mhEval [1,1,2] [2,2] = 2 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h112, h13) = `[3]`, at q = -1. -/
theorem qgen4_112_13 : (qi 3).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,2]) (hword [1,3]) := by
  rw [hword_pairing, show mhEval [1,1,2] [1,3] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h112, h31) = `[1]+q^2[2]`, at q = -1. -/
theorem qgen4_112_31 : (qi 1 + X^2 * qi 2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,2]) (hword [3,1]) := by
  rw [hword_pairing, show mhEval [1,1,2] [3,1] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h112, h4) = `1`, at q = -1. -/
theorem qgen4_112_4 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,1,2]) (hword [4]) := by
  rw [hword_pairing, show mhEval [1,1,2] [4] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h121, h121) = `[4]+q+q^3+q^5`, at q = -1. -/
theorem qgen4_121_121 : (qi 4 + X + X^3 + X^5).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,2,1]) (hword [1,2,1]) := by
  rw [hword_pairing, show mhEval [1,2,1] [1,2,1] = (-3) by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h121, h211) = `[5]+q^2[2]`, at q = -1. -/
theorem qgen4_121_211 : (qi 5 + X^2 * qi 2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,2,1]) (hword [2,1,1]) := by
  rw [hword_pairing, show mhEval [1,2,1] [2,1,1] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h121, h22) = `1+2q^2+q^3`, at q = -1. -/
theorem qgen4_121_22 : ((1 : Polynomial ℤ) + (2 : Polynomial ℤ) * X^2 + X^3).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,2,1]) (hword [2,2]) := by
  rw [hword_pairing, show mhEval [1,2,1] [2,2] = 2 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h121, h13) = `[2]+q^3`, at q = -1. -/
theorem qgen4_121_13 : (qi 2 + X^3).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,2,1]) (hword [1,3]) := by
  rw [hword_pairing, show mhEval [1,2,1] [1,3] = (-1) by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h121, h31) = `[2]+q^3`, at q = -1. -/
theorem qgen4_121_31 : (qi 2 + X^3).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,2,1]) (hword [3,1]) := by
  rw [hword_pairing, show mhEval [1,2,1] [3,1] = (-1) by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h121, h4) = `1`, at q = -1. -/
theorem qgen4_121_4 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,2,1]) (hword [4]) := by
  rw [hword_pairing, show mhEval [1,2,1] [4] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h211, h211) = `[5]+q[2]`, at q = -1. -/
theorem qgen4_211_211 : (qi 5 + X * qi 2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [2,1,1]) (hword [2,1,1]) := by
  rw [hword_pairing, show mhEval [2,1,1] [2,1,1] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h211, h22) = `[3]+q^4`, at q = -1. -/
theorem qgen4_211_22 : (qi 3 + X^4).eval (-1) = EKRadicalQuotient.quotientPairing (hword [2,1,1]) (hword [2,2]) := by
  rw [hword_pairing, show mhEval [2,1,1] [2,2] = 2 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h211, h13) = `1+q^2[2]`, at q = -1. -/
theorem qgen4_211_13 : ((1 : Polynomial ℤ) + X^2 * qi 2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [2,1,1]) (hword [1,3]) := by
  rw [hword_pairing, show mhEval [2,1,1] [1,3] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h211, h31) = `[3]`, at q = -1. -/
theorem qgen4_211_31 : (qi 3).eval (-1) = EKRadicalQuotient.quotientPairing (hword [2,1,1]) (hword [3,1]) := by
  rw [hword_pairing, show mhEval [2,1,1] [3,1] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h211, h4) = `1`, at q = -1. -/
theorem qgen4_211_4 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [2,1,1]) (hword [4]) := by
  rw [hword_pairing, show mhEval [2,1,1] [4] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h22, h22) = `[2]+q^4`, at q = -1. -/
theorem qgen4_22_22 : (qi 2 + X^4).eval (-1) = EKRadicalQuotient.quotientPairing (hword [2,2]) (hword [2,2]) := by
  rw [hword_pairing, show mhEval [2,2] [2,2] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h22, h13) = `1+q^2`, at q = -1. -/
theorem qgen4_22_13 : ((1 : Polynomial ℤ) + X^2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [2,2]) (hword [1,3]) := by
  rw [hword_pairing, show mhEval [2,2] [1,3] = 2 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h22, h31) = `1+q^2`, at q = -1. -/
theorem qgen4_22_31 : ((1 : Polynomial ℤ) + X^2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [2,2]) (hword [3,1]) := by
  rw [hword_pairing, show mhEval [2,2] [3,1] = 2 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h22, h4) = `1`, at q = -1. -/
theorem qgen4_22_4 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [2,2]) (hword [4]) := by
  rw [hword_pairing, show mhEval [2,2] [4] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h13, h13) = `[2]`, at q = -1. -/
theorem qgen4_13_13 : (qi 2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,3]) (hword [1,3]) := by
  rw [hword_pairing, show mhEval [1,3] [1,3] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h13, h31) = `1+q^3`, at q = -1. -/
theorem qgen4_13_31 : ((1 : Polynomial ℤ) + X^3).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,3]) (hword [3,1]) := by
  rw [hword_pairing, show mhEval [1,3] [3,1] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h13, h4) = `1`, at q = -1. -/
theorem qgen4_13_4 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [1,3]) (hword [4]) := by
  rw [hword_pairing, show mhEval [1,3] [4] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h31, h31) = `[2]`, at q = -1. -/
theorem qgen4_31_31 : (qi 2).eval (-1) = EKRadicalQuotient.quotientPairing (hword [3,1]) (hword [3,1]) := by
  rw [hword_pairing, show mhEval [3,1] [3,1] = 0 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h31, h4) = `1`, at q = -1. -/
theorem qgen4_31_4 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [3,1]) (hword [4]) := by
  rw [hword_pairing, show mhEval [3,1] [4] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]
open Polynomial in
/-- Printed entry (h4, h4) = `1`, at q = -1. -/
theorem qgen4_4_4 : ((1 : Polynomial ℤ)).eval (-1) = EKRadicalQuotient.quotientPairing (hword [4]) (hword [4]) := by
  rw [hword_pairing, show mhEval [4] [4] = 1 by decide +kernel]
  norm_num [qi, qf, Finset.sum_range_succ, Finset.prod_range_succ]

open EKPairingMatrices EKDualBases DegreeShapes EKIntegralBases

/-! ## Certified evaluator III: zero-one matrices (the e/h Gram matrix `M`) -/

def le1 (L : List (List ℕ)) : Prop := ∀ w ∈ L, ∀ x ∈ w, x ≤ 1

instance decLe1 (L : List (List ℕ)) : Decidable (le1 L) := by unfold le1; infer_instance

theorem le1_toL {r c : ℕ} (A : Raw r c) : le1 (toL A) ↔ ∀ i j, A i j ≤ 1 := by
  simp only [le1, toL, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]

def mEval (bl al : List ℕ) : ℤ :=
  ∑ L ∈ matSet bl al, if le1 L then (-1 : ℤ) ^ crossL L bl.length al.length else 0

theorem M_eval (d : ℕ) (ν μ : DegreeShape d) : M d ν μ = mEval ν.val.rowLens μ.val.rowLens := by
  classical
  rw [proposition_3_1_M]
  unfold ZeroOneMatrices
  rw [← Finset.sum_subtype (Finset.univ.filter (fun A : Mat (EKSemiorthogonality.rows ν.val)
      (EKSemiorthogonality.rows μ.val) => ∀ i j, A.val i j ≤ 1)) (by simp)
      (fun A => (-1 : ℤ) ^ crossing A.val), Finset.sum_filter]
  have h := mat_sum (EKSemiorthogonality.rows ν.val) (EKSemiorthogonality.rows μ.val)
    (fun L => if le1 L then (-1 : ℤ) ^ crossL L (ν.val.colLen 0) (μ.val.colLen 0) else 0)
  simp only [le1_toL, ← crossing_toL] at h
  rw [h, mEval, EKSemiorthogonality.rowLens_eq_ofFn, EKSemiorthogonality.rowLens_eq_ofFn,
    List.length_ofFn, List.length_ofFn]

theorem M_ofRowLens (d : ℕ) (w v : List ℕ) (hw : w.Sorted (· ≥ ·)) (hv : v.Sorted (· ≥ ·))
    (hwp : ∀ x ∈ w, 0 < x) (hvp : ∀ x ∈ v, 0 < x)
    (hwd : (YoungDiagram.ofRowLens w hw).card = d) (hvd : (YoungDiagram.ofRowLens v hv).card = d) :
    M d ⟨YoungDiagram.ofRowLens w hw, hwd⟩ ⟨YoungDiagram.ofRowLens v hv, hvd⟩ = mEval w v := by
  rw [M_eval]
  show mEval (YoungDiagram.ofRowLens w hw).rowLens (YoungDiagram.ofRowLens v hv).rowLens = _
  rw [YoungDiagram.rowLens_ofRowLens_eq_self hwp, YoungDiagram.rowLens_ofRowLens_eq_self hvp]

/-! ## Exhaustive partition lists (all degree-d shapes) -/

/-- Partitions of `s` with parts `≤ m`, at most `f` parts (weakly decreasing lists). -/
def partL : ℕ → ℕ → ℕ → List (List ℕ)
  | _, 0, _ => [[]]
  | 0, _+1, _ => []
  | f+1, s+1, m => (List.range (min (s+1) m)).flatMap
      (fun b => (partL f (s - b) (b+1)).map ((b+1) :: ·))

theorem mem_partL : ∀ (l : List ℕ) (f s m : ℕ), l.Sorted (· ≥ ·) → (∀ x ∈ l, 0 < x) →
    (∀ x ∈ l, x ≤ m) → l.sum = s → l.length ≤ f → l ∈ partL f s m
  | [], f, s, m, _, _, _, hs, _ => by subst hs; cases f <;> simp [partL]
  | a :: l, f, s, m, hso, hp, hm, hs, hf => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have ha := hp a (by simp)
    have ham := hm a (by simp)
    simp only [List.sum_cons] at hs
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hso' := List.sorted_cons.mp hso
    have ih := mem_partL l f (s - (a-1)) a hso'.2 (fun x hx => hp x (by simp [hx]))
      (fun x hx => hso'.1 x hx) (by omega) (by simp at hf; omega)
    simp only [partL, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨a - 1, by omega, l, by rw [show a - 1 + 1 = a by omega]; exact ih, by congr 1; omega⟩

theorem rowLens_sum (μ : YoungDiagram) : μ.rowLens.sum = μ.card := by
  conv_rhs => rw [← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := μ)]
  rw [EKPartitionSpanning.card_ofRowLens]

theorem rowLens_mem_partL (d : ℕ) (ν : DegreeShape d) : ν.val.rowLens ∈ partL d d d := by
  have hs : ν.val.rowLens.sum = d := by rw [rowLens_sum]; exact ν.property
  apply mem_partL _ _ _ _ (YoungDiagram.rowLens_sorted _) (YoungDiagram.pos_of_mem_rowLens _)
  · intro x hx; have := List.le_sum_of_mem hx; omega
  · exact hs
  · have := List.length_le_sum_of_one_le _ (YoungDiagram.pos_of_mem_rowLens ν.val); omega

/-- Generic exhaustiveness: a printed list of shapes covering `partL d d d` is all of `DegreeShape d`. -/
theorem exhaust {d k : ℕ} (S : Fin k → DegreeShape d) (pl : Fin k → List ℕ)
    (hS : ∀ j, (S j).val.rowLens = pl j) (hcov : ∀ l ∈ partL d d d, ∃ j, pl j = l) :
    ∀ ν, ∃ j, ν = S j := by
  intro ν
  obtain ⟨j, hj⟩ := hcov _ (rowLens_mem_partL d ν)
  exact ⟨j, Subtype.ext (shape_eq_of_rowLens (by rw [hS, hj]))⟩

theorem inj_of_rowLens {d k : ℕ} (S : Fin k → DegreeShape d) (pl : Fin k → List ℕ)
    (hS : ∀ j, (S j).val.rowLens = pl j) (hpl : Function.Injective pl) : Function.Injective S := by
  intro a b h; apply hpl; rw [← hS, ← hS, h]

/-! ## Generic dual-basis and Kostka-inversion lemmas -/

theorem m_of_table {d k : ℕ} (S : Fin k → DegreeShape d) (hex : ∀ ν, ∃ j, ν = S j)
    (hinj : Function.Injective S) (G : Matrix (Fin k) (Fin k) ℤ)
    (hG : ∀ j l, Mh d (S j) (S l) = G j l) (c : Fin k → ℤ) (i : Fin k)
    (hc : ∀ j, ∑ l, c l * G j l = if j = i then 1 else 0) :
    mBasis d (S i) = ∑ l, c l • degreeHBasis d (S l) := by
  symm; apply m_unique
  intro ν
  obtain ⟨j, rfl⟩ := hex ν
  rw [Submodule.coe_sum, map_sum]
  simp only [Submodule.coe_smul, degreeHBasis_apply, map_zsmul, smul_eq_mul]
  have key : ∑ l, c l * Mh d (S j) (S l) = if j = i then 1 else 0 := by rw [← hc j]; simp [hG]
  refine Eq.trans key ?_
  by_cases hji : j = i
  · subst hji; simp
  · rw [if_neg hji, if_neg (fun h => hji (hinj h))]

theorem f_of_table {d k : ℕ} (S : Fin k → DegreeShape d) (hex : ∀ ν, ∃ j, ν = S j)
    (hinj : Function.Injective S) (G : Matrix (Fin k) (Fin k) ℤ)
    (hG : ∀ j l, M d (S j) (S l) = G j l) (c : Fin k → ℤ) (i : Fin k)
    (hc : ∀ j, ∑ l, c l * G j l = if j = i then 1 else 0) :
    fBasis d (S i) = ∑ l, c l • degreeHBasis d (S l) := by
  symm; apply f_unique
  intro ν
  obtain ⟨j, rfl⟩ := hex ν
  rw [Submodule.coe_sum, map_sum]
  simp only [Submodule.coe_smul, degreeHBasis_apply, map_zsmul, smul_eq_mul]
  have key : ∑ l, c l * M d (S j) (S l) = if j = i then 1 else 0 := by rw [← hc j]; simp [hG]
  refine Eq.trans key ?_
  by_cases hji : j = i
  · subst hji; simp
  · rw [if_neg hji, if_neg (fun h => hji (hinj h))]

theorem kostka_inverse_relation {k : ℕ} {V : Type*} [AddCommGroup V]
    (K S : Matrix (Fin k) (Fin k) ℤ) (h : Fin k → V)
    (hKS : ∀ μ ν, ∑ l, K l μ * S l ν = if μ = ν then 1 else 0) (μ : Fin k) :
    h μ = ∑ l, K l μ • ∑ ν, S l ν • h ν := by
  symm
  calc ∑ l, K l μ • ∑ ν, S l ν • h ν = ∑ ν, (∑ l, K l μ * S l ν) • h ν := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]; exact Finset.sum_comm
    _ = h μ := by simp [hKS]

/-! ## Printed data, Sec. 5.1: odd monomial / forgotten (deg <= 4) and odd Schur (deg <= 5) in the h-basis -/

def pl1 : Fin 1 → List ℕ := ![[1]]
theorem hs1 : ∀ j, (hshapes1 j).val.rowLens = pl1 j := by
  intro j; fin_cases j; exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
/-- The printed degree-1 list is ALL shapes of degree 1. -/
theorem exhaust1 : ∀ ν, ∃ j, ν = hshapes1 j := exhaust hshapes1 pl1 hs1 (by decide +kernel)
theorem inj1 : Function.Injective hshapes1 := inj_of_rowLens hshapes1 pl1 hs1 (by decide)
/-- Existing e/h Gram matrix `M` in degree 1 (values kernel-proved entrywise below; not printed in EK). -/
def gramM1 : Matrix (Fin 1) (Fin 1) ℤ := !![1]
theorem gramM1_1_1 : EKDualBases.M 1 (⟨YoungDiagram.ofRowLens [1] (by decide), card_yd _ _ 1 rfl⟩ : DegreeShapes.DegreeShape 1) (⟨YoungDiagram.ofRowLens [1] (by decide), card_yd _ _ 1 rfl⟩ : DegreeShapes.DegreeShape 1) = 1 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM_table1 : ∀ i j, EKDualBases.M 1 (hshapes1 i) (hshapes1 j) = gramM1 i j := by
  intro i j; fin_cases i; fin_cases j
  exacts [gramM1_1_1]
/-- Printed Sec. 5.1: m1 = h1. -/
theorem mExp1_1 : mBasis 1 (hshapes1 0) = ∑ l, (![1] : Fin 1 → ℤ) l • degreeHBasis 1 (hshapes1 l) :=
  m_of_table hshapes1 exhaust1 inj1 printedGram1 gram_table1 _ 0 (by decide)
/-- Printed Sec. 5.1: f1 = h1. -/
theorem fExp1_1 : fBasis 1 (hshapes1 0) = ∑ l, (![1] : Fin 1 → ℤ) l • degreeHBasis 1 (hshapes1 l) :=
  f_of_table hshapes1 exhaust1 inj1 gramM1 gramM_table1 _ 0 (by decide)
/-- Printed Sec. 5.1 degree-1 odd Schur functions, row λ = coefficients of s_λ in the printed h-basis: s1 = h1. -/
def printedSchur1 : Matrix (Fin 1) (Fin 1) ℤ := !![1]
/-- The printed odd Schur expansions invert the existing signed Kostka matrix (row-vector convention h_μ = Σ_λ K_(λμ) s_λ). -/
theorem schur_kostka_inverse1 : ∀ μ ν, ∑ l, TableauDominance.signedKostka (shapes1 l) (shapes1 μ) * printedSchur1 l ν = if μ = ν then 1 else 0 := by
  simp only [kostka_table1]; decide
/-- Hence, in the actual quotient: with the printed s_λ := Σ_ν S_(λν) h_ν, h_μ = Σ_λ signedKostka λ μ • s_λ. -/
theorem schur_relation1 (μ : Fin 1) : EKPartitionSpanning.hPartition (hshapes1 μ).val = ∑ l, TableauDominance.signedKostka (shapes1 l) (shapes1 μ) • ∑ ν, printedSchur1 l ν • EKPartitionSpanning.hPartition (hshapes1 ν).val :=
  kostka_inverse_relation (Matrix.of fun l μ => TableauDominance.signedKostka (shapes1 l) (shapes1 μ)) printedSchur1 (fun ν => EKPartitionSpanning.hPartition (hshapes1 ν).val) schur_kostka_inverse1 μ

def pl2 : Fin 2 → List ℕ := ![[1,1], [2]]
theorem hs2 : ∀ j, (hshapes2 j).val.rowLens = pl2 j := by
  intro j; fin_cases j <;> exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
/-- The printed degree-2 list is ALL shapes of degree 2. -/
theorem exhaust2 : ∀ ν, ∃ j, ν = hshapes2 j := exhaust hshapes2 pl2 hs2 (by decide +kernel)
theorem inj2 : Function.Injective hshapes2 := inj_of_rowLens hshapes2 pl2 hs2 (by decide)
/-- Existing e/h Gram matrix `M` in degree 2 (values kernel-proved entrywise below; not printed in EK). -/
def gramM2 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1;
    1, 0]
theorem gramM2_11_11 : EKDualBases.M 2 (⟨YoungDiagram.ofRowLens [1,1] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) (⟨YoungDiagram.ofRowLens [1,1] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM2_11_2 : EKDualBases.M 2 (⟨YoungDiagram.ofRowLens [1,1] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) (⟨YoungDiagram.ofRowLens [2] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) = 1 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM2_2_11 : EKDualBases.M 2 (⟨YoungDiagram.ofRowLens [2] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) (⟨YoungDiagram.ofRowLens [1,1] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) = 1 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM2_2_2 : EKDualBases.M 2 (⟨YoungDiagram.ofRowLens [2] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) (⟨YoungDiagram.ofRowLens [2] (by decide), card_yd _ _ 2 rfl⟩ : DegreeShapes.DegreeShape 2) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM_table2 : ∀ i j, EKDualBases.M 2 (hshapes2 i) (hshapes2 j) = gramM2 i j := by
  intro i j; fin_cases i <;> fin_cases j
  exacts [gramM2_11_11, gramM2_11_2, gramM2_2_11, gramM2_2_2]
/-- Printed Sec. 5.1: m11 = -h11 +h2. -/
theorem mExp2_11 : mBasis 2 (hshapes2 0) = ∑ l, (![(-1), 1] : Fin 2 → ℤ) l • degreeHBasis 2 (hshapes2 l) :=
  m_of_table hshapes2 exhaust2 inj2 printedGram2 gram_table2 _ 0 (by decide)
/-- Printed Sec. 5.1: m2 = h11. -/
theorem mExp2_2 : mBasis 2 (hshapes2 1) = ∑ l, (![1, 0] : Fin 2 → ℤ) l • degreeHBasis 2 (hshapes2 l) :=
  m_of_table hshapes2 exhaust2 inj2 printedGram2 gram_table2 _ 1 (by decide)
/-- Printed Sec. 5.1: f11 = h2. -/
theorem fExp2_11 : fBasis 2 (hshapes2 0) = ∑ l, (![0, 1] : Fin 2 → ℤ) l • degreeHBasis 2 (hshapes2 l) :=
  f_of_table hshapes2 exhaust2 inj2 gramM2 gramM_table2 _ 0 (by decide)
/-- Printed Sec. 5.1: f2 = h11. -/
theorem fExp2_2 : fBasis 2 (hshapes2 1) = ∑ l, (![1, 0] : Fin 2 → ℤ) l • degreeHBasis 2 (hshapes2 l) :=
  f_of_table hshapes2 exhaust2 inj2 gramM2 gramM_table2 _ 1 (by decide)
/-- Printed Sec. 5.1 degree-2 odd Schur functions, row λ = coefficients of s_λ in the printed h-basis: s11 = h11 -h2; s2 = h2. -/
def printedSchur2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, (-1);
    0, 1]
/-- The printed odd Schur expansions invert the existing signed Kostka matrix (row-vector convention h_μ = Σ_λ K_(λμ) s_λ). -/
theorem schur_kostka_inverse2 : ∀ μ ν, ∑ l, TableauDominance.signedKostka (shapes2 l) (shapes2 μ) * printedSchur2 l ν = if μ = ν then 1 else 0 := by
  simp only [kostka_table2]; decide
/-- Hence, in the actual quotient: with the printed s_λ := Σ_ν S_(λν) h_ν, h_μ = Σ_λ signedKostka λ μ • s_λ. -/
theorem schur_relation2 (μ : Fin 2) : EKPartitionSpanning.hPartition (hshapes2 μ).val = ∑ l, TableauDominance.signedKostka (shapes2 l) (shapes2 μ) • ∑ ν, printedSchur2 l ν • EKPartitionSpanning.hPartition (hshapes2 ν).val :=
  kostka_inverse_relation (Matrix.of fun l μ => TableauDominance.signedKostka (shapes2 l) (shapes2 μ)) printedSchur2 (fun ν => EKPartitionSpanning.hPartition (hshapes2 ν).val) schur_kostka_inverse2 μ

def pl3 : Fin 3 → List ℕ := ![[1,1,1], [2,1], [3]]
theorem hs3 : ∀ j, (hshapes3 j).val.rowLens = pl3 j := by
  intro j; fin_cases j <;> exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
/-- The printed degree-3 list is ALL shapes of degree 3. -/
theorem exhaust3 : ∀ ν, ∃ j, ν = hshapes3 j := exhaust hshapes3 pl3 hs3 (by decide +kernel)
theorem inj3 : Function.Injective hshapes3 := inj_of_rowLens hshapes3 pl3 hs3 (by decide)
/-- Existing e/h Gram matrix `M` in degree 3 (values kernel-proved entrywise below; not printed in EK). -/
def gramM3 : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 1;
    1, (-1), 0;
    1, 0, 0]
theorem gramM3_111_111 : EKDualBases.M 3 (⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM3_111_21 : EKDualBases.M 3 (⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 1 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM3_111_3 : EKDualBases.M 3 (⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 1 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM3_21_111 : EKDualBases.M 3 (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 1 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM3_21_21 : EKDualBases.M 3 (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = (-1) := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM3_21_3 : EKDualBases.M 3 (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM3_3_111 : EKDualBases.M 3 (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [1,1,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 1 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM3_3_21 : EKDualBases.M 3 (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [2,1] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM3_3_3 : EKDualBases.M 3 (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) (⟨YoungDiagram.ofRowLens [3] (by decide), card_yd _ _ 3 rfl⟩ : DegreeShapes.DegreeShape 3) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM_table3 : ∀ i j, EKDualBases.M 3 (hshapes3 i) (hshapes3 j) = gramM3 i j := by
  intro i j; fin_cases i <;> fin_cases j
  exacts [gramM3_111_111, gramM3_111_21, gramM3_111_3, gramM3_21_111, gramM3_21_21, gramM3_21_3, gramM3_3_111, gramM3_3_21, gramM3_3_3]
/-- Printed Sec. 5.1: m111 = -h111 +h3. -/
theorem mExp3_111 : mBasis 3 (hshapes3 0) = ∑ l, (![(-1), 0, 1] : Fin 3 → ℤ) l • degreeHBasis 3 (hshapes3 l) :=
  m_of_table hshapes3 exhaust3 inj3 printedGram3 gram_table3 _ 0 (by decide)
/-- Printed Sec. 5.1: m21 = -h21 +h3. -/
theorem mExp3_21 : mBasis 3 (hshapes3 1) = ∑ l, (![0, (-1), 1] : Fin 3 → ℤ) l • degreeHBasis 3 (hshapes3 l) :=
  m_of_table hshapes3 exhaust3 inj3 printedGram3 gram_table3 _ 1 (by decide)
/-- Printed Sec. 5.1: m3 = h111 +h21 -h3. -/
theorem mExp3_3 : mBasis 3 (hshapes3 2) = ∑ l, (![1, 1, (-1)] : Fin 3 → ℤ) l • degreeHBasis 3 (hshapes3 l) :=
  m_of_table hshapes3 exhaust3 inj3 printedGram3 gram_table3 _ 2 (by decide)
/-- Printed Sec. 5.1: f111 = h3. -/
theorem fExp3_111 : fBasis 3 (hshapes3 0) = ∑ l, (![0, 0, 1] : Fin 3 → ℤ) l • degreeHBasis 3 (hshapes3 l) :=
  f_of_table hshapes3 exhaust3 inj3 gramM3 gramM_table3 _ 0 (by decide)
/-- Printed Sec. 5.1: f21 = -h21 +h3. -/
theorem fExp3_21 : fBasis 3 (hshapes3 1) = ∑ l, (![0, (-1), 1] : Fin 3 → ℤ) l • degreeHBasis 3 (hshapes3 l) :=
  f_of_table hshapes3 exhaust3 inj3 gramM3 gramM_table3 _ 1 (by decide)
/-- Printed Sec. 5.1: f3 = h111 +h21 -h3. -/
theorem fExp3_3 : fBasis 3 (hshapes3 2) = ∑ l, (![1, 1, (-1)] : Fin 3 → ℤ) l • degreeHBasis 3 (hshapes3 l) :=
  f_of_table hshapes3 exhaust3 inj3 gramM3 gramM_table3 _ 2 (by decide)
/-- Printed Sec. 5.1 degree-3 odd Schur functions, row λ = coefficients of s_λ in the printed h-basis: s111 = h111 -h3; s21 = h21 -h3; s3 = h3. -/
def printedSchur3 : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, (-1);
    0, 1, (-1);
    0, 0, 1]
/-- The printed odd Schur expansions invert the existing signed Kostka matrix (row-vector convention h_μ = Σ_λ K_(λμ) s_λ). -/
theorem schur_kostka_inverse3 : ∀ μ ν, ∑ l, TableauDominance.signedKostka (shapes3 l) (shapes3 μ) * printedSchur3 l ν = if μ = ν then 1 else 0 := by
  simp only [kostka_table3]; decide
/-- Hence, in the actual quotient: with the printed s_λ := Σ_ν S_(λν) h_ν, h_μ = Σ_λ signedKostka λ μ • s_λ. -/
theorem schur_relation3 (μ : Fin 3) : EKPartitionSpanning.hPartition (hshapes3 μ).val = ∑ l, TableauDominance.signedKostka (shapes3 l) (shapes3 μ) • ∑ ν, printedSchur3 l ν • EKPartitionSpanning.hPartition (hshapes3 ν).val :=
  kostka_inverse_relation (Matrix.of fun l μ => TableauDominance.signedKostka (shapes3 l) (shapes3 μ)) printedSchur3 (fun ν => EKPartitionSpanning.hPartition (hshapes3 ν).val) schur_kostka_inverse3 μ

def pl4 : Fin 5 → List ℕ := ![[1,1,1,1], [2,1,1], [2,2], [3,1], [4]]
theorem hs4 : ∀ j, (hshapes4 j).val.rowLens = pl4 j := by
  intro j; fin_cases j <;> exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
/-- The printed degree-4 list is ALL shapes of degree 4. -/
theorem exhaust4 : ∀ ν, ∃ j, ν = hshapes4 j := exhaust hshapes4 pl4 hs4 (by decide +kernel)
theorem inj4 : Function.Injective hshapes4 := inj_of_rowLens hshapes4 pl4 hs4 (by decide)
/-- Existing e/h Gram matrix `M` in degree 4 (values kernel-proved entrywise below; not printed in EK). -/
def gramM4 : Matrix (Fin 5) (Fin 5) ℤ := !![0, 0, 2, 0, 1;
    0, 1, 0, 1, 0;
    2, 0, (-1), 0, 0;
    0, 1, 0, 0, 0;
    1, 0, 0, 0, 0]
theorem gramM4_1111_1111 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_1111_211 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_1111_22 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 2 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_1111_31 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_1111_4 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_211_1111 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_211_211 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_211_22 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_211_31 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_211_4 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_22_1111 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 2 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_22_211 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_22_22 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = (-1) := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_22_31 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_22_4 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_31_1111 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_31_211 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_31_22 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_31_31 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_31_4 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_4_1111 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [1,1,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 1 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_4_211 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,1,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_4_22 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [2,2] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_4_31 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [3,1] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM4_4_4 : EKDualBases.M 4 (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) (⟨YoungDiagram.ofRowLens [4] (by decide), card_yd _ _ 4 rfl⟩ : DegreeShapes.DegreeShape 4) = 0 := by
  rw [M_ofRowLens _ _ _ _ _ (by decide) (by decide)]; decide +kernel
theorem gramM_table4 : ∀ i j, EKDualBases.M 4 (hshapes4 i) (hshapes4 j) = gramM4 i j := by
  intro i j; fin_cases i <;> fin_cases j
  exacts [gramM4_1111_1111, gramM4_1111_211, gramM4_1111_22, gramM4_1111_31, gramM4_1111_4, gramM4_211_1111, gramM4_211_211, gramM4_211_22, gramM4_211_31, gramM4_211_4, gramM4_22_1111, gramM4_22_211, gramM4_22_22, gramM4_22_31, gramM4_22_4, gramM4_31_1111, gramM4_31_211, gramM4_31_22, gramM4_31_31, gramM4_31_4, gramM4_4_1111, gramM4_4_211, gramM4_4_22, gramM4_4_31, gramM4_4_4]
/-- Printed Sec. 5.1: m1111 = h1111 -h211 +h22 -h4. -/
theorem mExp4_1111 : mBasis 4 (hshapes4 0) = ∑ l, (![1, (-1), 1, 0, (-1)] : Fin 5 → ℤ) l • degreeHBasis 4 (hshapes4 l) :=
  m_of_table hshapes4 exhaust4 inj4 printedGram4 gram_table4 _ 0 (by decide)
/-- Printed Sec. 5.1: m211 = -h1111 +h31. -/
theorem mExp4_211 : mBasis 4 (hshapes4 1) = ∑ l, (![(-1), 0, 0, 1, 0] : Fin 5 → ℤ) l • degreeHBasis 4 (hshapes4 l) :=
  m_of_table hshapes4 exhaust4 inj4 printedGram4 gram_table4 _ 1 (by decide)
/-- Printed Sec. 5.1: m22 = h1111 +h22 -2h4. -/
theorem mExp4_22 : mBasis 4 (hshapes4 2) = ∑ l, (![1, 0, 1, 0, (-2)] : Fin 5 → ℤ) l • degreeHBasis 4 (hshapes4 l) :=
  m_of_table hshapes4 exhaust4 inj4 printedGram4 gram_table4 _ 2 (by decide)
/-- Printed Sec. 5.1: m31 = h211 -h31. -/
theorem mExp4_31 : mBasis 4 (hshapes4 3) = ∑ l, (![0, 1, 0, (-1), 0] : Fin 5 → ℤ) l • degreeHBasis 4 (hshapes4 l) :=
  m_of_table hshapes4 exhaust4 inj4 printedGram4 gram_table4 _ 3 (by decide)
/-- Printed Sec. 5.1: m4 = -h1111 -2h22 +4h4. -/
theorem mExp4_4 : mBasis 4 (hshapes4 4) = ∑ l, (![(-1), 0, (-2), 0, 4] : Fin 5 → ℤ) l • degreeHBasis 4 (hshapes4 l) :=
  m_of_table hshapes4 exhaust4 inj4 printedGram4 gram_table4 _ 4 (by decide)
/-- Printed Sec. 5.1: f1111 = h4. -/
theorem fExp4_1111 : fBasis 4 (hshapes4 0) = ∑ l, (![0, 0, 0, 0, 1] : Fin 5 → ℤ) l • degreeHBasis 4 (hshapes4 l) :=
  f_of_table hshapes4 exhaust4 inj4 gramM4 gramM_table4 _ 0 (by decide)
/-- Printed Sec. 5.1: f211 = h31. -/
theorem fExp4_211 : fBasis 4 (hshapes4 1) = ∑ l, (![0, 0, 0, 1, 0] : Fin 5 → ℤ) l • degreeHBasis 4 (hshapes4 l) :=
  f_of_table hshapes4 exhaust4 inj4 gramM4 gramM_table4 _ 1 (by decide)
/-- Printed Sec. 5.1: f22 = -h22 +2h4. -/
theorem fExp4_22 : fBasis 4 (hshapes4 2) = ∑ l, (![0, 0, (-1), 0, 2] : Fin 5 → ℤ) l • degreeHBasis 4 (hshapes4 l) :=
  f_of_table hshapes4 exhaust4 inj4 gramM4 gramM_table4 _ 2 (by decide)
/-- Printed Sec. 5.1: f31 = h211 -h31. -/
theorem fExp4_31 : fBasis 4 (hshapes4 3) = ∑ l, (![0, 1, 0, (-1), 0] : Fin 5 → ℤ) l • degreeHBasis 4 (hshapes4 l) :=
  f_of_table hshapes4 exhaust4 inj4 gramM4 gramM_table4 _ 3 (by decide)
/-- Printed Sec. 5.1: f4 = h1111 +2h22 -4h4. -/
theorem fExp4_4 : fBasis 4 (hshapes4 4) = ∑ l, (![1, 0, 2, 0, (-4)] : Fin 5 → ℤ) l • degreeHBasis 4 (hshapes4 l) :=
  f_of_table hshapes4 exhaust4 inj4 gramM4 gramM_table4 _ 4 (by decide)
/-- Printed Sec. 5.1 degree-4 odd Schur functions, row λ = coefficients of s_λ in the printed h-basis: s1111 = h1111 -h211 +h22 -h4; s211 = h211 -h22 -h31 +h4; s22 = h22 +h31 -2h4; s31 = h31 -h4; s4 = h4. -/
def printedSchur4 : Matrix (Fin 5) (Fin 5) ℤ := !![1, (-1), 1, 0, (-1);
    0, 1, (-1), (-1), 1;
    0, 0, 1, 1, (-2);
    0, 0, 0, 1, (-1);
    0, 0, 0, 0, 1]
/-- The printed odd Schur expansions invert the existing signed Kostka matrix (row-vector convention h_μ = Σ_λ K_(λμ) s_λ). -/
theorem schur_kostka_inverse4 : ∀ μ ν, ∑ l, TableauDominance.signedKostka (shapes4 l) (shapes4 μ) * printedSchur4 l ν = if μ = ν then 1 else 0 := by
  simp only [kostka_table4]; decide
/-- Hence, in the actual quotient: with the printed s_λ := Σ_ν S_(λν) h_ν, h_μ = Σ_λ signedKostka λ μ • s_λ. -/
theorem schur_relation4 (μ : Fin 5) : EKPartitionSpanning.hPartition (hshapes4 μ).val = ∑ l, TableauDominance.signedKostka (shapes4 l) (shapes4 μ) • ∑ ν, printedSchur4 l ν • EKPartitionSpanning.hPartition (hshapes4 ν).val :=
  kostka_inverse_relation (Matrix.of fun l μ => TableauDominance.signedKostka (shapes4 l) (shapes4 μ)) printedSchur4 (fun ν => EKPartitionSpanning.hPartition (hshapes4 ν).val) schur_kostka_inverse4 μ

def pl5 : Fin 7 → List ℕ := ![[1,1,1,1,1], [2,1,1,1], [2,2,1], [3,1,1], [3,2], [4,1], [5]]
theorem hs5 : ∀ j, (hshapes5 j).val.rowLens = pl5 j := by
  intro j; fin_cases j <;> exact YoungDiagram.rowLens_ofRowLens_eq_self (hw := by decide) (by decide)
/-- The printed degree-5 list is ALL shapes of degree 5. -/
theorem exhaust5 : ∀ ν, ∃ j, ν = hshapes5 j := exhaust hshapes5 pl5 hs5 (by decide +kernel)
theorem inj5 : Function.Injective hshapes5 := inj_of_rowLens hshapes5 pl5 hs5 (by decide)
/-- Printed Sec. 5.1 degree-5 odd Schur functions, row λ = coefficients of s_λ in the printed h-basis: s11111 = h11111 +h221 -h311 -2h41 +h5; s2111 = h2111 -h311 -h41 +h5; s221 = h221 +h311 -h32 -3h41 +2h5; s311 = h311 -h32 -h41 +h5; s32 = h32 +h41 -2h5; s41 = h41 -h5; s5 = h5. -/
def printedSchur5 : Matrix (Fin 7) (Fin 7) ℤ := !![1, 0, 1, (-1), 0, (-2), 1;
    0, 1, 0, (-1), 0, (-1), 1;
    0, 0, 1, 1, (-1), (-3), 2;
    0, 0, 0, 1, (-1), (-1), 1;
    0, 0, 0, 0, 1, 1, (-2);
    0, 0, 0, 0, 0, 1, (-1);
    0, 0, 0, 0, 0, 0, 1]
/-- The printed odd Schur expansions invert the existing signed Kostka matrix (row-vector convention h_μ = Σ_λ K_(λμ) s_λ). -/
theorem schur_kostka_inverse5 : ∀ μ ν, ∑ l, TableauDominance.signedKostka (shapes5 l) (shapes5 μ) * printedSchur5 l ν = if μ = ν then 1 else 0 := by
  simp only [kostka_table5]; decide
/-- Hence, in the actual quotient: with the printed s_λ := Σ_ν S_(λν) h_ν, h_μ = Σ_λ signedKostka λ μ • s_λ. -/
theorem schur_relation5 (μ : Fin 7) : EKPartitionSpanning.hPartition (hshapes5 μ).val = ∑ l, TableauDominance.signedKostka (shapes5 l) (shapes5 μ) • ∑ ν, printedSchur5 l ν • EKPartitionSpanning.hPartition (hshapes5 ν).val :=
  kostka_inverse_relation (Matrix.of fun l μ => TableauDominance.signedKostka (shapes5 l) (shapes5 μ)) printedSchur5 (fun ν => EKPartitionSpanning.hPartition (hshapes5 ν).val) schur_kostka_inverse5 μ

end OddMath.Frontier.EKAppendixData
