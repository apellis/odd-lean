import OddMath.Frontier.TableauBumpMonotone

/-!
Chronological insertion of arbitrary words into genuine bounded positive tableaux.
Fulton, Young Tableaux §1.1, proposition printed p.11 (frozen PDF p.23):
the forward horizontal-strip assertion follows from the Row Bumping Lemma.
English zero-based cells; Fin n letter a denotes positive entry a.val + 1.
No reverse insertion, reconstruction, or sign assertion is made here.
-/
namespace OddMath.Frontier.TableauWordInsertion
open OddMath.Frontier OddMath.Frontier.TableauSign OddMath.Frontier.TableauEvaluation

abbrev State (n : ℕ) := Σ μ : YoungDiagram, {T : PositiveTableau μ // InAlphabet n T}
noncomputable def run (n : ℕ) : State n → List (Fin n) → State n × List (ℕ × ℕ)
  | S, [] => (S, [])
  | S, a :: w =>
    let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
    let R := run n ⟨I.shape, ⟨I.tableau, I.bounded⟩⟩ w
    (R.1, I.newCell :: R.2)
def spec (n : ℕ) (S : State n) (w : List (Fin n)) : Prop :=
  let R := run n S w
  R.2.length = w.length ∧ R.2.Nodup ∧ S.1.cells ⊆ R.1.1.cells ∧
    R.2.toFinset = R.1.1.cells \ S.1.cells
def horizontal (n : ℕ) (S : State n) (w : List (Fin n)) : Prop :=
  w.Sorted (· ≤ ·) →
  let R := run n S w
  R.2.Pairwise (fun p q => p.2 < q.2) ∧
    (∀ p ∈ R.1.1.cells \ S.1.cells, ∀ q ∈ R.1.1.cells \ S.1.cells,
      p.2 = q.2 → p = q)

theorem run_spec (n : ℕ) (S : State n) (w : List (Fin n)) : spec n S w := by
  induction w generalizing S with
  | nil => simp [spec, run]
  | cons a w ih =>
    let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
    let S' : State n := ⟨I.shape, ⟨I.tableau, I.bounded⟩⟩
    let R := run n S' w
    have hi := TableauInsertion.insert_cells n S.1 S.2.1 S.2.2 a
    change I.newCell ∉ S.1.cells ∧
      I.shape.cells = TableauInsertion.insertCell I.newCell S.1.cells at hi
    have ht := ih S'
    change R.2.length = w.length ∧ R.2.Nodup ∧
      I.shape.cells ⊆ R.1.1.cells ∧ R.2.toFinset = R.1.1.cells \ I.shape.cells at ht
    have hnew : I.newCell ∈ I.shape.cells := by
      rw [hi.2]; exact Finset.mem_insert_self _ _
    have hold : S.1.cells ⊆ I.shape.cells := by
      rw [hi.2]; exact Finset.subset_insert _ _
    have hfresh : I.newCell ∉ R.2 := by
      intro h
      have hh : I.newCell ∈ R.2.toFinset := List.mem_toFinset.mpr h
      rw [ht.2.2.2] at hh
      exact (Finset.mem_sdiff.mp hh).2 hnew
    change (I.newCell :: R.2).length = (a :: w).length ∧
      (I.newCell :: R.2).Nodup ∧ S.1.cells ⊆ R.1.1.cells ∧
      (I.newCell :: R.2).toFinset = R.1.1.cells \ S.1.cells
    refine ⟨by simpa using ht.1, List.nodup_cons.mpr ⟨hfresh, ht.2.1⟩,
      Finset.Subset.trans hold ht.2.2.1, ?_⟩
    ext p
    have hinc := ht.2.2.1 hnew
    simp only [List.toFinset_cons, Finset.mem_insert, ht.2.2.2, Finset.mem_sdiff]
    rw [hi.2]
    simp only [TableauInsertion.insertCell, Finset.mem_insert]
    constructor
    · rintro (rfl | ⟨hp, hn⟩)
      · exact ⟨hinc, hi.1⟩
      · exact ⟨hp, fun ho => hn (Or.inr ho)⟩
    · rintro ⟨hp, hn⟩
      by_cases he : p = I.newCell
      · exact Or.inl he
      · exact Or.inr ⟨hp, fun h => h.elim he hn⟩

private theorem run_columns (n : ℕ) (S : State n) (w : List (Fin n))
    (hw : w.Sorted (· ≤ ·)) :
    (run n S w).2.Pairwise (fun p q => p.2 < q.2) := by
  induction w generalizing S with
  | nil => simp [run]
  | cons a w ih =>
    let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
    let S' : State n := ⟨I.shape, ⟨I.tableau, I.bounded⟩⟩
    have hs := List.pairwise_cons.mp hw
    have ht := ih S' hs.2
    change (I.newCell :: (run n S' w).2).Pairwise (fun p q => p.2 < q.2)
    apply List.pairwise_cons.mpr
    refine ⟨?_, ht⟩
    cases w with
    | nil => simp [run]
    | cons b v =>
      let J := TableauInsertion.insert n S'.1 S'.2.1 S'.2.2 b
      let S'' : State n := ⟨J.shape, ⟨J.tableau, J.bounded⟩⟩
      have hab : a ≤ b := hs.1 b (by simp)
      have hij : I.newCell.2 < J.newCell.2 :=
        (TableauBumpMonotone.insert_pair_le n S.1 S.2.1 S.2.2 a b hab).2.2.1
      change (J.newCell :: (run n S'' v).2).Pairwise (fun p q => p.2 < q.2) at ht
      intro p hp
      change p ∈ J.newCell :: (run n S'' v).2 at hp
      rcases List.mem_cons.mp hp with he | hm
      · subst p; exact hij
      · exact lt_trans hij ((List.pairwise_cons.mp ht).1 p hm)

private theorem columns_injective (ps : List (ℕ × ℕ))
    (hs : ps.Pairwise (fun p q => p.2 < q.2)) :
    ∀ p ∈ ps, ∀ q ∈ ps, p.2 = q.2 → p = q := by
  induction ps with
  | nil => simp
  | cons a ps ih =>
    have hh := List.pairwise_cons.mp hs
    intro p hp q hq he
    rcases List.mem_cons.mp hp with hp_eq | hp_tail
    · subst p
      rcases List.mem_cons.mp hq with hq_eq | hq_tail
      · exact hq_eq.symm
      · have := hh.1 q hq_tail; omega
    · rcases List.mem_cons.mp hq with hq_eq | hq_tail
      · subst q
        have := hh.1 p hp_tail; omega
      · exact ih hh.2 p hp_tail q hq_tail he

theorem run_horizontal (n : ℕ) (S : State n) (w : List (Fin n)) :
    horizontal n S w := by
  intro hw
  have hc := run_columns n S w hw
  refine ⟨hc, ?_⟩
  intro p hp q hq he
  have hx := (run_spec n S w).2.2.2
  rw [← hx] at hp hq
  exact columns_injective _ hc p (List.mem_toFinset.mp hp) q (List.mem_toFinset.mp hq) he

#print axioms State
#print axioms run
#print axioms spec
#print axioms horizontal
#print axioms run_spec
#print axioms run_columns
#print axioms columns_injective
#print axioms run_horizontal
end OddMath.Frontier.TableauWordInsertion
