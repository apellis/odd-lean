import OddMath.Frontier.TableauSign
import Mathlib.Data.Finsupp.Multiset

/-!
# Exact finite fixed-content positive semistandard tableaux

Ellis arXiv:1111.3932v1 §2.1 defines content by multiplicities of positive
labels; Theorem 3.8 compares the two box-count signs. We construct the
actual finite domain for that comparison, not a reading word or a Schur
function. Finiteness uses functions from actual cells to content support.
-/

namespace OddMath.Frontier.TableauContent

open TableauSign
open scoped BigOperators

variable {μ : YoungDiagram}

/-- One singleton contribution per actual cell, with no ordering choice. -/
noncomputable def content (T : PositiveTableau μ) : ℕ →₀ ℕ :=
  ∑ p ∈ μ.cells, Finsupp.single (T.entry p.1 p.2) 1

/-- Content counts exactly the cells carrying the specified label. -/
theorem content_apply (T : PositiveTableau μ) (k : ℕ) :
    content T k = (μ.cells.filter (fun p => T.entry p.1 p.2 = k)).card := by
  classical
  simp only [content, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.card_filter]

/-- Positivity excludes label zero. -/
@[simp] theorem content_zero (T : PositiveTableau μ) : content T 0 = 0 := by
  classical
  rw [content_apply]
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro p hp
  exact Nat.ne_of_gt (T.positive (by simpa using hp))

/-- Every cell contributes exactly one to the total multiplicity. -/
theorem content_total (T : PositiveTableau μ) :
    (content T).sum (fun _ n => n) = μ.card := by
  classical
  rw [content, ← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp only [Finsupp.sum_single_index (h := fun _ n : ℕ => n) rfl, Finset.sum_const, smul_eq_mul,
    mul_one, YoungDiagram.card]

/-- The label of each actual cell is in the content support. -/
theorem entry_mem_support (T : PositiveTableau μ) {p : ℕ × ℕ}
    (hp : p ∈ μ.cells) : T.entry p.1 p.2 ∈ (content T).support := by
  classical
  rw [Finsupp.mem_support_iff, content_apply]
  exact Finset.card_ne_zero.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩

/-- A positive tableau is determined by its entries on its finite shape. -/
theorem ext_cells {S T : PositiveTableau μ}
    (h : ∀ p ∈ μ.cells, S.entry p.1 p.2 = T.entry p.1 p.2) : S = T := by
  have he : S.toSemistandardYoungTableau = T.toSemistandardYoungTableau := by
    apply SemistandardYoungTableau.ext
    intro i j
    by_cases hp : (i, j) ∈ μ
    · exact h (i, j) (by simpa using hp)
    · exact (S.zeros' hp).trans (T.zeros' hp).symm
  cases S
  cases T
  cases he
  rfl

/-- Encode a fixed-content tableau by a function between finite types. -/
noncomputable def contentEncoding (c : ℕ →₀ ℕ)
    (T : {T : PositiveTableau μ // content T = c}) :
    μ.cells → c.support := fun p =>
  ⟨T.val.entry p.val.1 p.val.2, by
    simpa only [T.property] using entry_mem_support T.val p.property⟩

theorem contentEncoding_injective (c : ℕ →₀ ℕ) :
    Function.Injective (contentEncoding (μ := μ) c) := by
  intro S T h
  apply Subtype.ext
  apply ext_cells
  intro p hp
  exact congrArg Subtype.val (congrFun h ⟨p, hp⟩)

/-- Finiteness is proved only for the content fiber, never assumed globally. -/
theorem finite_content (μ : YoungDiagram) (c : ℕ →₀ ℕ) :
    Set.Finite {T : PositiveTableau μ | content T = c} := by
  haveI : Finite {T : PositiveTableau μ // content T = c} :=
    Finite.of_injective (contentEncoding c) (contentEncoding_injective c)
  exact Set.finite_coe_iff.mp (show Finite {T : PositiveTableau μ // content T = c}
    from inferInstance)

/-- The exact finite set of all positive SSYT of shape μ and content c. -/
noncomputable def tableauxOfContent (μ : YoungDiagram) (c : ℕ →₀ ℕ) :
    Finset (PositiveTableau μ) := (finite_content μ c).toFinset

@[simp] theorem mem_tableauxOfContent (T : PositiveTableau μ) (c : ℕ →₀ ℕ) :
    T ∈ tableauxOfContent μ c ↔ content T = c := by
  classical
  simp [tableauxOfContent]

/-- Positive tableaux never realize a content with a nonzero zero-label count. -/
theorem tableauxOfContent_eq_empty_of_zero_ne (μ : YoungDiagram) (c : ℕ →₀ ℕ)
    (hc : c 0 ≠ 0) : tableauxOfContent μ c = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro T hT
  have h := (mem_tableauxOfContent T c).mp hT
  exact hc (h ▸ content_zero T)

/-- Incorrect total multiplicity also gives the empty domain. -/
theorem tableauxOfContent_eq_empty_of_total_ne (μ : YoungDiagram) (c : ℕ →₀ ℕ)
    (hc : c.sum (fun _ n => n) ≠ μ.card) : tableauxOfContent μ c = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro T hT
  have h := (mem_tableauxOfContent T c).mp hT
  exact hc (h ▸ content_total T)

/-- Every tableau belongs to the fiber of its own actual content. -/
theorem mem_own_content (T : PositiveTableau μ) : T ∈ tableauxOfContent μ (content T) :=
  (mem_tableauxOfContent T (content T)).mpr rfl

/-- The empty shape has the unique empty filling, including zeros off-shape. -/
def emptyTableau : PositiveTableau ⊥ where
  entry _ _ := 0
  row_weak' _ h := (YoungDiagram.not_mem_bot _ h).elim
  col_strict' _ h := (YoungDiagram.not_mem_bot _ h).elim
  zeros' _ := rfl
  positive h := (YoungDiagram.not_mem_bot _ h).elim

@[simp] theorem content_empty (T : PositiveTableau ⊥) : content T = 0 := by
  classical
  simp only [content, YoungDiagram.cells_bot, Finset.sum_empty]

/-- Empty content on empty shape contains one tableau, not zero tableaux. -/
theorem tableauxOfContent_empty_zero :
    tableauxOfContent ⊥ 0 = {emptyTableau} := by
  classical
  ext T
  simp only [mem_tableauxOfContent, content_empty, Finset.mem_singleton, true_iff]
  apply ext_cells
  simp only [YoungDiagram.cells_bot, Finset.not_mem_empty, false_implies, implies_true]

/-- Nonzero content cannot be realized on the empty shape. -/
theorem tableauxOfContent_empty_ne_zero (c : ℕ →₀ ℕ) (hc : c ≠ 0) :
    tableauxOfContent ⊥ c = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro T hT
  exact hc ((mem_tableauxOfContent T c).mp hT |>.symm.trans (content_empty T))

/-- Empty content cannot fill any shape with a positive number of cells. -/
theorem tableauxOfContent_zero_of_card_ne_zero (μ : YoungDiagram) (hμ : μ.card ≠ 0) :
    tableauxOfContent μ 0 = ∅ := by
  apply tableauxOfContent_eq_empty_of_total_ne
  simpa only [Finsupp.sum_zero_index] using Ne.symm hμ

/-- Leg A aggregated over the actual, exact fixed-content tableau domain. -/
theorem signed_content_sum (μ : YoungDiagram) (c : ℕ →₀ ℕ) :
    (∑ T ∈ tableauxOfContent μ c, LrLegA.signLeft (boxes T) (boxes T)) =
      ∑ T ∈ tableauxOfContent μ c, LrLegA.signRight (boxes T) (boxes T) := by
  apply Finset.sum_congr rfl
  intro T _
  exact TableauSign.global_sign T

end OddMath.Frontier.TableauContent
