import OddMath.Frontier.TableauRowWord
import OddMath.Frontier.PlacticEvaluation
import OddMath.Frontier.PbwEquivalence

/-!
# Literal positive tableau evaluation

Ellis arXiv:1111.3932v1 §2.1 and §3.1: paper label k maps to
(-1)^(k-1) x_(k-1). Increasing PBW order uses only strict crossings.
-/
namespace OddMath.Frontier.TableauEvaluation

open TableauSign TableauRowWord
open OddMath.SkewPolynomial
open scoped BigOperators

variable {μ : YoungDiagram}

def InAlphabet (n : ℕ) (T : PositiveTableau μ) : Prop :=
  ∀ p ∈ μ.cells, T.entry p.1 p.2 ≤ n

theorem rowWord_bounds (n : ℕ) (T : PositiveTableau μ) (h : InAlphabet n T)
    {k : ℕ} (hk : k ∈ rowWord T) : 0 < k ∧ k ≤ n := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
  have hp' := (mem_rowCells μ p).mp hp
  exact ⟨T.positive (by simpa using hp'), h p hp'⟩

/-- Every actual letter is retained; the bound proves the Fin constructor. -/
noncomputable def rowFinWord (n : ℕ) (T : PositiveTableau μ) (h : InAlphabet n T) :
    List (Fin n) :=
  (rowWord T).attach.map fun k => ⟨k.val - 1, by
    have hk := rowWord_bounds n T h k.property
    omega⟩

noncomputable def rowPolynomial (n : ℕ) (T : PositiveTableau μ) (h : InAlphabet n T) :
    SkewPolynomial n := PlacticEvaluation.toSkew n (OddPlactic.word n (rowFinWord n T h))

noncomputable def exponents (n : ℕ) (T : PositiveTableau μ) (i : Fin n) : ℕ :=
  TableauContent.content T (i.val + 1)

noncomputable def tildeWeight (n : ℕ) (T : PositiveTableau μ) : ℕ :=
  ∑ i : Fin n, i.val * exponents n T i

/-- Ordered insertion crosses precisely the smaller letters of a sorted suffix. -/
theorem insertCrossings_eq_filter {n : ℕ} (i : Fin n) (w : List (Fin n))
    (hw : w.Sorted (· ≤ ·)) :
    PbwNormalization.insertCrossings i w = (w.filter (fun j => j < i)).length := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    have hs := List.pairwise_cons.mp hw
    by_cases hij : i ≤ j
    · have hf : w.filter (fun k => k < i) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro k hk
        simpa using not_lt_of_ge (hij.trans (hs.1 k hk))
      simp [PbwNormalization.insertCrossings, hij, not_lt_of_ge hij, hf]
    · have hji : j < i := lt_of_not_ge hij
      simp [PbwNormalization.insertCrossings, hij, hji, ih hs.2]

/-- Exact equality of two independently defined strict inversion statistics. -/
theorem sortCrossings_eq_inversions {n : ℕ} (w : List (Fin n)) :
    PbwNormalization.sortCrossings w = inversions (w.map Fin.val) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [PbwNormalization.sortCrossings, insertCrossings_eq_filter _ _
      (List.sorted_insertionSort (· ≤ ·) w), ih]
    have hc := ((List.perm_insertionSort (· ≤ ·) w).filter
      (fun j => j < i)).length_eq
    simp only [List.map_cons, inversions, List.filter_map, List.length_map]
    simpa only [Fin.lt_def, Function.comp_def, Nat.add_comm] using
      congrArg (fun k => inversions (w.map Fin.val) + k) hc

/-- Converting back to positive labels recovers the literal parent word. -/
theorem rowFinWord_labels (n : ℕ) (T : PositiveTableau μ) (h : InAlphabet n T) :
    (rowFinWord n T h).map (fun i => i.val + 1) = rowWord T := by
  unfold rowFinWord
  rw [List.map_map]
  have he : (fun k : {k // k ∈ rowWord T} => k.val - 1 + 1) = Subtype.val := by
    funext k
    have hk := rowWord_bounds n T h k.property
    omega
  simpa only [Function.comp_def, he, List.map_id] using
    (List.attach_map_val (l := rowWord T) (f := id))

theorem rowFinWord_count (n : ℕ) (T : PositiveTableau μ) (h : InAlphabet n T)
    (i : Fin n) : (rowFinWord n T h).count i = exponents n T i := by
  have hinj : Function.Injective (fun i : Fin n => i.val + 1) := by
    intro a b hab
    change a.val + 1 = b.val + 1 at hab
    apply Fin.ext
    omega
  rw [← List.count_map_of_injective _ _ hinj, rowFinWord_labels]
  exact rowWord_count T (i.val + 1)

/-- Adding one preserves strict order, including equality of repeated labels. -/
theorem inversions_map_succ (w : List ℕ) :
    inversions (w.map (· + 1)) = inversions w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp [inversions, List.filter_map, Function.comp_def, ih]

theorem rowFinWord_inversions (n : ℕ) (T : PositiveTableau μ) (h : InAlphabet n T) :
    inversions ((rowFinWord n T h).map Fin.val) = inversions (rowWord T) := by
  rw [← rowFinWord_labels n T h]
  simpa only [List.map_map, Function.comp_def] using
    (inversions_map_succ ((rowFinWord n T h).map Fin.val)).symm

/-- The sum of zero-based labels equals its multiplicity expansion. -/
theorem sum_vals_eq_counts {n : ℕ} (w : List (Fin n)) :
    (w.map Fin.val).sum = ∑ i : Fin n, i.val * w.count i := by
  induction w with
  | nil => simp
  | cons j w ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.count_cons]
    simp only [Nat.mul_add, Finset.sum_add_distrib]
    simp only [mul_ite, Nat.mul_one, Nat.mul_zero, beq_iff_eq,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact Nat.add_comm _ _

/-- Extract exactly the source tilde sign, before any normal ordering. -/
theorem tildeWord_eq {n : ℕ} (w : List (Fin n)) :
    (w.map PlacticEvaluation.tildeGenerator).prod =
      (-1 : ℤ) ^ (w.map Fin.val).sum • PbwL3.Phi n (PbwNormalization.word w) := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons,
      PbwNormalization.word_cons, map_mul, PbwL3.Phi_q, ih,
      PlacticEvaluation.tildeGenerator, smul_mul_assoc, mul_smul_comm, smul_smul,
      pow_add]
    rw [_root_.mul_comm ((-1 : ℤ) ^ (w.map Fin.val).sum)]

/-- Literal plactic evaluation of every finite word through actual PBW sorting. -/
theorem wordPolynomial_eq {n : ℕ} (w : List (Fin n)) :
    PlacticEvaluation.toSkew n (OddPlactic.word n w) =
      monomial (fun i => w.count i)
        ((-1 : ℤ) ^ (inversions (w.map Fin.val) + (w.map Fin.val).sum)) := by
  rw [PlacticEvaluation.toSkew_word, tildeWord_eq, PbwNormalization.word_normalize,
    map_zsmul, PbwEquivalence.Phi_orderedMonomial, smul_smul,
    ← pow_add, sortCrossings_eq_inversions]
  simp only [monomial, Finsupp.smul_single, smul_eq_mul, _root_.mul_one, Nat.add_comm]

/-- Actual row-word evaluation, with the source tilde normalization explicit. -/
theorem rowPolynomial_eq (n : ℕ) (T : PositiveTableau μ) (h : InAlphabet n T) :
    rowPolynomial n T h = monomial (exponents n T)
      ((-1 : ℤ) ^ (LrLegA.totalNorthLt (boxes T) (boxes T) + tildeWeight n T)) := by
  unfold rowPolynomial
  rw [wordPolynomial_eq, rowFinWord_inversions, rowWord_inversions, sum_vals_eq_counts]
  simp only [rowFinWord_count, tildeWeight]

theorem inAlphabet_of_mem (n : ℕ) (c : ℕ →₀ ℕ)
    (hc : ∀ k ∈ c.support, k ≤ n) (T : PositiveTableau μ)
    (hT : T ∈ TableauContent.tableauxOfContent μ c) : InAlphabet n T := by
  intro p hp
  apply hc
  rw [← (TableauContent.mem_tableauxOfContent T c).mp hT]
  exact TableauContent.entry_mem_support T hp

/-- Literal finite sum over the exact fixed-content tableau fiber. -/
noncomputable def contentPolynomial (n : ℕ) (μ : YoungDiagram) (c : ℕ →₀ ℕ)
    (hc : ∀ k ∈ c.support, k ≤ n) : SkewPolynomial n :=
  ∑ T ∈ (TableauContent.tableauxOfContent μ c).attach,
    rowPolynomial n T.val (inAlphabet_of_mem n c hc T.val T.property)

/-- The fixed-content coefficient is the untilded sign sum TIMES its tilde factor.
The statement is stronger than requiring c 0 = 0: unrealizable fibers are empty. -/
theorem contentPolynomial_eq (n : ℕ) (μ : YoungDiagram) (c : ℕ →₀ ℕ)
    (hc : ∀ k ∈ c.support, k ≤ n) :
    contentPolynomial n μ c hc = monomial (fun i : Fin n => c (i.val + 1))
      (((-1 : ℤ) ^ (∑ i : Fin n, i.val * c (i.val + 1))) *
        ∑ T ∈ TableauContent.tableauxOfContent μ c,
          (-1 : ℤ) ^ LrLegA.totalNorthLt (boxes T) (boxes T)) := by
  classical
  unfold contentPolynomial
  have he (T : {T // T ∈ TableauContent.tableauxOfContent μ c}) :
      exponents n T.val = (fun i : Fin n => c (i.val + 1)) := by
    funext i
    exact congrArg (fun d : ℕ →₀ ℕ => d (i.val + 1))
      ((TableauContent.mem_tableauxOfContent T.val c).mp T.property)
  simp only [rowPolynomial_eq, tildeWeight, he, pow_add]
  rw [← Finset.sum_attach (TableauContent.tableauxOfContent μ c)
    (fun T => (-1 : ℤ) ^ LrLegA.totalNorthLt (boxes T) (boxes T))]
  rw [Finset.mul_sum]
  simp only [mul_comm ((-1 : ℤ) ^ (∑ i : Fin n, i.val * c (i.val + 1)))]
  exact (Finsupp.single_finset_sum _ _ _).symm

end OddMath.Frontier.TableauEvaluation
