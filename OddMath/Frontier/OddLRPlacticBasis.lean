import OddMath.Frontier.EKClassicalPlactic
import OddMath.Frontier.TableauStripSigns

/-!
# The tableau basis of the odd plactic ring

Ellis, *The odd Littlewood–Richardson rule*, arXiv:1111.3932v1 ("E"), §3.1, p. 8, sentence
after Theorem 3.1: "Thus the set of all Young tableaux with entries in A forms a basis of ZPl."

Carrier: `OddPlactic.Plactic n` (E (3.1), alphabet `Fin n`, paper letter = Lean letter + 1).
Tableaux with entries at most n are the insertion states `TableauWordInsertion.State n`;
the tableau `T` is sent to its row word `w_r(T)` (E (3.2)).

* `tableauBasis`: the row words `w_r(T)` form a ℤ-basis of ℤPl_n.
* `word_eq`: every word equals `± w_r(P(w))`, the sign being the sign of the
  chronological insertion (`TableauStripSigns.crossings`); `word_eq_inversions` identifies it
  with `(-1)^{N^<(w) + N^<(w_r(P(w)))}` (inversion numbers, E §2.2).

Spanning is Theorem 3.1 with signs (`TableauStripSigns.run_word`). Independence: the row
insertion of a letter, with the insertion sign, is a ℤ-linear operator on the free module
over tableaux; these operators satisfy the signed relations (K′), (K″), because insertion is
Knuth invariant (`EKClassicalPlactic.theorem_4_1_insertion`) and each elementary Knuth
transformation changes the sign.  The induced right module structure sends `w_r(T)` to `T`.
-/

namespace OddMath.Frontier.OddLRPlactic

open TableauSign TableauEvaluation EKClassicalPlactic

noncomputable section

/-- Tableaux with entries in `{1, …, n}`, with their shapes. -/
abbrev State (n : ℕ) := TableauWordInsertion.State n

/-- The row word `w_r(T)` as a word in `Fin n`. -/
abbrev rw {n : ℕ} (S : State n) : List (Fin n) := rowFinWord n S.2.1 S.2.2

/-- E (3.2): the image `w_r(T)` of a tableau in ℤPl_n. -/
def tabWord (n : ℕ) (S : State n) : OddPlactic.Plactic n := OddPlactic.word n (rw S)

/-- The empty tableau. -/
abbrev empty (n : ℕ) : State n := emptyState n

/-- The insertion tableau `P(w)` of a word, i.e. `∅ ← w`. -/
abbrev P {n : ℕ} (w : List (Fin n)) : State n := (TableauWordInsertion.run n (empty n) w).1

/-- The sign of the chronological insertion `∅ ← w`. -/
abbrev insSign {n : ℕ} (S : State n) (w : List (Fin n)) : ℤ :=
  (-1 : ℤ) ^ TableauStripSigns.crossings n S w

theorem rw_empty (n : ℕ) : rw (empty n) = [] := by
  simp [rw, rowFinWord, TableauRowWord.rowWord, TableauRowWord.rowCells, empty, emptyState]

theorem tabWord_empty (n : ℕ) : tabWord n (empty n) = 1 := by
  simp [tabWord, rw_empty]

/-! ## Signed normal form (spanning) -/

/-- Insertion into `T` with sign: `w_r(T) w = ± w_r(T ← w)` in ℤPl_n. -/
theorem word_rw_append {n : ℕ} (S : State n) (w : List (Fin n)) :
    OddPlactic.word n (rw S ++ w) =
      insSign S w • tabWord n (TableauWordInsertion.run n S w).1 :=
  TableauStripSigns.run_word n S w

/-- E Theorem 3.1 with signs: `w = ± w_r(P(w))` in ℤPl_n. -/
theorem word_eq {n : ℕ} (w : List (Fin n)) :
    OddPlactic.word n w = insSign (empty n) w • tabWord n (P w) := by
  have h := word_rw_append (empty n) w
  rwa [rw_empty, List.nil_append] at h

/-- A unit multiple of a word determines the unit. -/
theorem sign_cancel {n : ℕ} (w : List (Fin n)) {a b : ℤ}
    (h : a • OddPlactic.word n w = b • OddPlactic.word n w) : a = b := by
  have h' := congrArg (PlacticEvaluation.toSkew n) h
  simp only [map_zsmul, wordPolynomial_eq, OddMath.SkewPolynomial.monomial, Finsupp.smul_single, smul_eq_mul] at h'
  have h'' := Finsupp.single_injective _ h'
  have hne : ((-1 : ℤ) ^ (TableauRowWord.inversions (w.map Fin.val) + (w.map Fin.val).sum)) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  exact mul_right_cancel₀ hne h''

/-! ## Knuth invariance of insertion -/

/-- A state is determined by its underlying shape and tableau. -/
theorem state_ext {n : ℕ} {S S' : State n}
    (h : (⟨S.1, S.2.1⟩ : Σ μ : YoungDiagram, PositiveTableau μ) = ⟨S'.1, S'.2.1⟩) : S = S' := by
  obtain ⟨μ, T, hT⟩ := S
  obtain ⟨μ', T', hT'⟩ := S'
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  cases eq_of_heq h
  rfl

theorem rw_labels {n : ℕ} (S : State n) : (rw S).map lab = TableauRowWord.rowWord S.2.1 :=
  rowFinWord_labels n S.2.1 S.2.2

/-- `P` is constant on Knuth classes. -/
theorem P_eq_of_knuth {n : ℕ} {u v : List (Fin n)} (h : KnuthEquiv (u.map lab) (v.map lab)) :
    P u = P v := by
  apply state_ext
  obtain ⟨hex, -⟩ := theorem_4_1_insertion n u
  obtain ⟨-, huniq⟩ := theorem_4_1_insertion n v
  exact huniq _ (knuth_trans (knuth_symm h) hex)

/-- Inserting the row word of `T` into `∅` returns `T` (E, after Theorem 3.1). -/
theorem P_rw {n : ℕ} (S : State n) : P (rw S) = S := by
  apply state_ext
  obtain ⟨-, huniq⟩ := theorem_4_1_insertion n (rw S)
  refine (huniq ⟨S.1, S.2.1⟩ ?_).symm
  rw [rw_labels]
  exact knuth_refl _

theorem run_append {n : ℕ} (S : State n) (u v : List (Fin n)) :
    (TableauWordInsertion.run n S (u ++ v)).1 =
      (TableauWordInsertion.run n (TableauWordInsertion.run n S u).1 v).1 := by
  induction u generalizing S with
  | nil => rfl
  | cons a u ih => exact ih _

/-- Insertion of Knuth-equivalent words into the same tableau agrees. -/
theorem run_eq_of_knuth {n : ℕ} (S : State n) {u v : List (Fin n)}
    (h : KnuthEquiv (u.map lab) (v.map lab)) :
    (TableauWordInsertion.run n S u).1 = (TableauWordInsertion.run n S v).1 := by
  have hS : (TableauWordInsertion.run n (empty n) (rw S)).1 = S := P_rw S
  have e1 := run_append (empty n) (rw S) u
  have e2 := run_append (empty n) (rw S) v
  rw [hS] at e1 e2
  rw [← e1, ← e2]
  apply P_eq_of_knuth
  simpa only [List.map_append, List.append_nil] using knuth_context h ((rw S).map lab) []

theorem knuth_left_step {n : ℕ} {x y z : Fin n} (hxy : x < y) (hyz : y ≤ z) :
    KnuthEquiv ([y, z, x].map lab) ([y, x, z].map lab) := by
  simpa using knuth_K1 (lab_lt.mpr hxy) (lab_le.mpr hyz) [] []

theorem knuth_right_step {n : ℕ} {x y z : Fin n} (hxy : x ≤ y) (hyz : y < z) :
    KnuthEquiv ([x, z, y].map lab) ([z, x, y].map lab) := by
  simpa using knuth_K2 (lab_le.mpr hxy) (lab_lt.mpr hyz) [] []

/-- An elementary Knuth transformation flips the insertion sign. -/
theorem insSign_knuth {n : ℕ} (S : State n) {u v : List (Fin n)}
    (hk : KnuthEquiv (u.map lab) (v.map lab))
    (hw : OddPlactic.word n (rw S ++ u) = -OddPlactic.word n (rw S ++ v)) :
    insSign S u = -insSign S v := by
  rw [word_rw_append, word_rw_append, run_eq_of_knuth S hk, ← neg_smul] at hw
  exact sign_cancel _ hw

/-! ## The insertion representation (independence) -/

/-- Free module on tableaux. -/
abbrev Free (n : ℕ) := State n →₀ ℤ

/-- Right insertion of one letter, with its sign, as an operator on the free module. -/
def insOp {n : ℕ} (a : Fin n) : Module.End ℤ (Free n) :=
  Finsupp.linearCombination ℤ fun S =>
    insSign S [a] • Finsupp.single (TableauWordInsertion.run n S [a]).1 (1 : ℤ)

theorem insOp_single {n : ℕ} (a : Fin n) (S : State n) :
    insOp a (Finsupp.single S 1) =
      insSign S [a] • Finsupp.single (TableauWordInsertion.run n S [a]).1 (1 : ℤ) := by
  simp [insOp]

/-- The letters act by `op ∘ insOp` in the opposite ring (right action). -/
def insLetter {n : ℕ} (a : Fin n) : (Module.End ℤ (Free n))ᵐᵒᵖ := MulOpposite.op (insOp a)

/-- A word acts on a basis vector by insertion with its sign. -/
theorem prod_insLetter {n : ℕ} (w : List (Fin n)) (S : State n) :
    ((w.map insLetter).prod).unop (Finsupp.single S 1) =
      insSign S w • Finsupp.single (TableauWordInsertion.run n S w).1 (1 : ℤ) := by
  induction w generalizing S with
  | nil => simp [TableauWordInsertion.run, TableauStripSigns.crossings]
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, MulOpposite.unop_mul, Module.End.mul_apply, insLetter,
      MulOpposite.unop_op, insOp_single, map_zsmul, ih, smul_smul, ← pow_add]
    rfl

theorem prod_three {M : Type*} [Monoid M] (a b c : M) : [a, b, c].prod = a * b * c := by
  simp [mul_assoc]

theorem insLetter_respects (n : ℕ) : OddPlactic.RespectsKnuth (insLetter (n := n)) := by
  have key : ∀ u v : List (Fin n), KnuthEquiv (u.map lab) (v.map lab) →
      (∀ S : State n, OddPlactic.word n (rw S ++ u) = -OddPlactic.word n (rw S ++ v)) →
      (u.map insLetter).prod = -(v.map insLetter).prod := by
    intro u v hk hw
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_neg]
    apply Finsupp.lhom_ext
    intro S b
    rw [← Finsupp.smul_single_one, map_zsmul, map_zsmul, LinearMap.neg_apply,
      prod_insLetter, prod_insLetter, insSign_knuth S hk (hw S), run_eq_of_knuth S hk,
      neg_smul, smul_neg]
  constructor
  · intro x y z hxy hyz
    have h := key [y, z, x] [y, x, z] (knuth_left_step hxy hyz) (fun S => by
      simpa using OddPlactic.word_knuth_left n (rw S) [] x y z hxy hyz)
    simpa only [List.map_cons, List.map_nil, prod_three] using h
  · intro x y z hxy hyz
    have h := key [x, z, y] [z, x, y] (knuth_right_step hxy hyz) (fun S => by
      simpa using OddPlactic.word_knuth_right n (rw S) [] x y z hxy hyz)
    simpa only [List.map_cons, List.map_nil, prod_three] using h

/-- ℤPl_n acting on the free module over tableaux (in the opposite ring). -/
def rep (n : ℕ) : OddPlactic.Plactic n →+* (Module.End ℤ (Free n))ᵐᵒᵖ :=
  OddPlactic.lift insLetter (insLetter_respects n)

/-- Coordinates of an element: act on the empty tableau. -/
def coord (n : ℕ) : OddPlactic.Plactic n →ₗ[ℤ] Free n :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => (rep n x).unop (Finsupp.single (empty n) 1)
      map_zero' := by simp
      map_add' := fun x y => by simp }

theorem coord_word {n : ℕ} (w : List (Fin n)) :
    coord n (OddPlactic.word n w) = insSign (empty n) w • Finsupp.single (P w) (1 : ℤ) := by
  change (rep n (OddPlactic.word n w)).unop _ = _
  rw [rep, OddPlactic.lift_word, prod_insLetter]

/-- The row word of `T` inserts into `∅` with sign `+1`. -/
theorem insSign_rw {n : ℕ} (S : State n) : insSign (empty n) (rw S) = 1 := by
  have h := word_eq (rw S)
  rw [P_rw, tabWord] at h
  exact (sign_cancel (rw S) (by rw [one_smul]; exact h)).symm

theorem coord_tabWord {n : ℕ} (S : State n) :
    coord n (tabWord n S) = Finsupp.single S (1 : ℤ) := by
  rw [tabWord, coord_word, insSign_rw, P_rw, one_smul]

theorem tabWord_linearIndependent (n : ℕ) : LinearIndependent ℤ (tabWord n) := by
  apply LinearIndependent.of_comp (coord n)
  have he : (coord n) ∘ (tabWord n) = (Finsupp.basisSingleOne : Basis (State n) ℤ (Free n)) := by
    funext S
    rw [Function.comp_apply, coord_tabWord, Finsupp.coe_basisSingleOne]
  rw [he]
  exact Basis.linearIndependent _

/-! ## Spanning -/

theorem word_mem_span {n : ℕ} (w : List (Fin n)) :
    OddPlactic.word n w ∈ Submodule.span ℤ (Set.range (tabWord n)) := by
  rw [word_eq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem mul_word_mem_span {n : ℕ} {x : OddPlactic.Plactic n}
    (hx : x ∈ Submodule.span ℤ (Set.range (tabWord n))) (w : List (Fin n)) :
    x * OddPlactic.word n w ∈ Submodule.span ℤ (Set.range (tabWord n)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, rfl⟩ := hx
    rw [tabWord, ← OddPlactic.word_append]
    exact word_mem_span _
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem mul_mem_span {n : ℕ} {x y : OddPlactic.Plactic n}
    (hx : x ∈ Submodule.span ℤ (Set.range (tabWord n)))
    (hy : y ∈ Submodule.span ℤ (Set.range (tabWord n))) :
    x * y ∈ Submodule.span ℤ (Set.range (tabWord n)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨S, rfl⟩ := hy
    exact mul_word_mem_span hx _
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy

theorem quotientMap_mem_span {n : ℕ} (p : FreeAlgebra ℤ (Fin n)) :
    OddPlactic.quotientMap n p ∈ Submodule.span ℤ (Set.range (tabWord n)) := by
  induction p using FreeAlgebra.induction with
  | grade0 r =>
    have h : OddPlactic.quotientMap n (algebraMap ℤ _ r) = r • tabWord n (empty n) := by
      simp [tabWord_empty]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  | grade1 i =>
    have h := word_mem_span [i]
    simpa [OddPlactic.q] using h
  | mul a b ha hb => rw [map_mul]; exact mul_mem_span ha hb
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

theorem span_tabWord (n : ℕ) : Submodule.span ℤ (Set.range (tabWord n)) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := OddPlactic.relIdeal n) x
  exact quotientMap_mem_span p

/-! ## The basis -/

/-- **E §3.1, p. 8** (after Theorem 3.1): the row words `w_r(T)` of the semistandard tableaux
`T` with entries in `{1, …, n}` form a ℤ-basis of the odd plactic ring ℤPl_n. -/
def tableauBasis (n : ℕ) : Basis (State n) ℤ (OddPlactic.Plactic n) :=
  Basis.mk (tabWord_linearIndependent n) (span_tabWord n).ge

@[simp] theorem tableauBasis_apply {n : ℕ} (S : State n) : tableauBasis n S = tabWord n S :=
  Basis.mk_apply _ _ _

/-- The coordinates in the tableau basis are computed by insertion. -/
theorem tableauBasis_repr (n : ℕ) : (tableauBasis n).repr.toLinearMap = coord n := by
  apply (tableauBasis n).ext
  intro S
  rw [LinearEquiv.coe_coe, Basis.repr_self, tableauBasis_apply, coord_tabWord]

theorem repr_word {n : ℕ} (w : List (Fin n)) :
    (tableauBasis n).repr (OddPlactic.word n w) = Finsupp.single (P w) (insSign (empty n) w) := by
  have h := LinearMap.congr_fun (tableauBasis_repr n) (OddPlactic.word n w)
  rw [LinearEquiv.coe_coe] at h
  rw [h, coord_word, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- `x̃^w = ± x̃^{w_r(P(w))}` in `OPol_n`, with the same sign as in ℤPl_n. -/
theorem toSkew_word_eq {n : ℕ} (w : List (Fin n)) :
    PlacticEvaluation.toSkew n (OddPlactic.word n w) =
      insSign (empty n) w • PlacticEvaluation.toSkew n (tabWord n (P w)) := by
  rw [word_eq w, map_zsmul]

/-- The sign of `w = ± w_r(P(w))` is `(-1)^{N^<(w) + N^<(w_r(P(w)))}`, the product of the
inversion signs of the two words (E §2.2, `sign(T) = (-1)^{N^<(T)}`). -/
theorem insSign_eq_inversions {n : ℕ} (w : List (Fin n)) :
    insSign (empty n) w = (-1 : ℤ) ^ (TableauRowWord.inversions (w.map Fin.val) +
      TableauRowWord.inversions ((rw (P w)).map Fin.val)) := by
  have h := toSkew_word_eq w
  rw [tabWord, wordPolynomial_eq, wordPolynomial_eq] at h
  simp only [OddMath.SkewPolynomial.monomial, Finsupp.smul_single, smul_eq_mul] at h
  obtain ⟨he, hc⟩ := (Finsupp.single_eq_single_iff _ _ _ _).mp h |>.resolve_right (by
    rintro ⟨h1, -⟩
    exact absurd h1 (pow_ne_zero _ (by norm_num)))
  have hs : (w.map Fin.val).sum = ((rw (P w)).map Fin.val).sum := by
    rw [sum_vals_eq_counts, sum_vals_eq_counts]
    exact Finset.sum_congr rfl (fun i _ => by rw [congrFun he i])
  rw [hs] at hc
  have hu : ∀ k : ℕ, ((-1 : ℤ) ^ k) * ((-1 : ℤ) ^ k) = 1 := fun k => by
    rw [← mul_pow]; norm_num
  calc insSign (empty n) w
      = insSign (empty n) w * ((-1 : ℤ) ^ (TableauRowWord.inversions ((rw (P w)).map Fin.val) +
          ((rw (P w)).map Fin.val).sum)) *
          ((-1 : ℤ) ^ (TableauRowWord.inversions ((rw (P w)).map Fin.val) +
          ((rw (P w)).map Fin.val).sum)) := by rw [mul_assoc, hu, mul_one]
    _ = _ := by
      rw [← hc, pow_add, pow_add, pow_add]
      have := hu (((rw (P w)).map Fin.val).sum)
      calc _ = (-1 : ℤ) ^ TableauRowWord.inversions (w.map Fin.val) *
            (-1) ^ TableauRowWord.inversions ((rw (P w)).map Fin.val) *
            ((-1) ^ ((rw (P w)).map Fin.val).sum * (-1) ^ ((rw (P w)).map Fin.val).sum) := by ring
        _ = _ := by rw [this, mul_one]

theorem word_eq_inversions {n : ℕ} (w : List (Fin n)) :
    OddPlactic.word n w = (-1 : ℤ) ^ (TableauRowWord.inversions (w.map Fin.val) +
      TableauRowWord.inversions ((rw (P w)).map Fin.val)) • tabWord n (P w) := by
  rw [← insSign_eq_inversions, word_eq]

end

end OddMath.Frontier.OddLRPlactic
