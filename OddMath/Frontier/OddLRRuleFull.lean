import OddMath.Frontier.OddLRRuleKnuth

/-!
# Skew tableaux as tableaux of the full shape

Ellis, arXiv:1111.3932v1, §4.2, p.13 and proof of Theorem 4.8, p.14: a skew tableau `S` of
shape `λ/μ` is completed to `T_S ∈ SSYT(λ)` by filling `μ` with `T_μ` (row `i` filled with
`i + 1`) and adding `m = ℓ(μ)` to the entries of `S`. We prove:

* `fullEquiv`: skew tableaux of shape `λ/μ` ↔ tableaux of shape `λ` restricting to `T_μ`;
* `tableauSign_toFull`: `sign(T_S) = (-1)^{N(μ)} sign(S)` (`sign(S) = (-1)^{N^<(Ŝ)}`);
* `rowWord_toFull_filter`: the row word of `T_S` restricted to letters `> m` is `w_r(S) + m`.
-/

namespace OddMath.Frontier.OddLRRule

open TableauSign TableauEvaluation OddLRTableau

variable {lam mu : YoungDiagram}

theorem mem_of_le (h : mu ≤ lam) {p : ℕ × ℕ} (hp : p ∈ mu) : p ∈ lam :=
  YoungDiagram.cells_subset_iff.mpr h (by simpa using hp) |> (YoungDiagram.mem_cells _).mp

theorem row_lt_colLen {μ : YoungDiagram} {i j : ℕ} (h : (i, j) ∈ μ) : i < μ.colLen 0 :=
  YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (Nat.zero_le j) h)

/-- `T_S`: `T_μ` on `μ`, `S + ℓ(μ)` on `λ/μ`. -/
def toFull (S : SkewTableau lam mu) : PositiveTableau lam where
  entry i j := if (i, j) ∈ mu then i + 1 else if (i, j) ∈ lam then S.entry i j + mu.colLen 0 else 0
  row_weak' := by
    intro i j₁ j₂ hj h
    by_cases h2 : (i, j₂) ∈ mu
    · rw [if_pos (mu.up_left_mem le_rfl hj.le h2), if_pos h2]
    · rw [if_neg h2, if_pos h]
      by_cases h1 : (i, j₁) ∈ mu
      · rw [if_pos h1]; have := row_lt_colLen h1; omega
      · rw [if_neg h1, if_pos (lam.up_left_mem le_rfl hj.le h)]
        have := S.row_weak hj h h1; omega
  col_strict' := by
    intro i₁ i₂ j hi h
    by_cases h2 : (i₂, j) ∈ mu
    · rw [if_pos (mu.up_left_mem hi.le le_rfl h2), if_pos h2]; omega
    · rw [if_neg h2, if_pos h]
      by_cases h1 : (i₁, j) ∈ mu
      · rw [if_pos h1]; have := row_lt_colLen h1; have := S.positive h h2; omega
      · rw [if_neg h1, if_pos (lam.up_left_mem hi.le le_rfl h)]
        have := S.col_strict hi h h1; omega
  zeros' := by
    intro i j h
    rw [if_neg (fun hm => h (mem_of_le S.sub hm)), if_neg h]
  positive := by
    intro i j h
    by_cases h1 : (i, j) ∈ mu
    · rw [if_pos h1]; omega
    · rw [if_neg h1, if_pos h]; have := S.positive h h1; omega

theorem toFull_entry_mu (S : SkewTableau lam mu) {i j : ℕ} (h : (i, j) ∈ mu) :
    (toFull S).entry i j = i + 1 := if_pos h

theorem toFull_entry_skew (S : SkewTableau lam mu) {i j : ℕ} (h : (i, j) ∈ lam) (h' : (i, j) ∉ mu) :
    (toFull S).entry i j = S.entry i j + mu.colLen 0 := by
  change (if (i, j) ∈ mu then i + 1 else if (i, j) ∈ lam then S.entry i j + mu.colLen 0 else 0) = _
  rw [if_neg h', if_pos h]

/-- Tableaux of shape `λ` restricting to `T_μ` on `μ` and exceeding `ℓ(μ)` on `λ/μ`. -/
def FullCond (mu : YoungDiagram) (T : PositiveTableau lam) : Prop :=
  mu ≤ lam ∧ (∀ i j, (i, j) ∈ mu → T.entry i j = i + 1) ∧
    (∀ i j, (i, j) ∈ lam → (i, j) ∉ mu → mu.colLen 0 < T.entry i j)

theorem fullCond_toFull (S : SkewTableau lam mu) : FullCond mu (toFull S) :=
  ⟨S.sub, fun _ _ h => toFull_entry_mu S h, fun i j h h' => by
    rw [toFull_entry_skew S h h']; have := S.positive h h'; omega⟩

/-- Inverse of `toFull`. -/
def fromFull (T : PositiveTableau lam) (hT : FullCond mu T) : SkewTableau lam mu where
  entry i j := if (i, j) ∈ lam ∧ (i, j) ∉ mu then T.entry i j - mu.colLen 0 else 0
  sub := hT.1
  row_weak := by
    intro i j₁ j₂ hj h h1
    have h2 : (i, j₂) ∉ mu := fun hm => h1 (mu.up_left_mem le_rfl hj.le hm)
    rw [if_pos ⟨lam.up_left_mem le_rfl hj.le h, h1⟩, if_pos ⟨h, h2⟩]
    have := T.row_weak' hj h; omega
  col_strict := by
    intro i₁ i₂ j hi h h1
    have h2 : (i₂, j) ∉ mu := fun hm => h1 (mu.up_left_mem hi.le le_rfl hm)
    rw [if_pos ⟨lam.up_left_mem hi.le le_rfl h, h1⟩, if_pos ⟨h, h2⟩]
    have := T.col_strict' hi h
    have := hT.2.2 i₁ j (lam.up_left_mem hi.le le_rfl h) h1
    omega
  zeros_out := by intro i j h; rw [if_neg (fun h' => h h'.1)]
  zeros_in := by intro i j h; rw [if_neg (fun h' => h'.2 h)]
  positive := by
    intro i j h h'
    rw [if_pos ⟨h, h'⟩]; have := hT.2.2 i j h h'; omega

theorem toFull_fromFull (T : PositiveTableau lam) (hT : FullCond mu T) :
    toFull (fromFull T hT) = T := by
  apply TableauContent.ext_cells
  intro p hp
  have hp' : (p.1, p.2) ∈ lam := by simpa using hp
  by_cases hm : (p.1, p.2) ∈ mu
  · rw [toFull_entry_mu _ hm, hT.2.1 _ _ hm]
  · rw [toFull_entry_skew _ hp' hm]
    change (if (p.1, p.2) ∈ lam ∧ (p.1, p.2) ∉ mu then T.entry p.1 p.2 - mu.colLen 0 else 0) + _ = _
    rw [if_pos ⟨hp', hm⟩]
    have := hT.2.2 _ _ hp' hm; omega

theorem fromFull_toFull (S : SkewTableau lam mu) : fromFull (toFull S) (fullCond_toFull S) = S := by
  apply SkewTableau.ext_skew
  intro p hp
  obtain ⟨hl, hm⟩ := mem_skewCells.mp hp
  change (if (p.1, p.2) ∈ lam ∧ (p.1, p.2) ∉ mu then (toFull S).entry p.1 p.2 - mu.colLen 0
    else 0) = _
  rw [if_pos ⟨hl, hm⟩, toFull_entry_skew S hl hm]; omega

theorem toFull_injective : Function.Injective (toFull (lam := lam) (mu := mu)) := by
  intro S S' h
  rw [← fromFull_toFull S, ← fromFull_toFull S']
  congr 1

/-- Skew tableaux of shape `λ/μ` are the tableaux of shape `λ` satisfying `FullCond`. -/
def fullEquiv : SkewTableau lam mu ≃ {T : PositiveTableau lam // FullCond mu T} where
  toFun S := ⟨toFull S, fullCond_toFull S⟩
  invFun T := fromFull T.1 T.2
  left_inv S := fromFull_toFull S
  right_inv T := Subtype.ext (toFull_fromFull T.1 T.2)

theorem inAlphabet_toFull (S : SkewTableau lam mu) {r : ℕ} (hr : ∀ i j, S.entry i j ≤ r) :
    InAlphabet (mu.colLen 0 + r) (toFull S) := by
  intro p hp
  have hp' : (p.1, p.2) ∈ lam := by simpa using hp
  by_cases hm : (p.1, p.2) ∈ mu
  · rw [toFull_entry_mu S hm]; have := row_lt_colLen hm; omega
  · rw [toFull_entry_skew S hp' hm]; have := hr p.1 p.2; omega

/-! ## Row words and signs -/

theorem rowWord_toFull (S : SkewTableau lam mu) :
    TableauRowWord.rowWord (toFull S) =
      (TableauRowWord.rowCells lam).map (fun p => (toFull S).entry p.1 p.2) := rfl

/-- `w_r(T_S)` restricted to letters `> ℓ(μ)` is `w_r(S)` shifted by `ℓ(μ)`. -/
theorem rowWord_toFull_filter (S : SkewTableau lam mu) :
    (TableauRowWord.rowWord (toFull S)).filter (fun a => decide (mu.colLen 0 < a)) =
      S.rowWord.map (· + mu.colLen 0) := by
  rw [rowWord_toFull, SkewTableau.rowWord, List.filter_map, List.map_map]
  have hf : ∀ p ∈ TableauRowWord.rowCells lam,
      ((fun a => decide (mu.colLen 0 < a)) ∘ fun p : ℕ × ℕ => (toFull S).entry p.1 p.2) p =
        decide (p ∉ mu.cells) := by
    intro p hp
    have hp' : (p.1, p.2) ∈ lam := by simpa using (TableauRowWord.mem_rowCells lam p).mp hp
    by_cases hm : (p.1, p.2) ∈ mu
    · simp only [Function.comp_apply, toFull_entry_mu S hm]
      have := row_lt_colLen hm
      simp [show ¬ mu.colLen 0 < p.1 + 1 by omega, hm]
    · simp only [Function.comp_apply, toFull_entry_skew S hp' hm]
      have := S.positive hp' hm
      simp [show mu.colLen 0 < S.entry p.1 p.2 + mu.colLen 0 by omega, hm]
  rw [List.filter_congr hf]
  apply List.map_congr_left
  intro p hp
  have hp2 := (List.mem_filter.mp hp)
  have hp' : (p.1, p.2) ∈ lam := by simpa using (TableauRowWord.mem_rowCells lam p).mp hp2.1
  have hm : (p.1, p.2) ∉ mu := by simpa using hp2.2
  simp [toFull_entry_skew S hp' hm]

/-- Inversions split along a predicate separating small from large letters. -/
theorem inversions_split (m : ℕ) (P : ℕ × ℕ → Prop) [DecidablePred P] (f g : ℕ × ℕ → ℕ) :
    ∀ l : List (ℕ × ℕ), (∀ p ∈ l, P p → g p = 0 ∧ f p ≤ m) →
      (∀ p ∈ l, ¬ P p → f p = g p + m ∧ 0 < g p) →
      TableauRowWord.inversions (l.map f) =
        TableauRowWord.inversions (l.map g) + TableauRowWord.inversions ((l.filter P).map f)
  | [], _, _ => rfl
  | p :: l, h1, h2 => by
    have h1' : ∀ q ∈ l, P q → g q = 0 ∧ f q ≤ m := fun q hq => h1 q (List.mem_cons_of_mem _ hq)
    have h2' : ∀ q ∈ l, ¬ P q → f q = g q + m ∧ 0 < g q := fun q hq => h2 q (List.mem_cons_of_mem _ hq)
    have ih := inversions_split m P f g l h1' h2'
    by_cases hp : P p
    · obtain ⟨hg, hf⟩ := h1 p List.mem_cons_self hp
      rw [List.filter_cons_of_pos (by simpa using hp)]
      simp only [List.map_cons, TableauRowWord.inversions, ih]
      have e1 : ((l.map g).filter (fun y => decide (y < g p))).length = 0 := by
        rw [hg]; simp
      have e2 : ((l.map f).filter (fun y => decide (y < f p))).length =
          (((l.filter P).map f).filter (fun y => decide (y < f p))).length := by
        rw [List.filter_map, List.filter_map, List.length_map, List.length_map, List.filter_filter]
        congr 1
        apply List.filter_congr
        intro q hq
        by_cases hq' : P q
        · simp [hq']
        · have := h2' q hq hq'
          simp only [Function.comp_apply, hq', decide_false, Bool.and_false]
          simp; omega
      omega
    · obtain ⟨hf, hg⟩ := h2 p List.mem_cons_self hp
      rw [List.filter_cons_of_neg (by simpa using hp)]
      simp only [List.map_cons, TableauRowWord.inversions, ih]
      have e : ((l.map f).filter (fun y => decide (y < f p))).length =
          ((l.map g).filter (fun y => decide (y < g p))).length := by
        rw [List.filter_map, List.filter_map, List.length_map, List.length_map]
        congr 1
        apply List.filter_congr
        intro q hq
        by_cases hq' : P q
        · have := h1' q hq hq'
          simp only [Function.comp_apply]
          rw [decide_eq_decide]; constructor <;> intro _ <;> omega
        · have := h2' q hq hq'
          simp only [Function.comp_apply]
          rw [decide_eq_decide]; constructor <;> intro _ <;> omega
      omega

theorem rowCells_filter (h : mu ≤ lam) :
    (TableauRowWord.rowCells lam).filter (fun p => decide (p ∈ mu.cells)) =
      TableauRowWord.rowCells mu := by
  apply List.eq_of_perm_of_sorted (r := TableauRowWord.RowLE)
  · apply (List.perm_ext_iff_of_nodup ((TableauRowWord.rowCells_nodup lam).filter _)
      (TableauRowWord.rowCells_nodup mu)).mpr
    intro p
    simp only [List.mem_filter, TableauRowWord.mem_rowCells, decide_eq_true_eq]
    constructor
    · exact fun h' => h'.2
    · intro h'
      exact ⟨YoungDiagram.cells_subset_iff.mpr h h', h'⟩
  · exact (TableauRowWord.rowCells_sorted lam).filter _
  · exact TableauRowWord.rowCells_sorted mu

instance : IsAntisymm (ℕ × ℕ) TableauRowWord.RowLE :=
  ⟨by intro a b h1 h2; unfold TableauRowWord.RowLE at h1 h2; ext <;> omega⟩

/-- `sign(T_S) = (-1)^{N(μ)} sign(S)`, `sign(S) = (-1)^{N^<(Ŝ)}` (E §4.2). -/
theorem tableauSign_toFull (S : SkewTableau lam mu) :
    TableauDominance.tableauSign (toFull S) = (-1 : ℤ) ^ TableauStripSigns.north mu * S.sign := by
  classical
  have hsplit := inversions_split (mu.colLen 0) (fun p => p ∈ mu.cells)
    (fun p => (toFull S).entry p.1 p.2) (fun p => S.entry p.1 p.2) (TableauRowWord.rowCells lam)
    (by
      intro p _ hp
      have hp' : (p.1, p.2) ∈ mu := by simpa using hp
      exact ⟨S.zeros_in hp', by
        show (toFull S).entry p.1 p.2 ≤ _
        rw [toFull_entry_mu S hp']; have := row_lt_colLen hp'; omega⟩)
    (by
      intro p hpl hp
      have hl : (p.1, p.2) ∈ lam := by simpa using (TableauRowWord.mem_rowCells lam p).mp hpl
      have hp' : (p.1, p.2) ∉ mu := by simpa using hp
      exact ⟨toFull_entry_skew S hl hp', S.positive hl hp'⟩)
  have hmu : ((TableauRowWord.rowCells lam).filter (fun p => p ∈ mu.cells)).map
      (fun p => (toFull S).entry p.1 p.2) =
      TableauRowWord.rowWord (TableauDominance.canonicalTableau mu) := by
    rw [rowCells_filter S.sub]
    apply List.map_congr_left
    intro p hp
    have hp' : p ∈ mu.cells := (TableauRowWord.mem_rowCells mu p).mp hp
    rw [TableauDominance.canonical_entry hp', toFull_entry_mu S (by simpa using hp')]
  rw [hmu] at hsplit
  have hc := CompleteTableauExpansion.canonical_sign mu
  unfold TableauDominance.tableauSign at hc ⊢
  rw [rowWord_toFull, hsplit, pow_add, ← hc]
  unfold SkewTableau.sign SkewTableau.Nlt SkewTableau.hatWord
  ring

end OddMath.Frontier.OddLRRule
