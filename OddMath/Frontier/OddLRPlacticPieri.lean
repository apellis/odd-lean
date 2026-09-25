import OddMath.Frontier.OddLRPlacticBasis
import OddMath.Frontier.OddLRThm38

/-!
# Plactic odd Schur elements ŝ_λ and their e-right Pieri rule in ℤPl_n

Ellis, *The odd Littlewood–Richardson rule*, arXiv:1111.3932v1 ("E"):
* Definition 3.3, (3.3), p. 9: `ŝ_λ = (-1)^{dN(λ)+N(λ)} Σ_{T ∈ SSYT(λ)} T ∈ ZPl_n`;
  its image in `OPol_n` is (3.4) `s^p_λ` (`toSkew_shat`).
* (3.10), p. 11 (proof of Theorem 3.8): the e-right Pieri rule
  `ŝ_λ ŝ_{(1^k)} = Σ_μ (-1)^{|i_1/λ|+…+|i_k/λ|} ŝ_μ`, μ/λ a vertical strip of size k.
  E states (3.10) for `s^p` in `OPol_n`; here it is proved in ℤPl_n itself
  (`vertical_pieri`), which is what Corollary 3.9 needs.

Proof: the insertion argument of `OddLRVerticalPieri`, run at the level of ℤPl_n: the signed
insertion identity `TableauStripSigns.run_word` holds in ℤPl_n, the bijection
`OddLRVerticalPieri.aggregateEquiv` and the sign telescoping `run_parity` are reused.
The Pieri rule is then transcribed to the row-set form `OddLRElimination.RightPieri` used by
the triangular elimination (as in `OddLRThm38.pieri310`, `OddLRElimination.pieri310_bounded`).
-/

namespace OddMath.Frontier.OddLRPlactic

open scoped BigOperators
open TableauStripSigns TableauEvaluation DegreeShapes TableauSign
open OddLRVerticalPieri (Vertical stripBelow histBelow)
open OddLRElimination (belowRows rowInc stripRows addStrip toYoung)

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Tableaux of shape λ with entries at most n. -/
abbrev TabOf (n : ℕ) (lam : YoungDiagram) := {T : PositiveTableau lam // InAlphabet n T}

/-- **E Definition 3.3, (3.3)**: `ŝ_λ = (-1)^{dN(λ)+N(λ)} Σ_{T ∈ SSYT(λ)} w_r(T) ∈ ℤPl_n`. -/
def shat (n : ℕ) (lam : YoungDiagram) : OddPlactic.Plactic n :=
  (-1 : ℤ) ^ (directNorth lam + north lam) •
    ∑ T : TabOf n lam, OddPlactic.word n (rowFinWord n T.val T.property)

/-- E (3.4): the image of `ŝ_λ` in `OPol_n` is `s^p_λ`. -/
theorem toSkew_shat (n : ℕ) (lam : YoungDiagram) :
    PlacticEvaluation.toSkew n (shat n lam) = CompleteTableauExpansion.sp n lam := by
  rw [shat, CompleteTableauExpansion.sp, TableauHorizontalPieri.tableau_sum, map_zsmul, map_sum]
  rfl

/-- `ŝ_λ = 0` when λ has more than n rows (no tableau of shape λ with entries ≤ n). -/
theorem shat_tall (n : ℕ) (mu : YoungDiagram) (h : (n, 0) ∈ mu) : shat n mu = 0 := by
  rw [shat]
  convert smul_zero _
  apply Finset.sum_eq_zero
  intro T _
  exfalso
  have h1 : T.val.entry n 0 ≤ n := T.property (n, 0) h
  have h2 := TableauDominance.entry_ge_row T.val h
  omega

/-- The unique tableau of the empty shape. -/
theorem shat_bot (n : ℕ) : shat n ⊥ = 1 := by
  have hu : ∀ T : TabOf n ⊥, T = ⟨EKClassicalPlactic.emptyTableau,
      EKClassicalPlactic.emptyTableau_inAlphabet n⟩ := by
    intro T
    apply Subtype.ext
    apply TableauContent.ext_cells
    intro p hp
    exact absurd hp (by simp)
  letI : Unique (TabOf n ⊥) := ⟨⟨_⟩, hu⟩
  have hd : directNorth ⊥ + north ⊥ = 0 := by simp [directNorth, north]
  rw [shat, hd, pow_zero, one_smul, Fintype.sum_unique]
  exact tabWord_empty n

theorem shat_column (n k : ℕ) :
    shat n (OddLRVerticalPieri.column k) =
      ∑ T : TabOf n (OddLRVerticalPieri.column k), OddPlactic.word n (rowFinWord n T.val T.property) := by
  rw [shat, OddLRVerticalPieri.column_directNorth, ← two_mul, pow_mul]
  norm_num

/-! ## Pointwise signed insertion in ℤPl_n -/

/-- (3.10) pointwise, in ℤPl_n: inserting a strictly decreasing word. -/
theorem run_plactic (n : ℕ) (S : State n) (w : List (Fin n)) (hw : w.Pairwise (· > ·)) :
    (-1 : ℤ) ^ (directNorth S.1 + north S.1) • (tabWord n S * OddPlactic.word n w) =
    (-1 : ℤ) ^ (directNorth (TableauWordInsertion.run n S w).1.1 +
        north (TableauWordInsertion.run n S w).1.1 +
        histBelow S.1 (TableauWordInsertion.run n S w).2) •
      tabWord n (TableauWordInsertion.run n S w).1 := by
  rw [tabWord, ← OddPlactic.word_append, word_rw_append, smul_smul, ← pow_add]
  congr 1
  obtain ⟨X, hX⟩ := OddLRVerticalPieri.run_parity n S w hw
  have h1 := shape_partition S.1
  have h2 := shape_partition (TableauWordInsertion.run n S w).1.1
  apply OddLRVerticalPieri.neg_one_pow_congr
    (x := directNorth (TableauWordInsertion.run n S w).1.1 +
      northEast (TableauWordInsertion.run n S w).1.1)
    (y := X + directNorth S.1 + northEast S.1)
  omega

/-! ## Aggregation -/

def inputValue (n : ℕ) (lam : YoungDiagram) (k : ℕ)
    (x : TabOf n lam × TabOf n (OddLRVerticalPieri.column k)) : OddPlactic.Plactic n :=
  (-1 : ℤ) ^ (directNorth lam + north lam) •
    (OddPlactic.word n (rowFinWord n x.1.val x.1.property) *
      OddPlactic.word n (rowFinWord n x.2.val x.2.property))

def outputValue (n : ℕ) (lam : YoungDiagram) (S : State n) : OddPlactic.Plactic n :=
  (-1 : ℤ) ^ (directNorth S.1 + north S.1 + stripBelow lam S.1) • tabWord n S

theorem pointwise (n : ℕ) (lam : YoungDiagram) (k : ℕ)
    (x : TabOf n lam × TabOf n (OddLRVerticalPieri.column k)) :
    inputValue n lam k x = outputValue n lam
      (OddLRVerticalPieri.outputMap n lam k (OddLRVerticalPieri.aggregateEquiv n lam k x)).val := by
  have he : OddLRVerticalPieri.outputMap n lam k (OddLRVerticalPieri.aggregateEquiv n lam k x) =
      OddLRVerticalPieri.vInsertionEquiv n lam k (OddLRVerticalPieri.inputMap n lam k x) :=
    (OddLRVerticalPieri.outputEquiv n lam k).apply_symm_apply _
  rw [he]
  change inputValue n lam k x = outputValue n lam
    (TableauWordInsertion.run n ⟨lam, x.1⟩ (rowFinWord n x.2.1 x.2.2)).1
  have h := run_plactic n ⟨lam, x.1⟩ (rowFinWord n x.2.1 x.2.2)
    (OddLRVerticalPieri.column_word_decreasing n k x.2.1 x.2.2)
  rw [OddLRVerticalPieri.run_histBelow] at h
  exact h

theorem input_sum (n : ℕ) (lam : YoungDiagram) (k : ℕ) :
    shat n lam * shat n (OddLRVerticalPieri.column k) =
      ∑ x : TabOf n lam × TabOf n (OddLRVerticalPieri.column k), inputValue n lam k x := by
  rw [shat_column, shat, Fintype.sum_prod_type, smul_mul_assoc, Finset.sum_mul_sum,
    Finset.smul_sum]
  simp only [inputValue, Finset.smul_sum]

theorem output_sum (n : ℕ) (lam : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (lam.card + k)
    ∑ y : OddLRVerticalPieri.Indexed n lam k,
        outputValue n lam (OddLRVerticalPieri.outputMap n lam k y).val =
      ∑ nu : DegreeShape (lam.card + k), if Vertical lam nu.val then
        (-1 : ℤ) ^ stripBelow lam nu.val • shat n nu.val
      else 0 := by
  letI := degreeFintype (lam.card + k)
  rw [Fintype.sum_sigma]
  have hv : ∀ nu : OddLRVerticalPieri.Outer lam k, ∑ T : TabOf n nu.val.val,
      outputValue n lam (OddLRVerticalPieri.outputMap n lam k ⟨nu, T⟩).val =
      (-1 : ℤ) ^ stripBelow lam nu.val.val • shat n nu.val.val := by
    intro nu
    simp only [outputValue, OddLRVerticalPieri.outputMap, tabWord]
    rw [← Finset.smul_sum]
    unfold shat
    rw [smul_smul, ← pow_add]
    congr 2
    ring
  rw [Fintype.sum_congr _ _ hv]
  rw [← Finset.sum_filter]
  symm
  exact Finset.sum_subtype _ (by simp) _

/-- **E (3.10) in ℤPl_n**: `ŝ_λ ŝ_{(1^k)} = Σ_{μ/λ vertical k-strip} (-1)^{Σ_j |i_j/λ|} ŝ_μ`,
for every n, λ and k (shapes with more than n rows are included; their `ŝ` vanish). -/
theorem vertical_pieri (n : ℕ) (lam : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (lam.card + k)
    shat n lam * shat n (OddLRVerticalPieri.column k) =
      ∑ mu : DegreeShape (lam.card + k), if Vertical lam mu.val then
        (-1 : ℤ) ^ stripBelow lam mu.val • shat n mu.val
      else 0 := by
  letI := degreeFintype (lam.card + k)
  rw [input_sum, ← output_sum]
  exact Fintype.sum_equiv (OddLRVerticalPieri.aggregateEquiv n lam k) _ _ (pointwise n lam k)

/-! ## Transcription to the row-set form of the elimination -/

open OddLRThm38 (rowsOf vertical_addStrip rowsOf_mem rowsOf_addStrip addStrip_rowsOf
  card_addStrip stripBelow_of_vertical)

/-- (3.10) in ℤPl_n, indexed by the row sets `stripRows` of the elimination. -/
theorem pieri_rows (N : ℕ) (lam : YoungDiagram) (k : ℕ) :
    shat N lam * shat N (TableauExtremal.columnShape k) =
      ∑ I ∈ stripRows lam k, (-1 : ℤ) ^ (∑ a ∈ I, belowRows lam a) • shat N (addStrip lam k I) := by
  letI := degreeFintype (lam.card + k)
  have hv := vertical_pieri N lam k
  rw [OddLRThm38.column_eq_columnShape] at hv
  rw [hv, ← Finset.sum_filter]
  symm
  refine Finset.sum_bij'
    (fun I hI => (⟨addStrip lam k I, card_addStrip hI⟩ : DegreeShape (lam.card + k)))
    (fun mu _ => rowsOf lam mu.val) ?_ ?_ ?_ ?_ ?_
  · intro I hI
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, vertical_addStrip hI⟩
  · intro mu hmu
    rw [Finset.mem_filter] at hmu
    exact rowsOf_mem hmu.2 mu.property
  · intro I hI
    exact rowsOf_addStrip hI
  · intro mu hmu
    rw [Finset.mem_filter] at hmu
    exact Subtype.ext (addStrip_rowsOf hmu.2 mu.property)
  · intro I hI
    change _ = (-1 : ℤ) ^ stripBelow lam (addStrip lam k I) • shat N (addStrip lam k I)
    rw [stripBelow_of_vertical (vertical_addStrip hI), rowsOf_addStrip hI]

open OddLRElimination (strRows strRows_mem finRows finRows_strip finRows_map belowRows_toYoung
  mem_addStrip rowInc_strRows toYoung_column)
open OddSchurPieri (lowerRows VerticalStrip stripPartition)

/-- (3.10) in ℤPl_{n+2}, in the exact form `OddLRElimination.RightPieri` of (3.7). -/
theorem rightPieri (n : ℕ) :
    OddLRElimination.RightPieri (fun α : OddSymmetrizer.PartitionExponent n =>
      shat (n+2) (toYoung α)) := by
  intro k hk α
  change shat (n+2) (toYoung α) * shat (n+2) (toYoung (OddSchurPieri.column n k)) = _
  rw [toYoung_column n k hk, pieri_rows (n+2) (toYoung α) k]
  rw [← Finset.sum_filter_add_sum_filter_not (stripRows (toYoung α) k)
    (· ⊆ Finset.range (n+2))]
  rw [Finset.sum_eq_zero (s := (stripRows (toYoung α) k).filter
    (fun I => ¬ I ⊆ Finset.range (n+2))), add_zero]
  · symm
    refine Finset.sum_bij' (fun J _ => strRows J)
      (fun I hI => (⟨finRows n I, finRows_strip I hI⟩ : VerticalStrip n k α)) ?_ ?_ ?_ ?_ ?_
    · intro J _; exact strRows_mem J
    · intro I _; exact Finset.mem_univ _
    · intro J _
      apply Subtype.ext
      ext j
      simp [finRows, strRows, Fin.val_inj]
    · intro I hI
      exact finRows_map n I (Finset.mem_filter.mp hI).2
    · intro J _
      have hsign : (∑ a ∈ strRows J, belowRows (toYoung α) a) = lowerRows α.val J.val := by
        rw [strRows, Finset.sum_map]
        unfold lowerRows
        apply Finset.sum_congr rfl
        intro i _
        exact belowRows_toYoung α i
      have hmem := (Finset.mem_filter.mp (strRows_mem J)).1
      have hdiag : addStrip (toYoung α) k (strRows J) = toYoung (stripPartition J) := by
        apply YoungDiagram.ext
        ext p
        change p ∈ addStrip (toYoung α) k (strRows J) ↔ p ∈ toYoung (stripPartition J)
        rw [mem_addStrip _ _ hmem, OddLRElimination.mem_toYoung, rowInc_strRows]
      rw [hsign, hdiag]
  · intro I hI
    rw [Finset.mem_filter] at hI
    obtain ⟨a, ha, han⟩ := Finset.not_subset.mp hI.2
    rw [Finset.mem_range, not_lt] at han
    have hin : (a, (toYoung α).rowLen a) ∈ addStrip (toYoung α) k I := by
      rw [mem_addStrip _ _ hI.1]
      simp [rowInc, ha]
    have htall : (n+2, 0) ∈ addStrip (toYoung α) k I :=
      (addStrip (toYoung α) k I).isLowerSet (show ((n+2, 0) : ℕ × ℕ) ≤ (a, _) from
        ⟨han, Nat.zero_le _⟩) hin
    rw [shat_tall (n+2) _ htall, smul_zero]

end

end OddMath.Frontier.OddLRPlactic
