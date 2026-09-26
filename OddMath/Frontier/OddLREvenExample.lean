import OddMath.Frontier.OddLRExamplesTools

/-!
# Example 4.3 of Ellis, arXiv:1111.3932v1

E §4.1, Example 4.3, p.13: "The lowest degree product which is not described by the Pieri rule is
`s₂₁s₂₁ = s₂₂₁₁ + s₂₂₂ + s₃₁₁₁ + 2s₃₂₁ + s₃₃ + s₄₁₁ + s₄₂`" (`example_4_3`), in the ring of
symmetric functions `Λ₁`. The coefficients are the Littlewood–Richardson counts of Theorem 4.1
(`OddLREven.thm_4_1`), computed on the library's skew tableaux (`OddLRExamples.card_lrTableaux_eq`),
and every partition of `6` is accounted for (`OddLRExamples.rowLens_mem_partsF`).
-/

namespace OddMath.Frontier.OddLREven

open scoped BigOperators
open OddLRTableau OddLRExamples

noncomputable section

/-- The partition with row lengths `w`. -/
abbrev yd (w : List ℕ) (h : w.Sorted (· ≥ ·) := by decide) : YoungDiagram :=
  YoungDiagram.ofRowLens w h

theorem rowLens_yd (w : List ℕ) (h : w.Sorted (· ≥ ·)) (hpos : ∀ x ∈ w, 0 < x) :
    (yd w h).rowLens = w :=
  YoungDiagram.rowLens_ofRowLens_eq_self hpos

theorem eq_iff_rowLens (a b : YoungDiagram) : a = b ↔ a.rowLens = b.rowLens := by
  constructor
  · rintro rfl; rfl
  · intro h
    rw [← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := a),
      ← YoungDiagram.ofRowLens_to_rowLens_eq_self (μ := b)]
    congr 1

theorem eq_yd {lam : YoungDiagram} {w : List ℕ} (h : lam.rowLens = w) (hw : w.Sorted (· ≥ ·)) :
    lam = YoungDiagram.ofRowLens w hw := by
  subst h
  exact YoungDiagram.ofRowLens_to_rowLens_eq_self.symm

theorem repr_sE (a lam : YoungDiagram) :
    sBasisE.repr (sE a) lam = if a.rowLens = lam.rowLens then 1 else 0 := by
  classical
  rw [← sBasisE_apply, Basis.repr_self, Finsupp.single_apply]
  by_cases h : a = lam
  · rw [if_pos h, if_pos ((eq_iff_rowLens a lam).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((eq_iff_rowLens a lam).mpr h'))]

theorem repr_sE_of_card {a lam : YoungDiagram} (h : a.card ≠ lam.card) :
    sBasisE.repr (sE a) lam = 0 := by
  rw [repr_sE, if_neg]
  intro h'
  exact h (by rw [(eq_iff_rowLens a lam).mpr h'])

theorem card_yd (w : List ℕ) (h : w.Sorted (· ≥ ·)) : (yd w h).card = w.sum :=
  EKPartitionSpanning.card_ofRowLens w h

theorem card_lrTableaux_of_not_sub {lam mu nu : YoungDiagram} (h : ¬ mu.cells ⊆ lam.cells) :
    (lrTableaux lam mu nu).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
  intro S _
  exact h (YoungDiagram.cells_subset_iff.mpr S.sub)

set_option maxRecDepth 4000 in
/-- **E Example 4.3**: `s₂₁ s₂₁ = s₂₂₁₁ + s₂₂₂ + s₃₁₁₁ + 2 s₃₂₁ + s₃₃ + s₄₁₁ + s₄₂` in `Λ₁`. -/
theorem example_4_3 :
    sE (yd [2, 1]) * sE (yd [2, 1]) =
      sE (yd [2, 2, 1, 1]) + sE (yd [2, 2, 2]) + sE (yd [3, 1, 1, 1]) + 2 • sE (yd [3, 2, 1]) +
        sE (yd [3, 3]) + sE (yd [4, 1, 1]) + sE (yd [4, 2]) := by
  apply sBasisE.repr.injective
  ext lam
  change evenLR lam (yd [2, 1]) (yd [2, 1]) = _
  simp only [map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply]
  by_cases hc : lam.card = 6
  · have hmem := rowLens_mem_partsF lam
    rw [hc, show partsF 6 6 6 = [[1, 1, 1, 1, 1, 1], [2, 1, 1, 1, 1], [2, 2, 1, 1], [2, 2, 2],
      [3, 1, 1, 1], [3, 2, 1], [3, 3], [4, 1, 1], [4, 2], [5, 1], [6]] by decide] at hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    simp only [repr_sE, rowLens_yd [2, 2, 1, 1] _ (by decide), rowLens_yd [2, 2, 2] _ (by decide),
      rowLens_yd [3, 1, 1, 1] _ (by decide), rowLens_yd [3, 2, 1] _ (by decide),
      rowLens_yd [3, 3] _ (by decide), rowLens_yd [4, 1, 1] _ (by decide),
      rowLens_yd [4, 2] _ (by decide)]
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h <;>
    · rw [h, eq_yd h (by decide), thm_4_1]
      first
        | (rw [card_lrTableaux_eq (cellsL_ofRowLens _ _ _) (by decide) [2, 1] (by decide)]; decide)
        | (rw [card_lrTableaux_of_not_sub (by decide)]; decide)
  · rw [evenLR_eq_zero (by rw [card_yd]; simpa using hc)]
    have hz : ∀ (w : List ℕ) (h : w.Sorted (· ≥ ·)), w.sum = 6 →
        sBasisE.repr (sE (yd w h)) lam = 0 :=
      fun w h hs => repr_sE_of_card (by rw [card_yd, hs]; exact fun e => hc e.symm)
    rw [hz [2, 2, 1, 1] _ rfl, hz [2, 2, 2] _ rfl, hz [3, 1, 1, 1] _ rfl, hz [3, 2, 1] _ rfl,
      hz [3, 3] _ rfl, hz [4, 1, 1] _ rfl, hz [4, 2] _ rfl]
    simp

end

end OddMath.Frontier.OddLREven
