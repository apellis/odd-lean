import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Max

/-!
# Finite coefficient detection for the oriented nondegeneracy reduction

This is the additive leading-coefficient step proposed for the reduction of
Brundan–Ellis, *Super Kac–Moody 2-categories*, §8, to upward independence.
It handles decreasing crossing length together with increasing open-dot count.
It does not construct the diagrammatic sorting or closure maps, or assert the
Nondegeneracy Conjecture. Those comparison maps remain separate obligations.
-/

namespace OddMath.SKM.OrientedReduction
open scoped BigOperators

/-- A finite coefficient relation is detected by greatest crossing length and,
within that length, least dot count. Equal bidegrees retain their individual
labels: only the matching diagonal may contribute there.

Neither filtration is assumed globally bounded. The output coefficient group
may differ from the input group, and a diagonal need only reflect zero.
No commutativity of coefficient multiplication, domain, field, or grading of
bubble coefficients is used. -/
theorem eq_zero_of_crossing_dot_coefficients
    {A M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (crossings dots : A → ℕ) (entry : A → A → M → N)
    (hcross : ∀ i j p, crossings j < crossings i → entry i j p = 0)
    (hdot : ∀ i j p, crossings j = crossings i → dots i < dots j →
      entry i j p = 0)
    (hlabel : ∀ i j p, crossings j = crossings i → dots j = dots i →
      j ≠ i → entry i j p = 0)
    (hdiag : ∀ i p, entry i i p = 0 → p = 0)
    (f : A →₀ M)
    (h : ∀ i, (∑ j ∈ f.support, entry i j (f j)) = 0) : f = 0 := by
  classical
  by_contra hf
  have hs := Finsupp.support_nonempty_iff.mpr hf
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image f.support crossings hs
  let S := f.support.filter fun j => crossings j = crossings a
  have hS : S.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S dots hS
  have his := (Finset.mem_filter.mp hi).1
  have hic := (Finset.mem_filter.mp hi).2
  have hz := h i
  rw [Finset.sum_eq_single i] at hz
  · exact (Finsupp.mem_support_iff.mp his) (hdiag i (f i) hz)
  · intro j hj hji
    have hjc : crossings j ≤ crossings i := by simpa [hic] using hmax j hj
    rcases lt_or_eq_of_le hjc with hjlt | hjeq
    · exact hcross i j (f j) hjlt
    · have hjS : j ∈ S := Finset.mem_filter.mpr ⟨hj, hjeq.trans hic⟩
      have hjd := hmin j hjS
      rcases lt_or_eq_of_le hjd with hdlt | hdeq
      · exact hdot i j (f j) hjeq hdlt
      · exact hlabel i j (f j) hjeq hdeq.symm hji
  · intro hnot
    exact False.elim (hnot his)

end OddMath.SKM.OrientedReduction
