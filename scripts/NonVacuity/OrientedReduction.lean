import OddMath.SKM.OrientedReduction
import Mathlib.Tactic

/-! A concrete coefficient detector with both types of error and distinct
labels at equal crossing and dot counts. This is not an SKM representation. -/

namespace NonVacuity.OrientedReduction
open scoped BigOperators

private abbrev Label := ℕ × ℕ × Bool
private def crossings (i : Label) : ℕ := i.1
private def dots (i : Label) : ℕ := i.2.1

private def entry (i j : Label) (p : ℤ) : ℤ :=
  if i = j then -p
  else if crossings i < crossings j then 2 * p
  else if crossings i = crossings j ∧ dots j < dots i then 3 * p
  else 0

private theorem entry_cross (i j : Label) (p : ℤ)
    (h : crossings j < crossings i) : entry i j p = 0 := by
  have hne : i ≠ j := by intro he; subst j; omega
  have hlt : ¬crossings i < crossings j := by omega
  have heq : crossings i ≠ crossings j := by omega
  simp [entry, hne, hlt, heq]

private theorem entry_dot (i j : Label) (p : ℤ)
    (hc : crossings j = crossings i) (hd : dots i < dots j) :
    entry i j p = 0 := by
  have hne : i ≠ j := by intro he; subst j; omega
  have hlt : ¬crossings i < crossings j := by omega
  have hdot : ¬dots j < dots i := by omega
  simp [entry, hne, hlt, hdot]

private theorem entry_label (i j : Label) (p : ℤ)
    (hc : crossings j = crossings i) (hd : dots j = dots i) (hne : j ≠ i) :
    entry i j p = 0 := by
  have hlt : ¬crossings i < crossings j := by omega
  simp [entry, Ne.symm hne, hlt, hd]

private noncomputable def family : Label →₀ ℤ :=
  Finsupp.single (1, 0, false) 5 + Finsupp.single (1, 0, true) (-5) +
    Finsupp.single (0, 100, false) 7

/-- Both equal-rank labels survive separately, even with cancelling total
coefficients and a lower-crossing term carrying many more dots. -/
theorem family_detected : ∃ i,
    (∑ j ∈ family.support, entry i j (family j)) ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ i, (∑ j ∈ family.support, entry i j (family j)) = 0 := by
    intro i
    exact Classical.byContradiction (fun hi => h ⟨i, hi⟩)
  have hf := OddMath.SKM.OrientedReduction.eq_zero_of_crossing_dot_coefficients
    crossings dots entry entry_cross entry_dot entry_label
    (fun i p hp => by simpa [entry] using hp) family hz
  have he := congrArg (fun f : Label →₀ ℤ => f (1, 0, false)) hf
  norm_num [family, Finsupp.single_apply] at he

-- The off-diagonal pieces are not zero: lower crossings can have arbitrary
-- dot counts, while unchanged crossings can only acquire additional dots.
example : entry (0, 100, true) (1, 0, false) 3 = 6 := by decide
example : entry (1, 2, false) (1, 0, false) 3 = 9 := by decide
example : entry (1, 0, true) (1, 0, false) 3 = 0 := by decide

#print axioms OddMath.SKM.OrientedReduction.eq_zero_of_crossing_dot_coefficients
#print axioms family_detected
end NonVacuity.OrientedReduction
