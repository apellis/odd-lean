/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LeadingMovePolynomial

/-!
# Longest coefficients of the collected moving chain

The prescribed `contentMove` has the same longest prepend coefficients as
its explicit endpoint-polynomial crossing matrix. Coefficients are still
computed by PBW regrouping; no identification with a prescribed polynomial
or source-dot sorting is asserted.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA
open scoped Classical
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Scalar vanishing in the longest row survives old-matrix regrouping. -/
theorem prependEntryCoefficients_long_eq_zero (i : I) (s : List I)
    (t : Word I (s.length + 1))
    (f : wordObj D Sc (prependWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t)
    (hf : ∀ x : PrependIdx i s t.1,
      x.1.2.2.2 = longPrependShuffle s.length → (prependBasis D Sc).repr f x = 0)
    (m : ℕ) :
    prependEntryCoefficients D Sc i s t f (longPrependShuffle s.length, m) = 0 := by
  classical
  unfold prependEntryCoefficients
  erw [LinearMap.comp_apply, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  by_cases h : x.1.2.2.2 = longPrependShuffle s.length
  · erw [hf x h]
    simp
  · simp [h]

/-- The finite matrix obtained by replacing each moving chain with its
collected endpoint polynomial followed by the prescribed crossing chain. -/
def collectedContentMove (i : I) (n : ℕ) (β : Multiset I) : Hn D Sc (n + 1) :=
  ∑ s ∈ Finset.univ.filter (fun s : Word I n => wordContent s = β),
    FiniteHomMatrix.single (appendWord i s) (prependWord i s)
      (leadingMoveEndpointPolynomial D Sc i [] s.1 ≫
        cl D Sc _ _ (cw (leadingMoveWord [] s.1)) (leadingMoveWord_sChain i [] s.1))

/-- Entrywise comparison for the longest shuffle, retaining every old
permutation and dot degree in the coefficient matrix. -/
theorem prependWordCoefficients_moveHom_long (i : I) {n : ℕ} (s : Word I n) (m : ℕ) :
    prependWordCoefficients D Sc i s (appendWord i s) (moveHom D Sc i [] s.1)
      (longPrependShuffle n, m) =
    prependWordCoefficients D Sc i s (appendWord i s)
      (leadingMoveEndpointPolynomial D Sc i [] s.1 ≫
        cl D Sc _ _ (cw (leadingMoveWord [] s.1)) (leadingMoveWord_sChain i [] s.1))
      (longPrependShuffle n, m) := by
  rcases s with ⟨s, hs⟩
  subst n
  apply sub_eq_zero.mp
  rw [← Finsupp.sub_apply]
  erw [← map_sub]
  apply prependEntryCoefficients_long_eq_zero
  intro x hx
  exact prependBasis_long_repr_eq_zero_of_low D Sc i s (s ++ [i]) _
    (moveHom_sub_endpointPolynomial_mem_low D Sc i [] s) x hx

/-- Longest prepend coefficients of the prescribed content moving chain
are exactly those of the assembled finite endpoint-polynomial matrix. -/
theorem contentMove_long_prependCoefficients (i : I) (n : ℕ) (β : Multiset I) (m : ℕ) :
    prependCoefficients D Sc i n (contentMove D Sc i n β) (longPrependShuffle n, m) =
      prependCoefficients D Sc i n (collectedContentMove D Sc i n β)
        (longPrependShuffle n, m) := by
  simp only [contentMove, collectedContentMove, map_sum, Finsupp.coe_finsetSum,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro s hs
  erw [prependCoefficients_single, prependCoefficients_single]
  exact prependWordCoefficients_moveHom_long D Sc i s m

/-- Explicit finite wordwise coefficient formula. The endpoint polynomial
inside each summand is the finite signed sum over `MoveChoices`; the
remaining evaluation is precisely the existing scalar PBW regrouping. -/
theorem contentMove_long_prependCoefficients_sum (i : I) (n : ℕ)
    (β : Multiset I) (m : ℕ) :
    prependCoefficients D Sc i n (contentMove D Sc i n β) (longPrependShuffle n, m) =
      ∑ s ∈ Finset.univ.filter (fun s : Word I n => wordContent s = β),
        prependWordCoefficients D Sc i s (appendWord i s)
          (leadingMoveEndpointPolynomial D Sc i [] s.1 ≫
            cl D Sc _ _ (cw (leadingMoveWord [] s.1)) (leadingMoveWord_sChain i [] s.1))
          (longPrependShuffle n, m) := by
  rw [contentMove_long_prependCoefficients]
  simp only [collectedContentMove, map_sum, prependCoefficients_single,
    Finsupp.coe_finsetSum, Finset.sum_apply]

/-- Extraction retains the old parity twist and the corrected degree sign
when the concrete collected matrix replaces the moving chain. -/
theorem appendContentMoveLift_extract_collected (a : I → _root_.Polynomial k)
    (n : ℕ) (β : Multiset I) (i : I)
    (b : CyclotomicContentCorner D Sc a n β) (m : ℕ) :
    appendContentRhoExtract D Sc a n β i (appendContentMoveLift D Sc a n β i b) m =
      (SKM.zsign ℤ (D.parity i * Multiset.sum (Multiset.map D.parity β))) ^ m •
        (homMatrixTwist D Sc (n + 1) (appendContentParity D a β i)
          (prependCoefficients D Sc i (n + 1) (collectedContentMove D Sc i (n + 1) β)
            (longPrependShuffle (n + 1), m)) • b) := by
  rw [appendContentMoveLift_extract, contentMove_long_prependCoefficients]

end OddMath.QuiverHecke
