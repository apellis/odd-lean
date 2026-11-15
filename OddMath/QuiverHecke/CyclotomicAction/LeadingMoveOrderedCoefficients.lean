/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveProduct
import OddMath.QuiverHecke.CyclotomicAction.LeadingMovePolynomial
import OddMath.QuiverHecke.HnBasis

/-!
# Concrete ordered coefficients of the moving product

`prependWordCoefficients_moveHom_ordered` computes the longest-shuffle
coefficient of the prescribed moving homomorphism by a finite sum over local
choices. `leadingMoveOrderedCoefficients_explicit` separates the moving degree
from the old diagonal dot monomial. All distant separation signs cancel for
these square factors, in both parities. The old monomials are already sorted,
and `leadingMoveOrderedCoefficients_nonidentity` excludes every nonidentity
old permutation.

The degree-normalizing sign is trivial on this producer. Invariance under the
separate old matrix twist is not asserted here.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA MonoidalCategory
open scoped Classical
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The moving degree counts only dots at the new source position zero. -/
def sourceMovingDegree : List ℕ → ℕ
  | [] => 0
  | 0 :: ps => sourceMovingDegree ps + 1
  | (_ + 1) :: ps => sourceMovingDegree ps

/-- Dot monomials with the object family fixed to the matrix object family. -/
def wordEndpointDots {n : ℕ} (w : Word I n) (ps : List ℕ) : End (wordObj D Sc w) :=
  endpointDotMonomial D Sc w.1 ps

/-- A positioned dot with the object family fixed. -/
def wordPositionDot {n : ℕ} (w : Word I n) (p : ℕ) : End (wordObj D Sc w) :=
  dotE D Sc w.1 p

/-- Delete moving dots and renumber every old source position. -/
def sourceOldDots : List ℕ → List ℕ
  | [] => []
  | 0 :: ps => sourceOldDots ps
  | (p + 1) :: ps => p :: sourceOldDots ps

theorem sourceMovingDegree_append (ps qs : List ℕ) :
    sourceMovingDegree (ps ++ qs) = sourceMovingDegree ps + sourceMovingDegree qs := by
  induction ps with
  | nil => simp [sourceMovingDegree]
  | cons p ps ih =>
    cases p <;> simp [sourceMovingDegree, ih, Nat.add_right_comm]

omit [Fintype I] in
/-- Odd moving colours have only even moving degrees, including zero. -/
theorem sourceMovingDegree_leadingSourceDots_even (i : I) (hi : D.parity i = 1)
    (a : ℕ) (ν : List I) (c : MoveChoices ν) :
    sourceMovingDegree (leadingSourceDots D i 0 a ν c) % 2 = 0 := by
  induction ν generalizing a with
  | nil => rfl
  | cons j ν ih =>
    rcases c with ⟨b, c⟩
    by_cases hij : i = j
    · subst j
      fin_cases b <;>
        simp [leadingSourceDots, leadingSourceBlockDots, hi,
          sourceMovingDegree, Nat.add_mod, ih]
    · simp [leadingSourceDots, leadingSourceBlockDots, hij, ih]

omit [Fintype I] in
/-- The prescribed leading crossing word is already the canonical descending run. -/
theorem leadingMoveWord_eq_descRun (l ν : List I) :
    leadingMoveWord l ν = descRun l.length ν.length := by
  induction ν generalizing l with
  | nil => rfl
  | cons j ν ih => simp [leadingMoveWord, ih, descRun_succ]

omit [Fintype I] in
/-- Old positions in the finite producer are already in PBW order and bounded. -/
theorem sourceOldDots_leadingSourceDots_ordered (i : I) (a : ℕ)
    (ν : List I) (c : MoveChoices ν) :
    (sourceOldDots (leadingSourceDots D i 0 a ν c)).Pairwise (· ≤ ·) ∧
      ∀ p ∈ sourceOldDots (leadingSourceDots D i 0 a ν c), a ≤ p ∧ p < a + ν.length := by
  induction ν generalizing a with
  | nil => simp [leadingSourceDots, sourceOldDots]
  | cons j ν ih =>
    rcases c with ⟨b, c⟩
    obtain ⟨hs, hb⟩ := ih (a + 1) c
    have hlo : ∀ p ∈ sourceOldDots (leadingSourceDots D i 0 (a + 1) ν c), a ≤ p := by
      intro p hp
      exact Nat.le_trans (Nat.le_succ a) (hb p hp).1
    have hrange : ∀ p ∈ sourceOldDots (leadingSourceDots D i 0 (a + 1) ν c),
        a ≤ p ∧ p < a + (j :: ν).length := by
      intro p hp
      have := hb p hp
      simp only [List.length_cons]
      omega
    by_cases hij : i = j
    · subst j
      rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
      all_goals
        fin_cases b <;>
          simp [leadingSourceDots, leadingSourceBlockDots, hi,
            sourceOldDots, List.pairwise_cons, hs] <;>
          first | exact hrange | exact ⟨hlo, hrange⟩
    · simp only [leadingSourceDots, leadingSourceBlockDots, hij, ↓reduceIte,
        List.nil_append]
      exact ⟨hs, hrange⟩

end OddMath.QuiverHecke
