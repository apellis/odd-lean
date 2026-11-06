/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Braid

/-!
# The repeated-outside-colour cyclotomic braid correction

Ports the algebraic `braidQ` input of
`Categorification/KLR/CyclotomicAction/Square.lean`. The super divided-difference
polynomial retains its coefficient `(-1)^(|i|(|j|+s))`, including odd outside
colours. The equality is in the actual cyclotomic algebra; it does not yet
transport the three crossings through triple-superinduction associators.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- The explicit super divided-difference correction on an old-word corner. -/
def tripleBraidCorrection (i j : I) {n : ℕ} (w : Word I n) :
    End (wordObj D Sc (tripleWord i j i w)) :=
  ∑ s ∈ Finset.range (D.dn i j),
    (SKM.zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
      (dotE D Sc (tripleWord i j i w).1 w.1.length ^ (D.dn i j - 1 - s) *
        dotE D Sc (tripleWord i j i w).1 (w.1.length + 2) ^ s) +
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      ∑ s ∈ Finset.range p,
        (SKM.zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          (dotE D Sc (tripleWord i j i w).1 w.1.length ^ (p - 1 - s) *
            dotE D Sc (tripleWord i j i w).1 (w.1.length + 1) ^ q *
            dotE D Sc (tripleWord i j i w).1 (w.1.length + 2) ^ s)

/-- The full signed repeated-colour relation on each three-strand corner. -/
theorem tripleCross_braid_correction (i j : I) (hij : i ≠ j) {n : ℕ} (w : Word I n) :
    (tripleCrossLeft D Sc i j i w ≫ tripleCrossRight D Sc j i i w ≫
        tripleCrossLeft D Sc j i i w) -
      (tripleCrossRight D Sc i j i w ≫ tripleCrossLeft D Sc i i j w ≫
        tripleCrossRight D Sc i i j w) = tripleBraidCorrection D Sc i j w := by
  dsimp only [tripleCrossLeft, tripleCrossRight]
  rw [cl_comp, cl_comp, cl_comp, cl_comp]
  exact braid_iji D Sc w.1 [] hij _ _

variable [Fintype I]

/-- The correction as a diagonal family in the actual finite-matrix algebra. -/
def affineTripleBraidCorrection (i j : I) (n : ℕ) : Hn D Sc (n + 3) :=
  tripleMatrix D Sc i j i i j i (tripleBraidCorrection D Sc i j)

end OddMath.QuiverHecke
