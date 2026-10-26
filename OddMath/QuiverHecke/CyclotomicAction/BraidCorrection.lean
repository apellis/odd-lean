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

/-- Repeated-outside-colour braid in the affine superalgebra. -/
theorem affineTriple_braid_correction (i j : I) (hij : i ≠ j) (n : ℕ) :
    affineTripleLeft D Sc j i i n *
        (affineTripleRight D Sc j i i n * affineTripleLeft D Sc i j i n) -
      affineTripleRight D Sc i i j n *
        (affineTripleLeft D Sc i i j n * affineTripleRight D Sc i j i n) =
      affineTripleBraidCorrection D Sc i j n := by
  simp only [affineTripleLeft, affineTripleRight, affineTripleBraidCorrection, tripleMatrix_mul]
  unfold tripleMatrix
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  rw [← DFinsupp.single_sub]
  congr 1
  simpa only [Category.assoc] using tripleCross_braid_correction D Sc i j hij w

/-- The signed correction survives the specified two-sided cyclotomic quotient. -/
theorem cyclotomicTriple_braid_correction (i j : I) (hij : i ≠ j)
    (a : I → _root_.Polynomial k) (n : ℕ) :
    cyclotomicMk D Sc a (n + 2) (affineTripleLeft D Sc j i i n) *
        (cyclotomicMk D Sc a (n + 2) (affineTripleRight D Sc j i i n) *
          cyclotomicMk D Sc a (n + 2) (affineTripleLeft D Sc i j i n)) -
      cyclotomicMk D Sc a (n + 2) (affineTripleRight D Sc i i j n) *
        (cyclotomicMk D Sc a (n + 2) (affineTripleLeft D Sc i i j n) *
          cyclotomicMk D Sc a (n + 2) (affineTripleRight D Sc i j i n)) =
      cyclotomicMk D Sc a (n + 2) (affineTripleBraidCorrection D Sc i j n) := by
  simp only [← map_mul, ← map_sub]
  exact congrArg (cyclotomicMk D Sc a (n + 2)) (affineTriple_braid_correction D Sc i j hij n)

end OddMath.QuiverHecke
