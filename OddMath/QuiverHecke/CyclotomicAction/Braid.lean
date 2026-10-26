/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LastCrossing

/-!
# Three-strand braid identities in cyclotomic colour corners

Ports the algebraic braid input of
`Categorification/KLR/CyclotomicAction/Braid.lean`. Words read left to right,
diagrams compose bottom to top, and matrix multiplication reverses diagram
composition. The braid with distinct outside colours has no additional sign,
even when all three colours are odd. The assertion is in the concrete affine
and cyclotomic algebras, before transport through the induction associator.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- Attach three specified colours, retaining the old-word index. -/
def tripleWord (i j c : I) {n : ℕ} (w : Word I n) : Word I (n + 3) :=
  ⟨w.1 ++ [i,j,c] ++ [], by simp [w.2]⟩

theorem tripleWord_injective (i j c : I) (n : ℕ) :
    Function.Injective (tripleWord i j c (n := n)) := by
  intro a b h
  apply Subtype.ext
  exact List.append_cancel_right (List.append_cancel_right (congrArg Subtype.val h))

/-- Crossing the first two added strands. -/
def tripleCrossLeft (i j c : I) {n : ℕ} (w : Word I n) :
    wordObj D Sc (tripleWord i j c w) ⟶ wordObj D Sc (tripleWord j i c w) :=
  cl D Sc _ _ [.cross w.1.length] (by
    simp [tripleWord, pl, PG.ld, Shape.dom, Shape.cod])

/-- Crossing the last two added strands. -/
def tripleCrossRight (i j c : I) {n : ℕ} (w : Word I n) :
    wordObj D Sc (tripleWord i j c w) ⟶ wordObj D Sc (tripleWord i c j w) :=
  cl D Sc _ _ [.cross (w.1.length + 1)] (by
    have hle : w.1.length ≤ n + 1 := by omega
    simp [tripleWord, pl, PG.ld, Shape.dom, Shape.cod, List.take_append,
      List.drop_append, List.append_assoc, List.take_of_length_le hle,
      List.drop_eq_nil_of_le hle])

/-- The diagram-level braid on each old-word corner. -/
theorem tripleCross_braid (i j c : I) (hb : ¬ (i = c ∧ i ≠ j)) {n : ℕ} (w : Word I n) :
    tripleCrossLeft D Sc i j c w ≫ tripleCrossRight D Sc j i c w ≫
        tripleCrossLeft D Sc j c i w =
      tripleCrossRight D Sc i j c w ≫ tripleCrossLeft D Sc i c j w ≫
        tripleCrossRight D Sc c i j w := by
  dsimp only [tripleCrossLeft, tripleCrossRight]
  rw [cl_comp, cl_comp, cl_comp, cl_comp]
  exact braid_ne D Sc w.1 [] i j c hb _ _

variable [Fintype I]

/-- A family of morphisms on three-strand corners as a finite matrix. -/
def tripleMatrix (i j c i' j' c' : I) {n : ℕ}
    (f : ∀ w : Word I n, wordObj D Sc (tripleWord i j c w) ⟶
      wordObj D Sc (tripleWord i' j' c' w)) : Hn D Sc (n + 3) :=
  ∑ w, FiniteHomMatrix.single (tripleWord i' j' c' w) (tripleWord i j c w) (f w)

/-- Multiplication of corner families is pointwise reversed composition. -/
theorem tripleMatrix_mul (i j c i' j' c' i'' j'' c'' : I) {n : ℕ}
    (f : ∀ w : Word I n, wordObj D Sc (tripleWord i j c w) ⟶
      wordObj D Sc (tripleWord i' j' c' w))
    (g : ∀ w : Word I n, wordObj D Sc (tripleWord i' j' c' w) ⟶
      wordObj D Sc (tripleWord i'' j'' c'' w)) :
    tripleMatrix D Sc i' j' c' i'' j'' c'' g * tripleMatrix D Sc i j c i' j' c' f =
      tripleMatrix D Sc i j c i'' j'' c'' (fun w => f w ≫ g w) := by
  simp only [tripleMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_mul, Finset.sum_eq_single w]
  · exact FiniteHomMatrix.single_mul_single _ _ _ _ _
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (tripleWord_injective i' j' c' n h)) _ _
  · simp

/-- First-pair affine crossing with the third added colour fixed. -/
def affineTripleLeft (i j c : I) (n : ℕ) : Hn D Sc (n + 3) :=
  tripleMatrix D Sc i j c j i c (tripleCrossLeft D Sc i j c)

/-- Last-pair affine crossing with the first added colour fixed. -/
def affineTripleRight (i j c : I) (n : ℕ) : Hn D Sc (n + 3) :=
  tripleMatrix D Sc i j c i c j (tripleCrossRight D Sc i j c)

/-- The affine braid, including arbitrary old strands and all colour parities. -/
theorem affineTriple_braid (i j c : I) (hb : ¬ (i = c ∧ i ≠ j)) (n : ℕ) :
    affineTripleLeft D Sc j c i n *
        (affineTripleRight D Sc j i c n * affineTripleLeft D Sc i j c n) =
      affineTripleRight D Sc c i j n *
        (affineTripleLeft D Sc i c j n * affineTripleRight D Sc i j c n) := by
  simp only [affineTripleLeft, affineTripleRight, tripleMatrix_mul]
  congr 1
  funext w
  simpa only [Category.assoc] using tripleCross_braid D Sc i j c hb w

/-- The braid survives the specified two-sided cyclotomic quotient. -/
theorem cyclotomicTriple_braid (i j c : I) (hb : ¬ (i = c ∧ i ≠ j))
    (a : I → _root_.Polynomial k) (n : ℕ) :
    cyclotomicMk D Sc a (n + 2) (affineTripleLeft D Sc j c i n) *
        (cyclotomicMk D Sc a (n + 2) (affineTripleRight D Sc j i c n) *
          cyclotomicMk D Sc a (n + 2) (affineTripleLeft D Sc i j c n)) =
      cyclotomicMk D Sc a (n + 2) (affineTripleRight D Sc c i j n) *
        (cyclotomicMk D Sc a (n + 2) (affineTripleLeft D Sc i c j n) *
          cyclotomicMk D Sc a (n + 2) (affineTripleRight D Sc i j c n)) := by
  simp only [← map_mul]
  exact congrArg (cyclotomicMk D Sc a (n + 2)) (affineTriple_braid D Sc i j c hb n)

end OddMath.QuiverHecke
