/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.BraidCorrection
import OddMath.QuiverHecke.CyclotomicAction.SuperCrossing

/-!
# Signed right operators for the three-strand braid

Ports the signed-operator input corresponding to
`Categorification/KLR/CyclotomicAction/Braid.lean`. The three crossing matrices
have their actual homogeneous degrees. On a graded regular module, reversing
three homogeneous right multipliers introduces a sign symmetric in their
three degrees. Thus the uncorrected braid remains valid as an equality of
signed operators. Identification with triple-superinduction remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- First-pair crossing parity on the actual triple-word corner. -/
theorem tripleCrossLeft_parity (i j c : I) {n : ℕ} (w : Word I n) :
    tripleCrossLeft D Sc i j c w ∈ parity (R := k) _ _ (D.parity i * D.parity j) := by
  unfold tripleCrossLeft cl
  apply Presentation.diag_mem_homDeg'
  simp [degree_parity_mkD, tripleWord, pl, PG.ld, Shape.parity]

/-- Last-pair crossing parity on the actual triple-word corner. -/
theorem tripleCrossRight_parity (i j c : I) {n : ℕ} (w : Word I n) :
    tripleCrossRight D Sc i j c w ∈ parity (R := k) _ _ (D.parity j * D.parity c) := by
  unfold tripleCrossRight cl
  apply Presentation.diag_mem_homDeg'
  have hle : w.1.length ≤ n + 1 := by omega
  simp [degree_parity_mkD, tripleWord, pl, PG.ld, Shape.parity, List.take_append,
    List.drop_append, List.take_of_length_le hle, List.drop_eq_nil_of_le hle]

variable [Fintype I]

section Regular
variable {A : Type u} [Ring A] [Algebra k A]
  (G : ZMod 2 → Submodule k A) [GradedAlgebra G]

end Regular

end OddMath.QuiverHecke
