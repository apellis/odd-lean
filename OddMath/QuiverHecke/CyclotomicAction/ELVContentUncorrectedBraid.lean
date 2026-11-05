/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization

/-! # The uncorrected full-coefficient content braid

Brundan–Ellis Definition 1.5, the braid outside the repeated-outer correction
case. Both paths use the independent pair crossings and their induction
whiskerings. No local inverse or factor action is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private def crossingSign (i j : I) : k := by
  classical
  exact if i = j then -1 else 1

private theorem normalized_crossing (i j : I) :
    contentCrossAffine D Sc i j = crossingSign (k := k) i j • crossTwo D Sc i j := by
  classical
  by_cases h : i = j <;> simp [contentCrossAffine, crossingSign, h]

def contentNormalizedLeft (i j l : I) :=
  contentTriplePrefixAffine D Sc i j l
def contentNormalizedRight (i j l : I) :=
  (pres D Sc).obj (ob D [i]) ◁ contentCrossAffine D Sc j l

theorem contentNormalizedLeft_mem (i j l : I) :
    contentNormalizedLeft D Sc i j l ∈ parity (R := k) _ _ (D.parity i * D.parity j) :=
  contentTriplePrefixAffine_mem D Sc i j l
theorem contentNormalizedRight_mem (i j l : I) :
    contentNormalizedRight D Sc i j l ∈ parity (R := k) _ _ (D.parity j * D.parity l) :=
  MonoidalSupercategory.whiskerLeft_mem (R := k) _ (contentCrossAffine_mem D Sc j l)

/-- Both normalized source paths carry the same product of pair signs. -/
theorem contentNormalized_braid (i j l : I) (hb : ¬ (i = l ∧ i ≠ j)) :
    contentNormalizedLeft D Sc i j l ≫ contentNormalizedRight D Sc j i l ≫
        contentNormalizedLeft D Sc j l i =
      contentNormalizedRight D Sc i j l ≫ contentNormalizedLeft D Sc i l j ≫
        contentNormalizedRight D Sc l i j := by
  simp only [contentNormalizedLeft, contentTriplePrefixAffine_eq_whisker,
    contentNormalizedRight, normalized_crossing,
    MonoidalSupercategory.smul_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_smul (R := k),
    ← contentTripleLeft_whisker, ← contentTripleRight_whisker,
    Linear.smul_comp, Linear.comp_smul, smul_smul]
  have h := tripleCross_braid D Sc i j l hb ⟨[], rfl⟩
  change contentTripleLeft D Sc i j l ≫ contentTripleRight D Sc j i l ≫
      contentTripleLeft D Sc j l i =
    contentTripleRight D Sc i j l ≫ contentTripleLeft D Sc i l j ≫
      contentTripleRight D Sc l i j at h
  rw [h]
  congr 1
  ring

end OddMath.QuiverHecke.ELVOld
