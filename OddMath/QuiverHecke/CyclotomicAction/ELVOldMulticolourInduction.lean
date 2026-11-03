/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleMulticolourBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMulticolourBraid

/-! # Multicolour OLD braids on direct triple induction

Brundan–Ellis (1.9): the independently whiskered positive coefficient
crossings induce the whole direct triple-induction braid. The actual
OLD quotient supplies the source relation; no braid premise is introduced.
The negative equal-colour crossing normalization, rectangular flattening
and repeated-outer ordered correction are separate attachments.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The append along the prescribed three source colours. -/
abbrev tripleAppend (i j l : I) :=
  (append D Sc cutoff i ⋙ append D Sc cutoff j) ⋙ append D Sc cutoff l

theorem triplePrefix_supernatural (i j l : I) :
    IsSupernatural k (D.parity i * D.parity j)
      (F := tripleAppend D Sc cutoff i j l) (G := tripleAppend D Sc cutoff j i l)
      (triplePrefix D Sc cutoff i j l) := by
  simpa only [mul_comm] using
    (Distinct.cross_supernatural D Sc cutoff j i).whiskerRight (append D Sc cutoff l)

theorem tripleSuffix_supernatural (i j l : I) :
    IsSupernatural k (D.parity j * D.parity l)
      (F := tripleAppend D Sc cutoff i j l) (G := tripleAppend D Sc cutoff i l j)
      (tripleSuffix D Sc cutoff i j l) := by
  simpa only [mul_comm] using
    (Distinct.cross_supernatural D Sc cutoff l j).whiskerLeft (append D Sc cutoff i)

/-- The full direct balanced-induction maps satisfy the uncorrected multicolour braid. -/
theorem directTripleCross_braid (i j l : I) (hb : ¬ (i = l ∧ i ≠ j))
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    transformComponent (triplePrefix_supernatural D Sc cutoff j l i) M ≫
      transformComponent (tripleSuffix_supernatural D Sc cutoff j i l) M ≫
        transformComponent (triplePrefix_supernatural D Sc cutoff i j l) M =
    transformComponent (tripleSuffix_supernatural D Sc cutoff l i j) M ≫
      transformComponent (triplePrefix_supernatural D Sc cutoff i l j) M ≫
        transformComponent (tripleSuffix_supernatural D Sc cutoff i j l) M :=
  transformComponent_multicolour_braid
    (tripleAppend D Sc cutoff i j l) (tripleAppend D Sc cutoff j i l)
    (tripleAppend D Sc cutoff j l i) (tripleAppend D Sc cutoff l j i)
    (tripleAppend D Sc cutoff i l j) (tripleAppend D Sc cutoff l i j)
    (triplePrefix_supernatural D Sc cutoff i j l)
    (tripleSuffix_supernatural D Sc cutoff j i l)
    (triplePrefix_supernatural D Sc cutoff j l i)
    (tripleSuffix_supernatural D Sc cutoff i j l)
    (triplePrefix_supernatural D Sc cutoff i l j)
    (tripleSuffix_supernatural D Sc cutoff l i j)
    (tripleCross_braid D Sc cutoff i j l hb) M

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
