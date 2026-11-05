/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Global
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight

/-! # Matrix counts on an entire original-weight fibre

DeformedActionAssembly §§1, 6 fixes a highest cutoff weight Λ with
cutoff(i)=h_i(Λ). Its induction categories have weight sum(α)-Λ.
Thus the content-matrix height is the negative categorical weight height,
and the finite counts agree on every content in an original-weight fibre.
No injectivity of the root or coroot maps is assumed.
-/

noncomputable section
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X : Type u} [AddCommGroup X]
  (D : SKM.Datum I X) (cutoff : I → ℕ)

/-- The matrix height is constant on each original-weight fibre, even
before the cutoff has been identified with the highest-weight pairings. -/
theorem contentCrossingHeight_weightBlock (i : I) (Λ x : X)
    (β : WeightBlocks D Λ x) :
    contentCrossingHeight D cutoff i β.1 =
      (cutoff i : ℤ) - D.h i Λ - D.h i x := by
  have hb := congrArg (D.cd.coroot i) β.2
  change (D.cd.coroot i) ((β.1.map D.α).sum - Λ) = (D.cd.coroot i) x at hb
  simp only [map_sub, map_multiset_sum, Multiset.map_map, Function.comp_def] at hb
  unfold contentCrossingHeight SKM.Datum.h
  omega

/-- The source-required cutoff compatibility identifies the two height
conventions; it is not asserted for arbitrary unrelated Λ and cutoff. -/
theorem contentCrossingHeight_eq_neg_weight (i : I) (Λ x : X)
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (β : WeightBlocks D Λ x) :
    contentCrossingHeight D cutoff i β.1 = -D.h i x := by
  rw [contentCrossingHeight_weightBlock D cutoff i Λ x β, hcutoff, sub_self, zero_sub]

/-- The unit-window count is exactly the negative categorical height. -/
theorem contentUnitCount_weightBlock (i : I) (Λ x : X)
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (β : WeightBlocks D Λ x) :
    contentUnitCount D cutoff i β.1 = (-D.h i x).toNat := by
  unfold contentUnitCount
  rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x hcutoff β]

/-- The cap-window count is exactly the positive categorical height. -/
theorem contentCapCount_weightBlock (i : I) (Λ x : X)
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (β : WeightBlocks D Λ x) :
    contentCapCount D cutoff i β.1 = (D.h i x).toNat := by
  unfold contentCapCount
  rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x hcutoff β, neg_neg]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
