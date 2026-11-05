import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentCategory
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleAction
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRowLeading

/-! # Fixed-content height and finite matrix counts
DeformedMatrixComparison section 4 fixes one finite unit/cap count on an
exact-content block. The actual raw degree difference depends only on
that content; no equivalence between old and truncated categories is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The actual Cartan height of the supplied coefficient content. -/
def contentCrossingHeight (i : I) (β : Multiset I) : ℤ :=
  (cutoff i : ℤ) - (β.map (fun j => D.h i (D.α j))).sum

@[simp] theorem contentCrossingHeight_coe (i : I) (v : List I) :
    contentCrossingHeight D cutoff i (v : Multiset I) =
      (cutoff i : ℤ) - (v.map (fun j => D.h i (D.α j))).sum := rfl

/-- The prescribed unit count is the nonnegative part of the actual content height. -/
def contentUnitCount (i : I) (β : Multiset I) : ℕ :=
  (contentCrossingHeight D cutoff i β).toNat

/-- The prescribed cap count is the nonnegative part of the negative content height. -/
def contentCapCount (i : I) (β : Multiset I) : ℕ :=
  (-contentCrossingHeight D cutoff i β).toNat

theorem contentUnitCount_cast (i : I) (β : Multiset I)
    (h : 0 ≤ contentCrossingHeight D cutoff i β) :
    (contentUnitCount D cutoff i β : ℤ) = contentCrossingHeight D cutoff i β :=
  Int.toNat_of_nonneg h

theorem contentCapCount_cast (i : I) (β : Multiset I)
    (h : contentCrossingHeight D cutoff i β ≤ 0) :
    (contentCapCount D cutoff i β : ℤ) = -contentCrossingHeight D cutoff i β :=
  Int.toNat_of_nonneg (neg_nonneg.mpr h)

/-- The actual row-degree difference is exactly the fixed-content Cartan height. -/
theorem crossingHeight_eq_content (i : I) (v : List I) :
    (endpointQPDegree D cutoff i v : ℤ) - outputSDegree D i v =
      contentCrossingHeight D cutoff i (v : Multiset I) := by
  rw [contentCrossingHeight_coe, endpointQPDegree_sub_outputSDegree]

/-- Every actual untruncated content object has the same matrix height. -/
theorem oldContent_crossingHeight (i : I) (ν : List I)
    (v : OldContentCategory D Sc cutoff ν) :
    (endpointQPDegree D cutoff i v.obj.word : ℤ) - outputSDegree D i v.obj.word =
      contentCrossingHeight D cutoff i (ν : Multiset I) := by
  rw [crossingHeight_eq_content, Multiset.coe_eq_coe.mpr v.wordPerm]

/-- A single explicit count satisfies the positive matrix degree equality on the old block. -/
theorem oldContent_unitCount_height (i : I) (ν : List I)
    (h : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (v : OldContentCategory D Sc cutoff ν) :
    endpointQPDegree D cutoff i v.obj.word = outputSDegree D i v.obj.word +
      contentUnitCount D cutoff i (ν : Multiset I) := by
  have hv := oldContent_crossingHeight D Sc cutoff i ν v
  have hm := contentUnitCount_cast D cutoff i (ν : Multiset I) h
  omega

/-- A single explicit count satisfies the negative matrix degree equality on the old block. -/
theorem oldContent_capCount_height (i : I) (ν : List I)
    (h : contentCrossingHeight D cutoff i (ν : Multiset I) ≤ 0)
    (v : OldContentCategory D Sc cutoff ν) :
    outputSDegree D i v.obj.word = endpointQPDegree D cutoff i v.obj.word +
      contentCapCount D cutoff i (ν : Multiset I) := by
  have hv := oldContent_crossingHeight D Sc cutoff i ν v
  have hm := contentCapCount_cast D cutoff i (ν : Multiset I) h
  omega

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

