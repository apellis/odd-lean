import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedWindowInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTruncation

/-! # Weighted boundary contractions in raw kernel coordinates

SwappedHomInversion §4 (7): evaluate the chosen weighted finite `g'`
contractions by the raw OLD boundary coefficients in both height orientations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local instance boundaryWeightedPi : PiSupercategory k
    (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) := supermodulePiSupercategory
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The prescribed weighted unit followed by its finite inverse row. -/
def weightedContentUnitBoundaryValue (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (j : Fin (contentUnitCount D cutoff i β)) (r : ℕ) (b : M.obj w.obj) :=
  ((weightedContentLocalInverseFrom D Sc cutoff N i M β hh).g' j.val).total w
    ((unitDotColumn (T) (truncatedDot_supernatural D Sc cutoff N i) M r).total w.obj b)

/-- The prescribed finite cap inverse column followed by an ordinary cap row. -/
def weightedContentCapBoundaryValue (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r : ℕ) (j : Fin (contentCapCount D cutoff i β)) (b : M.obj w.obj) :=
  (capDotRow (T) (truncatedDot_supernatural D Sc cutoff N i) M r).total w.obj
    (((weightedContentLocalInverseTo D Sc cutoff N i M β hh).g' j.val).total w b)

/-- Evaluation of the specified weighted unit boundary is the raw represented boundary. -/
theorem weightedContentUnitBoundaryValue_atWord (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (j : Fin (contentUnitCount D cutoff i (w.word : Multiset I))) (r : ℕ) (b : (RM).obj w) :
    weightedContentUnitBoundaryValue D Sc cutoff N i M (w.word : Multiset I) hh
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) j r b =
    (RM).map (positiveKernelBoundary D Sc cutoff i w w hh j r (𝟙 w)) b := by
  unfold weightedContentUnitBoundaryValue
  rw [← weightedUnitColumnValue_compare D Sc cutoff N i M w r b]
  rw [weightedContentUnitWindow_chart D Sc cutoff N i M w hh]
  have h := positiveKernelBoundary_evaluate D Sc cutoff RM i w w hh j r (𝟙 w) b
  have hi : (RM).map (𝟙 w) b = b :=
    congrArg (fun f : (RM).obj w ⟶ (RM).obj w => f b) ((RM).toFunctor.map_id w)
  rw [hi] at h
  exact h.symm

/-- Evaluation of the specified weighted cap boundary is the raw represented boundary. -/
theorem weightedContentCapBoundaryValue_atWord (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0)
    (r : ℕ) (j : Fin (contentCapCount D cutoff i (w.word : Multiset I))) (b : (RM).obj w) :
    weightedContentCapBoundaryValue D Sc cutoff N i M (w.word : Multiset I) hh
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) r j b =
    (RM).map (negativeKernelBoundary D Sc cutoff i w w hh r j (𝟙 w)) b := by
  unfold weightedContentCapBoundaryValue
  rw [weightedContentCapWindow_chart D Sc cutoff N i M w hh]
  rw [← weightedCapRowValue_compare D Sc cutoff N i M w r]
  have h := negativeKernelBoundary_evaluate D Sc cutoff RM i w w hh r j (𝟙 w) b
  have hi : (RM).map (𝟙 w) b = b :=
    congrArg (fun f : (RM).obj w ⟶ (RM).obj w => f b) ((RM).toFunctor.map_id w)
  rw [hi] at h
  exact h.symm

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

end OddMath.QuiverHecke.ELVOld
