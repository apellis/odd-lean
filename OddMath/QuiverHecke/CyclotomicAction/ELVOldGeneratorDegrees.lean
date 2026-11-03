import OddMath.QuiverHecke.CyclotomicAction.ELVOldCategoryGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendDegree

/-! # Integer degrees of the chosen old append generators

The represented finite matrix uses the prescribed appended dot and
equal-colour crossing. Their degrees here are inherited from the source
diagrams, independently of their super parity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The prescribed last dot has integer degree `2 dᵢ`. -/
theorem oldAppendDotComponent_degree (i : I) (s : OldCategory D Sc cutoff) :
    CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i s ∈
      oldDegree D sy Sc hc cutoff (s.word ++ [i]) (s.word ++ [i]) (2 * sy.d i) := by
  apply Submodule.mem_map_of_mem
  apply appendComponent_mem_degree
  unfold dotE genE
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_gdeg_mkD]
    simp [pl, PG.ld, gdeg]
  · exact Submodule.zero_mem _

/-- The prescribed last equal crossing has integer degree `-2 dᵢ`. -/
theorem equalCrossComponent_degree (i : I) (s : OldCategory D Sc cutoff) :
    CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ∈
      oldDegree D sy Sc hc cutoff ((s.word ++ [i]) ++ [i]) ((s.word ++ [i]) ++ [i])
        (-2 * sy.d i) := by
  apply Submodule.mem_map_of_mem
  apply affineUnit_mem_degree D Sc cutoff sy hc
  unfold crossLast cl
  apply Presentation.diag_mem_homDeg'
  rw [degree_gdeg_mkD]
  simp [pl, PG.ld, gdeg, SKM.Datum.d_self]
  ring

end OddMath.QuiverHecke.ELVOld
