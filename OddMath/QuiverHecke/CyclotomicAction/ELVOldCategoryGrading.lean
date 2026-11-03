import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendSuperfunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVOldGrading

/-! # Integer grading of the old coefficient category and chosen append

The represented kernels in the source-coefficient closure calculation
use the existing integer grading of the old cyclotomic quotient. This
packages that grading on the full old category and proves that the
chosen right append preserves it. No grading of arbitrary module Homs
is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The integer degree is exactly the old quotient image of the source
coefficient-diagram degree, independently of total super parity. -/
@[instance_reducible]
def oldCategoryGradedSupercategory : GradedSupercategory k (OldCategory D Sc cutoff) where
  degree v w := oldDegree D sy Sc hc cutoff v.word w.word
  isInternal_degree v w := oldDegree_internal D sy Sc hc cutoff v.word w.word
  proj_mem_degree := by
    intro v w n f p hf
    rw [oldCategory_proj]
    exact oldProj_mem_oldDegree D sy Sc hc cutoff p hf
  id_mem_degree v := by
    let _ := elvHomGrading D sy Sc hc cutoff
    exact Submodule.mem_map_of_mem (GradedSupercategory.id_mem_degree (obj D Sc cutoff v.word))
  comp_mem_degree := by
    rintro v t w m n f g ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    let _ := elvHomGrading D sy Sc hc cutoff
    exact Submodule.mem_map_of_mem (GradedSupercategory.comp_mem_degree ha hb)

/-- The prescribed append map preserves integer degree. -/
theorem oldAppend_mem_degree (i : I) {v w : OldCategory D Sc cutoff} {n : ℤ} {f : v ⟶ w}
    (hf : f ∈ oldDegree D sy Sc hc cutoff v.word w.word n) :
    (CyclotomicCrossingTensor.append D Sc cutoff i).map f ∈
      oldDegree D sy Sc hc cutoff (v.word ++ [i]) (w.word ++ [i]) n := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact Submodule.mem_map_of_mem (rightContext_mem_degree D Sc cutoff sy hc [i] ha)

/-- The selected old append is a graded superfunctor without any
additional generator-compatibility premise. -/
def oldAppendGraded (i : I) :
    letI := oldCategoryGradedSupercategory D Sc cutoff sy hc
    GradedSuperfunctor k (OldCategory D Sc cutoff) (OldCategory D Sc cutoff) := by
  letI := oldCategoryGradedSupercategory D Sc cutoff sy hc
  exact { toFunctor := CyclotomicCrossingTensor.append D Sc cutoff i
          isGraded := { map_mem_degree := oldAppend_mem_degree D Sc cutoff sy hc i } }

end OddMath.QuiverHecke.ELVOld
