/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldGradingOver
import OddMath.QuiverHecke.CyclotomicAction.ELVOldGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules

/-!
# Grading of the old cyclotomic quotient over a graded base ring

Let `R` be a commutative `K`-algebra graded by `𝒜`, with a coefficient-graded homogeneous quiver
Hecke presentation over `R`. The old cyclotomic ideal is homogeneous for the grading
`QuiverHecke.elvHomGradingOver` (`ELVOld.ideal_dproj_mem_over`), so the old quotient category is
a graded supercategory over `K` (`ELVOld.oldCategoryGradedSupercategoryOver`): the degree parts
are the images of the degree parts of the ELV coefficient category, and the degree projections
descend to the quotient as additive maps.

For `K = R` with the trivial grading this is `ELVOld.oldCategoryGradedSupercategory`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams GradedSupercategory

namespace OddMath.QuiverHecke.ELVOld

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ)

/-- The degree projection on the old quotient over a graded base, as an additive map. -/
def oldDprojOver (v w : List I) (n : ℤ) : Old D Sc cutoff v w →+ Old D Sc cutoff v w :=
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  QuotientAddGroup.map (ideal D Sc cutoff v w).toAddSubgroup
    (ideal D Sc cutoff v w).toAddSubgroup (dproj K n).toAddMonoidHom
    (fun _ hf => ideal_dproj_mem_over D sy 𝒜 Sc hP cutoff hf n)

theorem oldDprojOver_mk (v w : List I) (n : ℤ) (f : hom D Sc cutoff v w) :
    oldDprojOver D sy 𝒜 Sc hP cutoff v w n ((ideal D Sc cutoff v w).mkQ f) =
      (ideal D Sc cutoff v w).mkQ
        (letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
        letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
        letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
        dproj K n f) :=
  rfl

/-- The degree-`n` part of a Hom module of the old quotient category over a graded base. -/
def oldDegreeOver (v w : OldCategory D Sc cutoff) (n : ℤ) :
    letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
    Submodule K (v ⟶ w) :=
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  { carrier := {f | ∃ a ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v.word w.word n,
      (ideal D Sc cutoff v.word w.word).mkQ a = f}
    add_mem' := by
      rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, add_mem ha hb, map_add _ a b⟩
    zero_mem' := ⟨0, zero_mem _, map_zero _⟩
    smul_mem' := by
      rintro c _ ⟨a, ha, rfl⟩
      refine ⟨algebraMap K R c • a, ?_, map_smul _ _ a⟩
      simpa using smul_mem_elvHomDegreeOver D sy 𝒜 Sc hP cutoff
        (SetLike.algebraMap_mem_graded 𝒜 c) ha }

theorem mkQ_mem_oldDegreeOver {v w : OldCategory D Sc cutoff} {n : ℤ}
    {a : hom D Sc cutoff v.word w.word} (ha : a ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v.word w.word n) :
    ((ideal D Sc cutoff v.word w.word).mkQ a : v ⟶ w) ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w n :=
  ⟨a, ha, rfl⟩

theorem oldDprojOver_of_mem {v w : OldCategory D Sc cutoff} {m : ℤ} {f : v ⟶ w}
    (hf : f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w m) (n : ℤ) :
    oldDprojOver D sy 𝒜 Sc hP cutoff v.word w.word n f = if m = n then f else 0 := by
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  obtain ⟨a, ha, rfl⟩ := hf
  rw [oldDprojOver_mk]
  split_ifs with h
  · subst n
    rw [dproj_of_mem ha]
  · rw [dproj_of_mem_ne ha h, map_zero]

/-- The degree parts of the old quotient over a graded base form an internal direct sum. -/
theorem oldDegreeOver_internal (v w : OldCategory D Sc cutoff) :
    letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
    DirectSum.IsInternal (oldDegreeOver D sy 𝒜 Sc hP cutoff v w) := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s f hf he n hn
    have hh := congrArg (oldDprojOver D sy 𝒜 Sc hP cutoff v.word w.word n) he
    rw [map_sum, map_zero] at hh
    have hsum : (∑ i ∈ s, oldDprojOver D sy 𝒜 Sc hP cutoff v.word w.word n (f i)) = f n := by
      calc
        _ = ∑ i ∈ s, if i = n then f i else 0 :=
          Finset.sum_congr rfl (fun i hi => oldDprojOver_of_mem D sy 𝒜 Sc hP cutoff (hf i hi) n)
        _ = f n := by simp [hn]
    exact hsum.symm.trans hh
  · classical
    refine Submodule.eq_top_iff'.2 fun f => ?_
    obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
    letI := degreeDecomposition K (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)
    rw [← DirectSum.sum_support_decompose
      (GradedSupercategory.degree (R := K) (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)) a,
      map_sum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff
        (DirectSum.decompose (GradedSupercategory.degree (R := K) (obj D Sc cutoff v.word)
          (obj D Sc cutoff w.word)) a i).2)

/-- **The old quotient category over a graded base is a graded supercategory over `K`.** -/
@[instance_reducible]
def oldCategoryGradedSupercategoryOver :
    letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
    GradedSupercategory K (OldCategory D Sc cutoff) :=
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  { degree := oldDegreeOver D sy 𝒜 Sc hP cutoff
    isInternal_degree := oldDegreeOver_internal D sy 𝒜 Sc hP cutoff
    proj_mem_degree := by
      rintro v w n _ p ⟨a, ha, rfl⟩
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      rw [Supercategory.proj_restrictScalars K R (OldCategory D Sc cutoff),
        oldCategory_proj, oldProj_mk]
      refine mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff ?_
      rw [← Supercategory.proj_restrictScalars K R (ELVCoefficientCategory D Sc cutoff)]
      exact proj_mem_degree p ha
    id_mem_degree := fun v => by
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      exact mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff (id_mem_degree (R := K) (obj D Sc cutoff v.word))
    comp_mem_degree := by
      rintro v t w m n _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      exact mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff (comp_mem_degree ha hb) }

end OddMath.QuiverHecke.ELVOld
