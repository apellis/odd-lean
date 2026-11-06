/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldGradingOver
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedCategory

/-!
# Grading of the coefficient-truncated quotient over a graded base ring

Let `R` be a commutative `K`-algebra graded by `𝒜`, with a coefficient-graded homogeneous quiver
Hecke presentation over `R`. The coefficient truncation ideal is homogeneous for the grading
`QuiverHecke.elvHomGradingOver` (`ELVOld.truncatedIdeal_dproj_mem_over`), so the
coefficient-truncated quotient category is a graded supercategory over `K`
(`ELVOld.truncatedGradedSupercategoryOver`): the degree parts are the images of the degree parts
of the ELV coefficient category, and the degree projections descend as additive maps.

For `K = R` with the trivial grading this is `ELVOld.truncatedGradedSupercategory`.
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
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

/-- A coefficient basis vector at a word identity has its coefficient degree, over a graded
base. -/
theorem coefficientIdentity_basis_degreeOver (t : List I) (a : SKM.SYM.CoefficientIndex D) :
    coefficientIdentity D Sc cutoff t (SKM.SYM.coefficientBasis D R a) ∈
      elvHomDegreeOver D sy 𝒜 Sc hP cutoff t t (SKM.SYM.coefficientDegree D sy a) := by
  letI := Linear.restrictScalars K R (H D Sc)
  letI := Supercategory.restrictScalars K R (H D Sc)
  letI := quiverHeckeGradingOver D sy 𝒜 Sc hP
  have ha := SKM.SYM.coefficientBasis_mem_over (sy := sy) (𝒜 := 𝒜) a
  have hi : (𝟙 ((pres D Sc).obj (ob D t))) ∈
      GradedSupercategory.degree (R := K) ((pres D Sc).obj (ob D t)) ((pres D Sc).obj (ob D t))
        0 :=
    GradedSupercategory.id_mem_degree _
  have h := elvQuotientMap_source_mem_degreeOver D sy 𝒜 Sc hP cutoff ha hi
  rw [elvQuotientMap_source, add_zero] at h
  exact h

/-- The coefficient truncation ideal is stable under the degree projections over `K`. -/
theorem coefficientHomIdeal_dproj_mem_over {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ coefficientHomIdeal D Sc cutoff N v w) (n : ℤ) :
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
    dproj K n f ∈ coefficientHomIdeal D Sc cutoff N v w := by
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  let S : Set (hom D Sc cutoff v w) := {f | ∃ t a, N ≤ SKM.SYM.coefficientWeight D a ∧
    ∃ l : hom D Sc cutoff v t, ∃ r : hom D Sc cutoff t w,
      l ≫ coefficientIdentity D Sc cutoff t (SKM.SYM.coefficientBasis D R a) ≫ r = f}
  letI := degreeDecomposition K (obj D Sc cutoff v) (obj D Sc cutoff w)
  rw [dproj_apply]
  refine BasisGrading.decompose_mem_span 𝒜
    (GradedSupercategory.degree (R := K) (obj D Sc cutoff v) (obj D Sc cutoff w))
    (fun hr hy => smul_mem_elvHomDegreeOver D sy 𝒜 Sc hP cutoff hr hy) (S := S)
    ?_ hf n
  rintro g ⟨t, c, hcw, a, b, rfl⟩ m
  rw [← dproj_apply]
  refine induction_on_degree (R := K) a (by simp) (fun r a ha => ?_)
    (fun a a' ha ha' => ?_)
  · refine induction_on_degree (R := K) b (by simp) (fun s b hb => ?_)
      (fun b b' hb hb' => ?_)
    · have hg := comp_mem_degree ha
        (comp_mem_degree (coefficientIdentity_basis_degreeOver D sy 𝒜 Sc hP cutoff t c) hb)
      by_cases h : r + (SKM.SYM.coefficientDegree D sy c + s) = m
      · rw [← h, dproj_of_mem hg]
        exact Submodule.subset_span ⟨t, c, hcw, a, b, rfl⟩
      · rw [dproj_of_mem_ne hg h]
        exact Submodule.zero_mem _
    · simpa only [Preadditive.comp_add, map_add] using Submodule.add_mem _ hb hb'
  · simpa only [Preadditive.add_comp, map_add] using Submodule.add_mem _ ha ha'

/-- The truncation ideal (old relations and coefficient truncation) is stable under the degree
projections over `K`. -/
theorem truncatedIdeal_dproj_mem_over {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ truncatedIdeal D Sc cutoff N v w) (n : ℤ) :
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
    dproj K n f ∈ truncatedIdeal D Sc cutoff N v w := by
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  obtain ⟨f, hf₁, g, hg, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨_, ideal_dproj_mem_over D sy 𝒜 Sc hP cutoff hf₁ n,
    _, coefficientHomIdeal_dproj_mem_over D sy 𝒜 Sc hP cutoff N hg n, rfl⟩

/-- The degree projection on the truncated quotient over a graded base, as an additive map. -/
def truncatedDprojOver (v w : List I) (n : ℤ) :
    TruncatedOld D Sc cutoff N v w →+ TruncatedOld D Sc cutoff N v w :=
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  QuotientAddGroup.map (truncatedIdeal D Sc cutoff N v w).toAddSubgroup
    (truncatedIdeal D Sc cutoff N v w).toAddSubgroup (dproj K n).toAddMonoidHom
    (fun _ hf => truncatedIdeal_dproj_mem_over D sy 𝒜 Sc hP cutoff N hf n)

theorem truncatedDprojOver_mk (v w : List I) (n : ℤ) (f : hom D Sc cutoff v w) :
    truncatedDprojOver D sy 𝒜 Sc hP cutoff N v w n ((truncatedIdeal D Sc cutoff N v w).mkQ f) =
      (truncatedIdeal D Sc cutoff N v w).mkQ
        (letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
        letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
        letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
        dproj K n f) :=
  rfl

/-- The degree-`n` part of a Hom module of the truncated quotient over a graded base. -/
def truncatedDegreeOver (v w : TruncatedCategory D Sc cutoff N) (n : ℤ) :
    letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
    Submodule K (v ⟶ w) :=
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  { carrier := {f | ∃ a ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v.word w.word n,
      (truncatedIdeal D Sc cutoff N v.word w.word).mkQ a = f}
    add_mem' := by
      rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, add_mem ha hb, map_add _ a b⟩
    zero_mem' := ⟨0, zero_mem _, map_zero _⟩
    smul_mem' := by
      rintro c _ ⟨a, ha, rfl⟩
      refine ⟨algebraMap K R c • a, ?_, map_smul _ _ a⟩
      simpa using smul_mem_elvHomDegreeOver D sy 𝒜 Sc hP cutoff
        (SetLike.algebraMap_mem_graded 𝒜 c) ha }

theorem mkQ_mem_truncatedDegreeOver {v w : TruncatedCategory D Sc cutoff N} {n : ℤ}
    {a : hom D Sc cutoff v.word w.word}
    (ha : a ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v.word w.word n) :
    ((truncatedIdeal D Sc cutoff N v.word w.word).mkQ a : v ⟶ w) ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w n :=
  ⟨a, ha, rfl⟩

/-- Homogeneous scalars of the base shift degrees in the truncated quotient. -/
theorem smul_mem_truncatedDegreeOver {v w : TruncatedCategory D Sc cutoff N} {e n : ℤ} {r : R}
    {f : v ⟶ w} (hr : r ∈ 𝒜 e) (hf : f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w n) :
    r • f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w (e + n) := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact ⟨r • a, smul_mem_elvHomDegreeOver D sy 𝒜 Sc hP cutoff hr ha, map_smul _ r a⟩

theorem truncatedDprojOver_of_mem {v w : TruncatedCategory D Sc cutoff N} {m : ℤ} {f : v ⟶ w}
    (hf : f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w m) (n : ℤ) :
    truncatedDprojOver D sy 𝒜 Sc hP cutoff N v.word w.word n f = if m = n then f else 0 := by
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  obtain ⟨a, ha, rfl⟩ := hf
  rw [truncatedDprojOver_mk]
  split_ifs with h
  · subst n
    rw [dproj_of_mem ha]
  · rw [dproj_of_mem_ne ha h, map_zero]

/-- The degree parts of the truncated quotient over a graded base form an internal direct
sum. -/
theorem truncatedDegreeOver_internal (v w : TruncatedCategory D Sc cutoff N) :
    letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
    DirectSum.IsInternal (truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w) := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s f hf he n hn
    have hh := congrArg (truncatedDprojOver D sy 𝒜 Sc hP cutoff N v.word w.word n) he
    rw [map_sum, map_zero] at hh
    have hsum : (∑ i ∈ s, truncatedDprojOver D sy 𝒜 Sc hP cutoff N v.word w.word n (f i)) =
        f n := by
      calc
        _ = ∑ i ∈ s, if i = n then f i else 0 :=
          Finset.sum_congr rfl
            (fun i hi => truncatedDprojOver_of_mem D sy 𝒜 Sc hP cutoff N (hf i hi) n)
        _ = f n := by simp [hn]
    exact hsum.symm.trans hh
  · classical
    refine Submodule.eq_top_iff'.2 fun f => ?_
    obtain ⟨a, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word w.word).mkQ_surjective f
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
    letI := degreeDecomposition K (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)
    rw [← DirectSum.sum_support_decompose
      (GradedSupercategory.degree (R := K) (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)) a,
      map_sum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
        (DirectSum.decompose (GradedSupercategory.degree (R := K) (obj D Sc cutoff v.word)
          (obj D Sc cutoff w.word)) a i).2)

/-- **The coefficient-truncated quotient over a graded base is a graded supercategory over
`K`.** -/
@[instance_reducible]
def truncatedGradedSupercategoryOver :
    letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
    letI := Supercategory.restrictScalars K R (TruncatedCategory D Sc cutoff N)
    GradedSupercategory K (TruncatedCategory D Sc cutoff N) :=
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := Supercategory.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  { degree := truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
    isInternal_degree := truncatedDegreeOver_internal D sy 𝒜 Sc hP cutoff N
    proj_mem_degree := by
      rintro v w n _ p ⟨a, ha, rfl⟩
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      rw [BoxProdCoefficient.proj_eq_proj (R := R)
          (fun _ _ _ _ => Iff.rfl),
        truncatedCategory_proj, truncatedProj_mk]
      refine mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ?_
      rw [← BoxProdCoefficient.proj_eq_proj (K := K)
        (fun _ _ _ _ => Iff.rfl)]
      exact proj_mem_degree p ha
    id_mem_degree := fun v => by
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      exact mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
        (id_mem_degree (R := K) (obj D Sc cutoff v.word))
    comp_mem_degree := by
      rintro v t w m n _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      exact mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N (comp_mem_degree ha hb) }

end OddMath.QuiverHecke.ELVOld
