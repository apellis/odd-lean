/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCategoryCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedNilpotenceOver

/-!
# Coefficient image on exact-content ELV supermodules over a graded base ring

Over a commutative `K`-algebra `R` graded by `𝒜`, central families on the exact-content source
category are graded by the degree of their components in the truncated quotient over `K`
(`ELVOld.contentCoefficientDegreeOver`). Their images on the exact-content module category form
a coefficient grading (`ELVOld.contentModuleCoeffGradingOver`). If `𝒜` lives in degrees
`0, …, b` and there are finitely many colours, bounded degree support of the source category
(`ELVOld.contentCategory_end_boundedOver`) makes every coefficient of high degree vanish, so
these coefficients generate a jointly nilpotent coefficient ideal
(`ELVOld.contentModuleCoefficientIdealOver`).

For `K = R` with the trivial grading these are the constructions of
`OddMath.QuiverHecke.CyclotomicAction.ELVCategoryCoefficients`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams Supercategory OddMath.Diagrams

namespace OddMath.QuiverHecke.ELVOld

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

theorem id_mem_truncatedDegreeOver (v : TruncatedCategory D Sc cutoff N) :
    𝟙 v ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v v 0 := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := Supercategory.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := truncatedGradedSupercategoryOver D sy 𝒜 Sc hP cutoff N
  exact GradedSupercategory.id_mem_degree (R := K) v

theorem comp_mem_truncatedDegreeOver {u v w : TruncatedCategory D Sc cutoff N} {m n : ℤ}
    {f : u ⟶ v} {g : v ⟶ w} (hf : f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N u v m)
    (hg : g ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w n) :
    f ≫ g ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N u w (m + n) := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := Supercategory.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := truncatedGradedSupercategoryOver D sy 𝒜 Sc hP cutoff N
  exact GradedSupercategory.comp_mem_degree (R := K) hf hg

variable (β : Multiset I)

/-- Integer degrees of source central families over a graded base: every component lies in the
given degree of the truncated quotient. -/
def contentCoefficientDegreeOver (n : ℤ) : Set (ContentCoefficient D Sc cutoff N β) :=
  {c | ∀ (p : ZMod 2) (v : ContentCategory D Sc cutoff N β),
    c.app p v ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v.obj v.obj n}

/-- The image of the source coefficient degree on the exact-content module target, over a
graded base. -/
def contentModuleCoeffGradingOver :
    SwappedAssembly.ProbeWindow.CoeffGrading R (contentModuleTarget D Sc cutoff N β) where
  deg n := {t | ∃ c ∈ contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N β n,
    contentRealize D Sc cutoff N β c = t}
  id_mem := by
    refine ⟨_, ?_, contentRealize_id D Sc cutoff N β⟩
    intro p v
    change (if p = 0 then 𝟙 v else 0) ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v.obj v.obj 0
    split_ifs
    · exact id_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v.obj
    · exact Submodule.zero_mem _
  comp_mem := by
    rintro m n x y ⟨c, hc', rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨c ≫ d, ?_, contentRealize_comp D Sc cutoff N β c d⟩
    intro p v
    change (c ≫ d).app p v ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v.obj v.obj (m + n)
    rw [Superfunctor.comp_app]
    exact Submodule.add_mem _
      (comp_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N (hc' 0 v) (hd p v))
      (comp_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N (hc' 1 v) (hd _ v))
  proj_mem := by
    rintro n p x ⟨c, hc', rfl⟩
    refine ⟨proj R p c, ?_, contentRealize_proj D Sc cutoff N β p c⟩
    intro q v
    change (proj R p c).app q v ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v.obj v.obj n
    rw [Superfunctor.proj_app]
    split_ifs
    · exact hc' _ v
    · exact Submodule.zero_mem _

/-- One degree threshold for all words of the fixed content, over a base ring graded in degrees
`0, …, b`. -/
theorem contentCategory_end_boundedOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) :
    ∃ B : ℕ, ∀ (v : ContentCategory D Sc cutoff N β) (n : ℤ), (B : ℤ) ≤ n →
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v.obj v.obj n = ⊥ := by
  classical
  choose B hB using fun v : List I =>
    truncatedContent_boundedOver D sy 𝒜 Sc hP cutoff N b h𝒜 v v
  let S := β.toList.permutations.toFinset
  refine ⟨S.sup B + 1, fun v n hn => hB v.obj.word n (Or.inr ?_)⟩
  have hv : v.obj.word ∈ S := by
    change v.obj.word ∈ β.toList.permutations.toFinset
    simp only [List.mem_toFinset, List.mem_permutations]
    apply Multiset.coe_eq_coe.mp
    exact v.content.trans (Multiset.coe_toList β).symm
  have hle := Finset.le_sup (f := B) hv
  have hle' : (B v.obj.word : ℤ) ≤ ((S.sup B : ℕ) : ℤ) := by exact_mod_cast hle
  omega

/-- Source support annihilates every high-degree central family simultaneously, over a graded
base. -/
theorem contentCoefficient_eq_zeroOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (n : ℤ)
    (hn : ((contentCategory_end_boundedOver D sy 𝒜 Sc hP cutoff N β b h𝒜).choose : ℤ) ≤ n)
    (c : ContentCoefficient D Sc cutoff N β)
    (h : c ∈ contentCoefficientDegreeOver D sy 𝒜 Sc hP cutoff N β n) : c = 0 := by
  apply Superfunctor.hom_ext
  intro p v
  have hv := h p v
  rw [(contentCategory_end_boundedOver D sy 𝒜 Sc hP cutoff N β b h𝒜).choose_spec v n hn] at hv
  exact (Submodule.mem_bot _).mp hv

/-- High-degree coefficients vanish on the exact-content module category, over a graded base. -/
theorem contentModule_coefficient_eq_zeroOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (n : ℤ)
    (hn : ((contentCategory_end_boundedOver D sy 𝒜 Sc hP cutoff N β b h𝒜).choose : ℤ) ≤ n)
    (t : 𝟙 (contentModuleTarget D Sc cutoff N β) ⟶ 𝟙 (contentModuleTarget D Sc cutoff N β))
    (ht : t ∈ (contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β).deg n) : t = 0 := by
  obtain ⟨c, hc', rfl⟩ := ht
  rw [contentCoefficient_eq_zeroOver D sy 𝒜 Sc hP cutoff N β b h𝒜 n hn c hc']
  exact (contentRealizeLinear D Sc cutoff N β).map_zero

/-- Jointly nilpotent coefficient ideal on functors into the exact-content module category,
over a base ring graded in degrees `0, …, b`. -/
def contentModuleCoefficientIdealOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (T : PiSCat R) :
    SwappedAssembly.ProbeWindow.CoefficientIdeal (T ⟶ contentModuleTarget D Sc cutoff N β) :=
  SwappedAssembly.ProbeWindow.reservoirCoefficientIdeal T
    (contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β)
    (contentCategory_end_boundedOver D sy 𝒜 Sc hP cutoff N β b h𝒜).choose
    (contentModule_coefficient_eq_zeroOver D sy 𝒜 Sc hP cutoff N β b h𝒜)

end OddMath.QuiverHecke.ELVOld
