/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Gradings of quotients by homogeneous ideals

Let `𝒜` grade a `K`-algebra `R` and let `f : R →ₐ[K] R'` be surjective with homogeneous
kernel. The images `f (𝒜 i)` grade `R'`. This grades the truncations `K[h]/(h^N)` of the Rees
ring, with `h` in degree one, needed for the graded quiver Hecke supercategory over them
(route step 2 of `docs/Nondegeneracy/Phase2Plan.md`).

## Main definitions and results

* `GradedImage.image 𝒜 f i`: the image of `𝒜 i`.
* `GradedImage.iSupIndep_image`, `GradedImage.iSup_image`: the images are independent and
  span `R'`.
* `GradedImage.gradedAlgebra`: the resulting graded algebra structure on `R'`.
-/

noncomputable section

namespace OddMath.SKM.GradedImage

open DirectSum

variable {ι K R R' : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing K] [CommRing R]
  [CommRing R'] [Algebra K R] [Algebra K R'] (𝒜 : ι → Submodule K R) [GradedAlgebra 𝒜]
  (f : R →ₐ[K] R')

/-- The image of the degree-`i` part. -/
def image (i : ι) : Submodule K R' := (𝒜 i).map f.toLinearMap

variable {𝒜 f}

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
theorem map_mem_image {i : ι} {x : R} (hx : x ∈ 𝒜 i) : f x ∈ image 𝒜 f i :=
  ⟨x, hx, rfl⟩

variable (𝒜 f)

theorem gradedMonoid : SetLike.GradedMonoid (image 𝒜 f) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one f⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, map_mul f a b⟩

/-- For surjective `f`, the images span. -/
theorem iSup_image (hf : Function.Surjective f) : ⨆ i, image 𝒜 f i = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := hf y
  rw [← DirectSum.sum_support_decompose 𝒜 x, map_sum]
  exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i (map_mem_image (SetLike.coe_mem _))

variable {𝒜} in
theorem decompose_eq_zero_of_mem_iSup {d : ι} {z : R} (hz : z ∈ ⨆ (e) (_ : e ≠ d), 𝒜 e) :
    (decompose 𝒜 z d : R) = 0 := by
  refine Submodule.iSup_induction _ (motive := fun z => (decompose 𝒜 z d : R) = 0) hz
    (fun e z hz => ?_) (by simp) (fun a b ha hb => by simp [ha, hb])
  refine Submodule.iSup_induction _ (motive := fun z => (decompose 𝒜 z d : R) = 0) hz
    (fun he z hz => decompose_of_mem_ne 𝒜 hz he) (by simp)
    (fun a b ha hb => by simp [ha, hb])

/-- For homogeneous kernel, the images are independent. -/
theorem iSupIndep_image (hI : (RingHom.ker f).IsHomogeneous 𝒜) : iSupIndep (image 𝒜 f) := by
  intro d
  rw [Submodule.disjoint_def]
  rintro y ⟨x, hx, rfl⟩ hy
  have hy' : f.toLinearMap x ∈ (⨆ (e) (_ : e ≠ d), 𝒜 e).map f.toLinearMap := by
    simpa only [Submodule.map_iSup, image] using hy
  obtain ⟨z, hz, hzx⟩ := hy'
  have hker : x - z ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact hzx.symm
  have h := (Ideal.IsHomogeneous.mem_iff 𝒜 hI).mp hker d
  rw [decompose_sub, DirectSum.sub_apply, Submodule.coe_sub, decompose_of_mem_same 𝒜 hx,
    decompose_eq_zero_of_mem_iSup hz, sub_zero] at h
  exact (RingHom.mem_ker.mp h : f x = 0)

theorem isInternal_image (hf : Function.Surjective f) (hI : (RingHom.ker f).IsHomogeneous 𝒜) :
    DirectSum.IsInternal (image 𝒜 f) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_image 𝒜 f hI)
    (iSup_image 𝒜 f hf)

/-- The graded algebra structure on the target of a surjection with homogeneous kernel. -/
@[instance_reducible]
def gradedAlgebra (hf : Function.Surjective f) (hI : (RingHom.ker f).IsHomogeneous 𝒜) :
    GradedAlgebra (image 𝒜 f) :=
  { gradedMonoid 𝒜 f, (isInternal_image 𝒜 f hf hI).chooseDecomposition with }

end OddMath.SKM.GradedImage
