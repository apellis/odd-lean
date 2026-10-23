/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.FiniteType

/-!
# Injectivity from a degreewise comparison of bases

Over a commutative ring, a surjective linear map from a free module with a graded basis onto a
free module with a graded basis indexed by the same set is injective, provided the map is
graded and each degree contains finitely many basis vectors
(`injective_of_surjective_of_basis`). In each degree this is a surjective endomorphism of a
finitely generated module, hence injective by Orzech's theorem. This is the counting step
comparing the Brundan–Ellis family of Theorem 8.1 (arXiv:1701.04133v2) with the Khovanov–Lauda
basis (KL III, arXiv:0807.3250, Theorem 1.2 and §6.4) for even data.
-/

namespace OddMath.SKM.EvenBridge

open Module

variable {R : Type*} [CommRing R] {J ι : Type*}

/-- A surjective endomorphism of the free module on `J` which maps each basis vector into the
span of the basis vectors of the same degree is injective, when the degrees have finite
fibres. -/
theorem injective_of_surjective_of_mem_supported (φ : (J →₀ R) →ₗ[R] (J →₀ R))
    (hφ : Function.Surjective φ) (deg : J → ι)
    (hdeg : ∀ j, φ (Finsupp.single j 1) ∈ Finsupp.supported R R {i | deg i = deg j})
    (hfin : ∀ d, Finite {j // deg j = d}) : Function.Injective φ := by
  classical
  let V : ι → Submodule R (J →₀ R) := fun d => Finsupp.supported R R {j | deg j = d}
  have hfilt : ∀ d (y : J →₀ R), y ∈ V d → y.filter (fun j => deg j = d) = y :=
    fun d y hy => (Finsupp.filter_eq_self_iff _ _).2 fun j hj => hy (Finsupp.mem_support_iff.2 hj)
  have hfilt0 : ∀ d e (y : J →₀ R), y ∈ V e → e ≠ d → y.filter (fun j => deg j = d) = 0 := by
    intro d e y hy hne
    ext j
    by_cases h : deg j = d
    · rw [Finsupp.filter_apply_pos (fun i => deg i = d) y h, Finsupp.coe_zero, Pi.zero_apply]
      by_contra h0
      exact hne ((hy (Finsupp.mem_support_iff.2 h0) : deg j = e).symm.trans h)
    · rw [Finsupp.filter_apply_neg (fun i => deg i = d) y h]
      rfl
  have hmem : ∀ d (x : J →₀ R), x.filter (fun j => deg j = d) ∈ V d := by
    intro d x j hj
    rw [Finset.mem_coe, Finsupp.support_filter] at hj
    exact (Finset.mem_filter.1 hj).2
  have hcomm : ∀ d x, (φ x).filter (fun j => deg j = d) = φ (x.filter (fun j => deg j = d)) := by
    intro d x
    induction x using Finsupp.induction_linear with
    | zero => rw [Finsupp.filter_zero, map_zero, Finsupp.filter_zero]
    | add x y hx hy => rw [map_add, Finsupp.filter_add, hx, hy, Finsupp.filter_add, map_add]
    | single j c =>
      have hm : φ (Finsupp.single j c) ∈ V (deg j) := by
        rw [show Finsupp.single j c = c • Finsupp.single j 1 by simp, map_smul]
        exact Submodule.smul_mem _ _ (hdeg j)
      by_cases h : deg j = d
      · rw [Finsupp.filter_single_of_pos (fun i => deg i = d) h]
        subst h
        exact hfilt _ _ hm
      · rw [Finsupp.filter_single_of_neg (fun i => deg i = d) h, map_zero, hfilt0 d (deg j) _ hm h]
  have hV : ∀ d x, x ∈ V d → φ x ∈ V d := by
    intro d x hx
    rw [← hfilt d x hx, ← hcomm]
    exact hmem d _
  have hblock : ∀ d, Function.Injective ((φ.restrict (hV d)) : V d →ₗ[R] V d) := by
    intro d
    have : Finite {j | deg j = d} := hfin d
    have : Module.Finite R (V d) :=
      Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := R) (R := R) {j | deg j = d}).symm
    refine OrzechProperty.injective_of_surjective_endomorphism _ ?_
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hφ y
    refine ⟨⟨_, hmem d x⟩, Subtype.ext ?_⟩
    rw [LinearMap.coe_restrict_apply, ← hcomm, hx, hfilt d y hy]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  ext j
  have h1 := hcomm (deg j) x
  rw [hx, Finsupp.filter_zero] at h1
  have h2 : (⟨_, hmem (deg j) x⟩ : V (deg j)) = 0 :=
    hblock (deg j) (Subtype.ext (by rw [LinearMap.coe_restrict_apply, ← h1, map_zero]; rfl))
  have h3 := congrArg (fun z : V (deg j) => (z : J →₀ R) j) h2
  rwa [Finsupp.filter_apply_pos (fun i => deg i = deg j) x rfl] at h3

/-- The coordinates of a homogeneous vector in a basis of homogeneous vectors vanish outside its
degree, for an independent family of submodules. -/
theorem repr_mem_supported {W : Type*} [AddCommGroup W] [Module R W] (p : ι → Submodule R W)
    (hp : iSupIndep p) (b : Basis J R W) (deg : J → ι) (hb : ∀ j, b j ∈ p (deg j)) {d : ι}
    {w : W} (hw : w ∈ p d) : b.repr w ∈ Finsupp.supported R R {j | deg j = d} := by
  classical
  have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero p).1 hp
  set x := b.repr w
  let we : ι → W := fun e => b.repr.symm (x.filter fun j => deg j = e)
  have hwe : ∀ e, we e ∈ p e := by
    intro e
    simp only [we, Basis.repr_symm_apply, Finsupp.linearCombination_apply]
    refine Submodule.finsuppSum_mem _ _ _ _ fun j hj => Submodule.smul_mem _ _ ?_
    have he : deg j = e := by
      by_contra h
      exact hj (Finsupp.filter_apply_neg (fun i => deg i = e) x h)
    exact he ▸ hb j
  let t := insert d (x.support.image deg)
  have hsum : ∑ e ∈ t, (x.filter fun j => deg j = e) = x := by
    ext j
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.filter_apply]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra h0
      exact h (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
        (Finsupp.mem_support_iff.2 (Ne.symm h0))))
  let v : ι → W := fun e => we e - if e = d then w else 0
  have hv : ∀ e ∈ t, v e ∈ p e := by
    intro e _
    refine Submodule.sub_mem _ (hwe e) ?_
    split_ifs with h
    · exact h ▸ hw
    · exact Submodule.zero_mem _
  have hvs : ∑ e ∈ t, v e = 0 := by
    simp only [v, we]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' t d, ← map_sum, hsum,
      ite_eq_left (Finset.mem_insert_self _ _), LinearEquiv.symm_apply_apply, sub_self]
  intro j hj
  rw [Finset.mem_coe, Finsupp.mem_support_iff] at hj
  by_contra hne
  have hjt : deg j ∈ t := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
    (Finsupp.mem_support_iff.2 hj))
  have h0 := hind t v hv hvs (deg j) hjt
  simp only [v, ite_eq_right (show ¬deg j = d from hne), sub_zero, we,
    LinearEquiv.map_eq_zero_iff] at h0
  have := congrArg (fun z : J →₀ R => z j) h0
  simp at this
  exact hj this

/-- **Injectivity from a degreewise comparison of bases.** Let `f` be a surjective linear map
from the free module on `J` to `W`, sending the basis vector `j` into the piece `p (deg j)` of an
independent family of submodules, and let `b` be a basis of `W`, indexed by `J`, with
`b j ∈ p (deg j)`. If the fibres of `deg` are finite, then `f` is injective. -/
theorem injective_of_surjective_of_basis {W : Type*} [AddCommGroup W] [Module R W]
    (f : (J →₀ R) →ₗ[R] W) (hf : Function.Surjective f) (p : ι → Submodule R W)
    (hp : iSupIndep p) (deg : J → ι) (hdeg : ∀ j, f (Finsupp.single j 1) ∈ p (deg j))
    (b : Basis J R W) (hb : ∀ j, b j ∈ p (deg j)) (hfin : ∀ d, Finite {j // deg j = d}) :
    Function.Injective f := by
  have h := injective_of_surjective_of_mem_supported (b.repr.toLinearMap ∘ₗ f)
    (b.repr.surjective.comp hf) deg (fun j => repr_mem_supported p hp b deg hb (hdeg j)) hfin
  exact fun x y hxy => h (by simp [hxy])

end OddMath.SKM.EvenBridge
