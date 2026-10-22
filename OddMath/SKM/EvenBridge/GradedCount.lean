/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Injectivity from a degreewise count

A linear map from a free module with a graded basis onto a space with independent
finite-dimensional graded pieces is injective as soon as, in each degree, the number of basis
vectors equals the dimension of the corresponding piece
(`injective_of_surjective_of_card_eq_finrank`). This is the counting step comparing the
Brundan–Ellis family of Theorem 8.1 (arXiv:1701.04133v2) with the Khovanov–Lauda basis
(KL III, arXiv:0807.3250, Theorem 1.2) for even data.
-/

namespace OddMath.SKM.EvenBridge

open Module

variable {k : Type*} [Field k] {J ι W : Type*} [AddCommGroup W] [Module k W]

private theorem sum_pieces [DecidableEq ι] (deg : J → ι) (x : J →₀ k) (t : Finset ι)
    (ht : ∀ j ∈ x.support, deg j ∈ t) :
    ∑ e ∈ t, ∑ j ∈ x.support with deg j = e, Finsupp.single j (x j) = x := by
  rw [Finset.sum_fiberwise_of_maps_to ht]
  exact Finsupp.sum_single x

private theorem piece_mem [DecidableEq ι] (deg : J → ι) (x : J →₀ k) (e : ι) :
    ∑ j ∈ x.support with deg j = e, Finsupp.single j (x j) ∈
      Finsupp.supported k k {j | deg j = e} := by
  classical
  exact Submodule.sum_mem _ fun j hj =>
    Finsupp.single_mem_supported k _ (Finset.mem_filter.1 hj).2

/-- **Injectivity from a degreewise count.** Let `f` be a surjective linear map from the free
module on `J` to `W`, sending the basis vector `j` into the piece `p (deg j)` of an independent
family of finite-dimensional subspaces. If each fibre of `deg` is finite with as many elements as
the dimension of the corresponding piece, then `f` is injective. -/
theorem injective_of_surjective_of_card_eq_finrank (f : (J →₀ k) →ₗ[k] W)
    (hf : Function.Surjective f) (p : ι → Submodule k W) (hp : iSupIndep p) (deg : J → ι)
    (hdeg : ∀ j, f (Finsupp.single j 1) ∈ p (deg j)) [∀ d, FiniteDimensional k (p d)]
    (hfin : ∀ d, Finite {j // deg j = d})
    (hcard : ∀ d, Nat.card {j // deg j = d} = finrank k (p d)) :
    Function.Injective f := by
  classical
  have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero p).1 hp
  let V : ι → Submodule k (J →₀ k) := fun d => Finsupp.supported k k {j | deg j = d}
  have hV : ∀ d, V d ≤ (p d).comap f := by
    intro d
    simp only [V]
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact (show deg j = d from hj) ▸ hdeg j
  let g : ∀ d, V d →ₗ[k] p d := fun d =>
    (f.domRestrict (V d)).codRestrict (p d) fun x => hV d x.2
  -- every homogeneous vector is the image of a homogeneous vector of the same degree
  have hsurj : ∀ d, Function.Surjective (g d) := by
    intro d ⟨w, hw⟩
    obtain ⟨y, rfl⟩ := hf w
    let t := insert d (y.support.image deg)
    have ht : ∀ j ∈ y.support, deg j ∈ t := fun j hj =>
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj)
    let v : ι → W := fun e =>
      f (∑ j ∈ y.support with deg j = e, Finsupp.single j (y j)) - if e = d then f y else 0
    have hv : ∀ e ∈ t, v e ∈ p e := by
      intro e _
      refine Submodule.sub_mem _ (hV e (piece_mem deg y e)) ?_
      split_ifs with h
      · exact h ▸ hw
      · exact Submodule.zero_mem _
    have hsum : ∑ e ∈ t, v e = 0 := by
      simp only [v]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' t d, ← map_sum, sum_pieces deg y t ht,
        ite_eq_left_iff.2 (fun h => absurd (Finset.mem_insert_self _ _) h), sub_self]
    have h0 := hind t v hv hsum d (Finset.mem_insert_self _ _)
    simp only [v, ite_true, sub_eq_zero] at h0
    exact ⟨⟨_, piece_mem deg y d⟩, Subtype.ext h0⟩
  -- in each degree the restricted map is between spaces of the same finite dimension
  have hinj : ∀ d, Function.Injective (g d) := by
    intro d
    have : Finite {j | deg j = d} := hfin d
    have : Fintype {j | deg j = d} := Fintype.ofFinite _
    let e := Finsupp.supportedEquivFinsupp (M := k) (R := k) {j | deg j = d}
    have : FiniteDimensional k (V d) := LinearEquiv.finiteDimensional e.symm
    have hrank : finrank k (V d) = finrank k (p d) := by
      rw [e.finrank_eq, finrank_finsupp_self, ← hcard d, ← Nat.card_eq_fintype_card]
      rfl
    have key := LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := k) (V := V d)
      (V₂ := p d) (f := g d) hrank
    exact key.2 (hsurj d)
  -- global injectivity
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  let t := x.support.image deg
  have ht : ∀ j ∈ x.support, deg j ∈ t := fun j hj => Finset.mem_image_of_mem _ hj
  have hsum : ∑ e ∈ t, f (∑ j ∈ x.support with deg j = e, Finsupp.single j (x j)) = 0 := by
    rw [← map_sum, sum_pieces deg x t ht, hx]
  have h0 := hind t _ (fun e _ => hV e (piece_mem deg x e)) hsum
  rw [← sum_pieces deg x t ht]
  refine Finset.sum_eq_zero fun e he => ?_
  have := @hinj e ⟨_, piece_mem deg x e⟩ 0 (by
    apply Subtype.ext
    rw [map_zero]
    exact h0 e he)
  exact congrArg Subtype.val this

end OddMath.SKM.EvenBridge
