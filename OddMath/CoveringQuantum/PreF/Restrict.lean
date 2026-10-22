/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.PreF.Form

/-!
# Restriction of the free bilinear form to a subset of generators

For an injective map `e : J → I` of index sets, the algebra map
`PreF.incl e : 'f_J → 'f_I`, `θⱼ ↦ θ_{e j}`, intertwines the twists and skew derivations of a
bicharacter `χ` on `I` with those of its restriction `χ ∘ (e × e)`, and pulls the bilinear form
back to the bilinear form of the restriction. Consequently it reflects the radical. Every
element of `'f_I` lies in the image of `'f_s` for a finite set `s` of indices.

These are the ingredients used to reduce statements about the radical over an arbitrary index
set to finite index sets.

## Main definitions

* `PreF.incl e`: the algebra map `'f_J → 'f_I` induced by `e : J → I`.

## Main results

* `PreF.incl_rDeriv`: `rₑⱼ ∘ incl = incl ∘ rⱼ` for injective `e`.
* `PreF.form_incl`: `(incl x, incl y) = (x, y)`.
* `PreF.mem_radical_of_incl_mem`: `incl` reflects the radical.
* `PreF.exists_finset_mem_range_incl`: every element comes from a finite set of generators.
-/

noncomputable section

namespace OddMath.CoveringQuantum.PreF

variable {k I J : Type*} [CommRing k]

variable (k) in
/-- The algebra map `'f_J → 'f_I`, `θⱼ ↦ θ_{e j}`. -/
def incl (e : J → I) : PreF k J →ₐ[k] PreF k I := FreeAlgebra.lift k fun j ↦ θ k (e j)

@[simp] theorem incl_θ (e : J → I) (j : J) : incl k e (θ k j) = θ k (e j) :=
  FreeAlgebra.lift_ι_apply _ _

variable (χ : Bichar k I) (χJ : Bichar k J) (e : J → I) (hχ : ∀ i j, χJ i j = χ (e i) (e j))

include hχ in
/-- `incl` intertwines the twists. -/
theorem incl_twist (j : J) (x : PreF k J) :
    incl k e (twist χJ j x) = twist χ (e j) (incl k e x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 l =>
    change incl k e (twist χJ j (θ k l)) = twist χ (e j) (incl k e (θ k l))
    rw [twist_θ, incl_θ, twist_θ, map_smul, incl_θ, hχ]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

variable [DecidableEq I] [DecidableEq J]

include hχ in
/-- For injective `e`, `incl` intertwines the right skew derivations. -/
theorem incl_rDeriv (he : Function.Injective e) (j : J) (x : PreF k J) :
    incl k e (rDeriv χJ j x) = rDeriv χ (e j) (incl k e x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 l =>
    change incl k e (rDeriv χJ j (θ k l)) = rDeriv χ (e j) (incl k e (θ k l))
    rw [rDeriv_θ, incl_θ, rDeriv_θ]
    by_cases h : j = l
    · simp [h]
    · simp [h, he.ne h]
  | mul a b ha hb =>
    rw [rDeriv_mul, map_add, map_mul, map_mul, ha, hb, incl_twist χ χJ e hχ, map_mul, rDeriv_mul]
  | add a b ha hb => simp only [map_add, ha, hb]

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem counit_incl (x : PreF k J) : counit (incl k e x) = counit x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 l =>
    change counit (incl k e (θ k l)) = counit (θ k l)
    simp
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

variable (nm : I → k) (nmJ : J → k) (hn : ∀ j, nmJ j = nm (e j))

include hχ hn in
/-- For injective `e`, `incl` pulls the bilinear form back to the restricted form. -/
theorem form_incl (he : Function.Injective e) (x y : PreF k J) :
    form χ nm (incl k e x) (incl k e y) = form χJ nmJ x y := by
  induction x using induction_right generalizing y with
  | algebraMap c => simp [form_algebraMap_left]
  | smul c x hx => rw [map_smul, LinearMap.map_smul₂, LinearMap.map_smul₂, hx]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | mul_θ x j hx =>
    rw [map_mul, incl_θ, form_mul_θ, ← incl_rDeriv χ χJ e hχ he, hx, form_mul_θ, hn]

include hχ hn in
/-- For injective `e`, `incl` reflects the radical. -/
theorem mem_radical_of_incl_mem (he : Function.Injective e) {x : PreF k J}
    (hx : incl k e x ∈ radical χ nm) : x ∈ radical χJ nmJ := by
  apply (mem_radical_iff χJ nmJ).mpr
  intro y
  rw [← form_incl χ χJ e hχ nm nmJ hn he, (mem_radical_iff χ nm).mp hx]

omit [DecidableEq I] [DecidableEq J] in
/-- Every element of `'f_I` is the image of an element of `'f_s` for a finite set `s`. -/
theorem exists_finset_mem_range_incl (x : PreF k I) :
    ∃ s : Finset I, x ∈ (incl k ((↑) : s → I)).range := by
  have key : ∀ s : Finset I,
      (incl k ((↑) : s → I)).range = Algebra.adjoin k (θ k '' (s : Set I)) := by
    intro s
    rw [incl, ← Algebra.adjoin_range_eq_range_freeAlgebra_lift]
    congr 1
    ext y
    simp
  have mono : ∀ {s t : Finset I}, s ⊆ t →
      (incl k ((↑) : s → I)).range ≤ (incl k ((↑) : t → I)).range := by
    intro s t hst
    rw [key, key]
    exact Algebra.adjoin_mono (Set.image_mono (by exact_mod_cast hst))
  induction x using FreeAlgebra.induction with
  | grade0 c => exact ⟨∅, Subalgebra.algebraMap_mem _ c⟩
  | grade1 i =>
    refine ⟨{i}, ?_⟩
    rw [key]
    exact Algebra.subset_adjoin ⟨i, by simp, rfl⟩
  | mul a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨t, ht⟩ := hb
    classical
    exact ⟨s ∪ t, Subalgebra.mul_mem _ (mono Finset.subset_union_left hs)
      (mono Finset.subset_union_right ht)⟩
  | add a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨t, ht⟩ := hb
    classical
    exact ⟨s ∪ t, Subalgebra.add_mem _ (mono Finset.subset_union_left hs)
      (mono Finset.subset_union_right ht)⟩

end OddMath.CoveringQuantum.PreF
