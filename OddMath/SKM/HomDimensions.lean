/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.GradedExpansion

/-!
# Homogeneous dimensions in BE2 (dum)

The graded restriction of the conjectural basis gives an explicit finite
convolution of the dimensions of the abstract coefficient algebra components.
The colour-degree local-finiteness hypothesis is the intermediate scope
recorded in ERRATA [BE2] 9 and issue #42.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams
namespace MatchingBasisChoice

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
variable {a b : List (Letter I)} (F : MatchingBasisChoice a b)
variable (sy : Symmetrizer D) (μ : X) (k : Type w) [CommRing k]

/-- Only finitely many decorated matchings have degree below a given bound. -/
theorem labelDegree_le_finite (n : ℤ) :
    Set.Finite {t : F.Labels | (F.labelBidegree sy μ t).1 ≤ n} := by
  obtain ⟨N, hN⟩ := F.degree_bounded_below sy μ
  apply ((Set.finite_Icc N n).biUnion (fun z _ => F.degree_finite sy μ z)).subset
  intro t ht
  exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨⟨hN t, ht⟩, rfl⟩⟩

/-- The finite set of labels that can contribute to integer degree `n`. -/
def boundedLabels (n : ℤ) := {t : F.Labels // (F.labelBidegree sy μ t).1 ≤ n}

instance (n : ℤ) : Fintype (F.boundedLabels sy μ n) :=
  (F.labelDegree_le_finite sy μ n).fintype

/-- Coefficients outside the contributing label set vanish. -/
theorem coefficient_eq_zero (z : ℤ × ZMod 2)
    (f : F.coefficientComponent (k := k) sy μ z) (t : F.Labels)
    (ht : ¬ (F.labelBidegree sy μ t).1 ≤ z.1) : f.val t = 0 := by
  have h := f.property t
  rw [SYM.component_eq_bot sy k _ (by simp only [Prod.fst_sub]; omega)] at h
  exact h

/-- Restrict shifted coefficient expansions to the finite set of contributing
labels. The coefficient components are subspaces of `SYM`, not image spaces. -/
def coefficientComponentEquiv (z : ℤ × ZMod 2) :
    F.coefficientComponent (k := k) sy μ z ≃ₗ[k]
      (∀ t : F.boundedLabels sy μ z.1,
        SYM.component sy k (z - F.labelBidegree sy μ t.val)) := by
  classical
  let extend (f : ∀ t : F.boundedLabels sy μ z.1,
      SYM.component sy k (z - F.labelBidegree sy μ t.val)) : F.Labels →₀ SYM D k :=
    Finsupp.onFinset (F.labelDegree_le_finite sy μ z.1).toFinset
      (fun t => if h : (F.labelBidegree sy μ t).1 ≤ z.1 then (f ⟨t, h⟩).val else 0)
      (fun t h => by
        simp only [Set.Finite.mem_toFinset]
        by_contra hn
        exact h (dite_eq_right hn))
  have hm (f : ∀ t : F.boundedLabels sy μ z.1,
      SYM.component sy k (z - F.labelBidegree sy μ t.val)) :
      extend f ∈ F.coefficientComponent (k := k) sy μ z := by
    intro t
    change (if h : (F.labelBidegree sy μ t).1 ≤ z.1 then (f ⟨t, h⟩).val else 0) ∈ _
    split_ifs with h
    · exact (f ⟨t, h⟩).property
    · exact Submodule.zero_mem _
  refine
    { toFun := fun f t => ⟨f.val t.val, f.property t.val⟩
      invFun := fun f => ⟨extend f, hm f⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  · intro f
    apply Subtype.ext
    ext t
    change (if h : (F.labelBidegree sy μ t).1 ≤ z.1 then f.val t else 0) = f.val t
    split_ifs with h
    · rfl
    · exact (F.coefficient_eq_zero sy μ k z f t h).symm
  · intro f
    funext t
    apply Subtype.ext
    exact dite_eq_left t.property

end MatchingBasisChoice

section Dimensions
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
variable {k : Type w} [Field k] {Sc : Scalars D k}
variable {a b : List (Letter I)} (F : MatchingBasisChoice a b)
variable (sy : Symmetrizer D) (cs : CScalars Sc) (μ : X)

/-- Componentwise dimension convolution for BE2 Theorem 12.1, (dum).
The Nondegeneracy Conjecture enters only through the selected family's basis
hypothesis. `DegreeLocallyFinite` is the explicit intermediate hypothesis
needed to interpret all dimensions as finite integers. -/
theorem homComponent_finrank (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite)
    (hF : F.IsBasis cs μ) (z : ℤ × ZMod 2) :
    Module.finrank k (homComponent sy Sc μ a b z) =
      ∑ t : F.boundedLabels sy μ z.1,
        Module.finrank k (SYM.component sy k (z - F.labelBidegree sy μ t.val)) := by
  let (t : F.boundedLabels sy μ z.1) :
      FiniteDimensional k (SYM.component sy k (z - F.labelBidegree sy μ t.val)) :=
    SYM.finiteDimensional_component sy hf _
  rw [← (F.componentExpansionEquiv sy cs μ hc hF z).finrank_eq,
    (F.coefficientComponentEquiv sy μ k z).finrank_eq]
  exact Module.finrank_pi_fintype _

/-- The conjecture supplies the only independence input to the homogeneous
dimension formula. All component dimensions on the right belong to the
abstract coefficient algebra `SYM`. -/
theorem homComponent_finrank_of_nondegeneracy (hc : Sc.Homogeneous)
    (hf : sy.DegreeLocallyFinite) (hN : NondegeneracyConjecture cs)
    (hab : wt D 0 a = wt D 0 b) (z : ℤ × ZMod 2) :
    Module.finrank k (homComponent sy Sc μ a b z) =
      ∑ t : F.boundedLabels sy μ z.1,
        Module.finrank k (SYM.component sy k (z - F.labelBidegree sy μ t.val)) :=
  homComponent_finrank F sy cs μ hc hf (hN a b hab μ F) z

end Dimensions
end OddMath.SKM
