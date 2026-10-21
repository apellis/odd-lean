/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Grading
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Homogeneous spanning families and Laurentian Hom-spaces

The Laurentian condition used in Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, §§11–12 follows from a homogeneous spanning family with finite degree
fibers and degrees bounded below. These are explicit hypotheses on the spanning family;
neither independence of that family nor finiteness of the set of colours is required.

The projection used below is constructed from the internal direct-sum grading. For the
presented Hom-spaces, this grading follows from `isHomogeneous_gdeg`, not from a
nondegeneracy hypothesis.
-/

noncomputable section

namespace OddMath.SKM

namespace GradedSpanning

variable {k M α : Type*} [Field k] [AddCommGroup M] [Module k M]
variable (A : ℤ → Submodule k M) (hA : DirectSum.IsInternal A)
variable (v : α → M) (d : α → ℤ)
variable (hv : ∀ x, v x ∈ A (d x)) (hspan : Submodule.span k (Set.range v) = ⊤)
include hA hv hspan

/-- Projecting a homogeneous spanning family onto one degree gives a spanning family
for precisely that homogeneous component. -/
theorem component_eq_span (n : ℤ) :
    A n = Submodule.span k (v '' {x | d x = n}) := by
  let := hA.chooseDecomposition
  let p : M →ₗ[k] M := (A n).subtype ∘ₗ
    (DirectSum.component k ℤ (fun i => A i) n) ∘ₗ (DirectSum.decomposeLinearEquiv A).toLinearMap
  have psame {x : M} (hx : x ∈ A n) : p x = x :=
    DirectSum.decompose_of_mem_same A hx
  have pne {x : M} {j : ℤ} (hx : x ∈ A j) (hj : j ≠ n) : p x = 0 :=
    DirectSum.decompose_of_mem_ne A hx hj
  apply le_antisymm
  · intro x hx
    have hxspan : x ∈ Submodule.span k (Set.range v) := by rw [hspan]; trivial
    rw [← psame hx]
    clear hx
    induction hxspan using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      by_cases ha : d a = n
      · rw [psame (ha ▸ hv a)]
        exact Submodule.subset_span ⟨a, ha, rfl⟩
      · rw [pne (hv a) ha]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact ha ▸ hv a

/-- Finite degree fibers of a homogeneous spanning family imply finite-dimensional
homogeneous components. -/
theorem finiteDimensional_component (hfinite : ∀ n, Set.Finite {x | d x = n}) (n : ℤ) :
    FiniteDimensional k (A n) := by
  rw [component_eq_span A hA v d hv hspan n]
  exact FiniteDimensional.span_of_finite k ((hfinite n).image v)

/-- A uniform lower bound on the degrees of a homogeneous spanning family is also a
lower bound on the nonzero homogeneous components. -/
theorem component_eq_bot (N : ℤ) (hlower : ∀ x, N ≤ d x) {n : ℤ} (hn : n < N) :
    A n = ⊥ := by
  rw [component_eq_span A hA v d hv hspan n]
  have hempty : {x | d x = n} = (∅ : Set α) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (not_le_of_gt hn) (hx ▸ hlower x)
  rw [hempty, Set.image_empty, Submodule.span_empty]

/-- The two Laurentian bounds follow from local finiteness and a uniform lower bound
on the degrees of a homogeneous spanning family. -/
theorem laurentian (hfinite : ∀ n, Set.Finite {x | d x = n})
    (hlower : ∃ N, ∀ x, N ≤ d x) :
    (∀ n, FiniteDimensional k (A n)) ∧ ∃ N, ∀ n < N, A n = ⊥ := by
  refine ⟨finiteDimensional_component A hA v d hv hspan hfinite, ?_⟩
  obtain ⟨N, hN⟩ := hlower
  exact ⟨N, fun _ hn => component_eq_bot A hA v d hv hspan N hN hn⟩

end GradedSpanning

open CategoryTheory StringDiagrams

universe u v w

section HomGrading

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
variable {k : Type w} [CommRing k] (sy : Symmetrizer D) (Sc : Scalars D k)

/-- The integer-graded parts of a presented Hom-space form an internal direct sum,
using only homogeneity of the defining scalars. -/
theorem isInternal_homDeg_gdeg (hc : Sc.Homogeneous) (a b : Obj (sig D)) :
    DirectSum.IsInternal ((pres D Sc).homDeg (gdeg D sy) a b) :=
  Presentation.isInternal_homDeg (isHomogeneous_gdeg D sy Sc hc) a b

end HomGrading

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
variable {k : Type w} [Field k] (sy : Symmetrizer D) (Sc : Scalars D k)

/-- A homogeneous spanning family makes the presented Hom-space Laurentian when its
degree fibers are finite and its degrees have a uniform lower bound. The finiteness and
bound are explicit inputs, independent of nondegeneracy. -/
theorem homDeg_laurentian_of_spanning (hc : Sc.Homogeneous) (a b : Obj (sig D))
    {α : Type*} (v : α → ((pres D Sc).obj a ⟶ (pres D Sc).obj b)) (d : α → ℤ)
    (hv : ∀ x, v x ∈ (pres D Sc).homDeg (gdeg D sy) a b (d x))
    (hspan : Submodule.span k (Set.range v) = ⊤)
    (hfinite : ∀ n, Set.Finite {x | d x = n}) (hlower : ∃ N, ∀ x, N ≤ d x) :
    (∀ n, FiniteDimensional k ((pres D Sc).homDeg (gdeg D sy) a b n)) ∧
      ∃ N, ∀ n < N, (pres D Sc).homDeg (gdeg D sy) a b n = ⊥ :=
  GradedSpanning.laurentian _ (isInternal_homDeg_gdeg D sy Sc hc a b)
    v d hv hspan hfinite hlower

end OddMath.SKM
