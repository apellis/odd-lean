/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSupport

/-! # Finite integer support at arbitrary strand content

The coefficient-weight-truncated vacuum and the finite homogeneous append
spanning family give finite degree support by induction on the source word.
No rank, freeness, or bound on the number of words of a weight is used.
-/
noncomputable section
open CategoryTheory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

/-- Finite smaller degree supports propagate through the concrete finite append family. -/
theorem truncatedAppend_finite_support (i : I) (v w : List I)
    (ih : ∀ t : List I, ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N v t)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v t n) :
    ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N (v ++ [i]) w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w n := by
  classical
  choose S hfin hs using ih
  let T : Set ℤ := ⋃ (q : AppendCrossingSkeleton i v w),
    ⋃ (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree),
      (fun a => 2 * sy.d i * j.val + (a + appendTailDegree D sy q.index)) '' S q.index.oldTarget
  have ht : T.Finite := Set.finite_iUnion fun q => Set.finite_iUnion fun j =>
    (hfin q.index.oldTarget).image _
  refine ⟨T, ht, le_antisymm ?_ le_top⟩
  rw [appendFiniteRange_degree_support D Sc cutoff sy hc N i v w
    (fun q => S q.index.oldTarget) (fun q => hs q.index.oldTarget)]
  refine iSup_le fun q => iSup_le fun j => iSup_le fun a => iSup_le fun ha => ?_
  exact le_iSup_of_le _ (le_iSup_of_le
    (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨j, ⟨a, ha, rfl⟩⟩⟩ :
      2 * sy.d i * j.val + (a + appendTailDegree D sy q.index) ∈ T) le_rfl)

/-- Arbitrary content has finite support whenever the coefficient degrees have a
uniform degree/weight bound. This bound is obtained from finite colours below. -/
theorem truncatedContent_finite_support_of_bound (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (v w : List I) :
    ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v w n := by
  induction v using List.reverseRecOn generalizing w with
  | nil => exact ⟨Set.Icc 0 (M * N), Set.finite_Icc _ _,
      truncatedVacuum_support_of_bound D Sc cutoff sy hc N M hM hbound w⟩
  | append_singleton v i ih =>
      exact truncatedAppend_finite_support D Sc cutoff sy hc N i v w ih

/-- Finite colours give bounded integer support for every pair of words, including
arbitrarily repeated even, odd, and mixed colours. -/
theorem truncatedContent_finite_support [Finite I] (v w : List I) :
    ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v w n := by
  obtain ⟨M, hM, hb⟩ := SKM.SYM.exists_coefficientDegree_bound D sy
  exact truncatedContent_finite_support_of_bound D Sc cutoff sy hc N M hM hb v w

/-- A finite homogeneous spanning support kills all other homogeneous parts. -/
theorem truncatedDegree_eq_bot_of_support (v w : List I) (S : Set ℤ)
    (hS : (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) =
      ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v w n)
    (n : ℤ) (hn : n ∉ S) :
    truncatedDegree D Sc cutoff sy hc N v w n = ⊥ := by
  have hp : (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) ≤
      LinearMap.ker (truncatedDproj D Sc cutoff sy hc N v w n) := by
    rw [hS]
    refine iSup_le fun a => iSup_le fun ha => ?_
    intro z hz
    exact (truncatedDproj_of_mem D Sc cutoff sy hc N hz n).trans
      (ite_eq_right (by intro he; exact hn (he ▸ ha)))
  apply bot_unique
  intro z hz
  have he := truncatedDproj_of_mem D Sc cutoff sy hc N hz n
  rw [ite_eq_left rfl, hp (Submodule.mem_top : z ∈ (⊤ : Submodule k _))] at he
  exact he.symm

/-- An explicit loose symmetric interval extracted from a finite support. -/
theorem truncatedContent_bounded_of_finite_support (v w : List I)
    (h : ∃ S : Set ℤ, S.Finite ∧
      (⊤ : Submodule k (TruncatedOld D Sc cutoff N v w)) =
        ⨆ n ∈ S, truncatedDegree D Sc cutoff sy hc N v w n) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegree D Sc cutoff sy hc N v w n = ⊥ := by
  classical
  obtain ⟨S, hf, hs⟩ := h
  refine ⟨hf.toFinset.sup Int.natAbs, fun n hn =>
    truncatedDegree_eq_bot_of_support D Sc cutoff sy hc N v w S hs n ?_⟩
  intro hmem
  have hnat : n.natAbs ≤ hf.toFinset.sup Int.natAbs :=
    Finset.le_sup (f := Int.natAbs) (hf.mem_toFinset.mpr hmem)
  have habs : |n| ≤ ((hf.toFinset.sup Int.natAbs : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnat
  have := abs_le.mp habs
  omega

/-- Actual bounded integer support at arbitrary content, from the coefficient
bound and the concrete cyclotomic recurrence, not from a support premise. -/
theorem truncatedContent_bounded_of_bound (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (v w : List I) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegree D Sc cutoff sy hc N v w n = ⊥ :=
  truncatedContent_bounded_of_finite_support D Sc cutoff sy hc N v w
    (truncatedContent_finite_support_of_bound D Sc cutoff sy hc N M hM hbound v w)

/-- Every coefficient-weight-truncated cyclotomic Hom has bounded integer
support for finite colours, without any restriction on strand content. -/
theorem truncatedContent_bounded [Finite I] (v w : List I) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegree D Sc cutoff sy hc N v w n = ⊥ :=
  truncatedContent_bounded_of_finite_support D Sc cutoff sy hc N v w
    (truncatedContent_finite_support D Sc cutoff sy hc N v w)

end OddMath.QuiverHecke.ELVOld
