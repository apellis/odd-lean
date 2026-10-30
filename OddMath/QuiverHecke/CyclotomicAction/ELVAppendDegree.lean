/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendSpanning
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedAppend

/-! Degree shifts of the finite append spanning maps. -/
noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

theorem affineUnit_mem_degree {v w : List I} {d : ℤ}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    (hf : f ∈ homDegree D sy Sc v w d) :
    affineUnit D Sc cutoff v w f ∈ elvHomDegree D sy Sc hc cutoff v w d := by
  let _ := elvCoefficientCategoryGrading (k := k) D sy cutoff
  let _ := gradedSupercategory D sy Sc hc
  have h := BoxProd.tmulHom_mem_degree (X := obj D Sc cutoff v)
    (Y := obj D Sc cutoff w)
    (GradedSupercategory.id_mem_degree (R := k) (obj D Sc cutoff v).fst) hf
  rw [zero_add] at h
  exact h

theorem appendSourcePower_mem_degree (i : I) (v : List I) (n : ℕ) :
    appendSourcePower D Sc cutoff i v n ∈
      elvHomDegree D sy Sc hc cutoff (v ++ [i]) (v ++ [i]) (2 * sy.d i * n) := by
  rw [appendSourcePower_whisker]
  apply affineUnit_mem_degree D Sc cutoff sy hc
  let _ := gradedSupercategory D sy Sc hc
  let _ := gradedMonoidalSupercategory D sy Sc hc
  have h : (dotE D Sc [i] 0 ^ n : End _) ∈ homDegree D sy Sc [i] [i]
      (2 * sy.d i * n) := by
    simpa only [firstDotPower, dotE_pow, List.map_replicate] using
      firstDotPower_mem_gdeg D sy Sc i [] n
  exact GradedMonoidalSupercategory.whiskerLeft_mem_degree ((pres D Sc).obj (ob D v)) h

/-- Sum of the generator degrees of the concrete tail diagram. -/
def appendTailDegree {i : I} {v w : List I} (x : AppendIdx i v w) : ℤ :=
  gsum D sy (pl (x.oldTarget ++ [i])
    (((List.replicate x.1.1 v.length).map PG.dot) ++
      cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹)))

theorem appendTail_mem_degree {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendTail D Sc x ∈ homDegree D sy Sc (x.oldTarget ++ [i]) w
      (appendTailDegree D sy x) :=
  Presentation.diag_mem_homDeg' (degree_gdeg_mkD D sy _ _)

/-- The source moving dots, old homogeneous term, and tail contribute additively. -/
theorem appendBoundedOldMap_mem_degree (N : ℕ) (i : I) (v t w : List I)
    (j : ℕ) {h : hom D Sc cutoff (t ++ [i]) w} {a b : ℤ}
    (hh : h ∈ elvHomDegree D sy Sc hc cutoff (t ++ [i]) w b)
    {r : TruncatedOld D Sc cutoff N v t}
    (hr : r ∈ truncatedDegree D Sc cutoff sy hc N v t a) :
    appendBoundedOldMap D Sc cutoff N i v t w j h r ∈
      truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w (2 * sy.d i * j + (a + b)) := by
  obtain ⟨r, hr, rfl⟩ := hr
  rw [appendBoundedOldMap_mk]
  apply Submodule.mem_map_of_mem
  let _ := elvHomGrading D sy Sc hc cutoff
  exact GradedSupercategory.comp_mem_degree
    (appendSourcePower_mem_degree D Sc cutoff sy hc i v j)
    (GradedSupercategory.comp_mem_degree
      (rightContext_mem_degree D Sc cutoff sy hc [i] hr) hh)

/-- Homogeneity of every actual map in the finite append range spanning family. -/
theorem appendCrossingSkeleton_map_mem_degree (N : ℕ) (i : I) (v w : List I)
    (q : AppendCrossingSkeleton i v w) (j : ℕ) {a : ℤ}
    {r : TruncatedOld D Sc cutoff N v q.index.oldTarget}
    (hr : r ∈ truncatedDegree D Sc cutoff sy hc N v q.index.oldTarget a) :
    appendBoundedOldMap D Sc cutoff N i v q.index.oldTarget w j
      (affineUnit D Sc cutoff _ _ (appendTail D Sc q.index)) r ∈
    truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w
      (2 * sy.d i * j + (a + appendTailDegree D sy q.index)) :=
  appendBoundedOldMap_mem_degree D Sc cutoff sy hc N i v q.index.oldTarget w j
    (affineUnit_mem_degree D Sc cutoff sy hc (appendTail_mem_degree D Sc sy q.index)) hr

/-- A supported smaller quotient gives supported range, with the concrete shift. -/
theorem appendBoundedOldMap_range_le (N : ℕ) (i : I) (v t w : List I)
    (j : ℕ) {h : hom D Sc cutoff (t ++ [i]) w} {b : ℤ}
    (hh : h ∈ elvHomDegree D sy Sc hc cutoff (t ++ [i]) w b)
    (S : Set ℤ)
    (hS : (⊤ : Submodule k (TruncatedOld D Sc cutoff N v t)) =
      ⨆ a ∈ S, truncatedDegree D Sc cutoff sy hc N v t a) :
    LinearMap.range (appendBoundedOldMap D Sc cutoff N i v t w j h) ≤
      ⨆ a ∈ S, truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w
        (2 * sy.d i * j + (a + b)) := by
  rw [← Submodule.map_top, hS, Submodule.map_iSup]
  apply iSup_le
  intro a
  rw [Submodule.map_iSup]
  apply iSup_le
  intro ha
  apply le_trans _ (le_iSup_of_le a (le_iSup_of_le ha le_rfl))
  rintro z ⟨r, hr, rfl⟩
  exact appendBoundedOldMap_mem_degree D Sc cutoff sy hc N i v t w j hh hr

/-- All-content support propagation from smaller truncated Hom support. The
indices are finite when each `S q` is finite; no finite-colour assumption occurs. -/
theorem appendFiniteRange_degree_support (N : ℕ) (i : I) (v w : List I)
    (S : AppendCrossingSkeleton i v w → Set ℤ)
    (hS : ∀ q, (⊤ : Submodule k (TruncatedOld D Sc cutoff N v q.index.oldTarget)) =
      ⨆ a ∈ S q, truncatedDegree D Sc cutoff sy hc N v q.index.oldTarget a) :
    (⊤ : Submodule k (TruncatedOld D Sc cutoff N (v ++ [i]) w)) =
      ⨆ (q : AppendCrossingSkeleton i v w)
        (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree)
        (a : ℤ) (_ : a ∈ S q),
        truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w
          (2 * sy.d i * j.val + (a + appendTailDegree D sy q.index)) := by
  apply le_antisymm _ le_top
  rw [← appendFiniteRangeSpan_eq_top D Sc cutoff N i v w]
  unfold appendFiniteRangeSpan
  apply iSup_le
  intro q
  apply iSup_le
  intro j
  exact le_trans (appendBoundedOldMap_range_le D Sc cutoff sy hc N i v
    q.index.oldTarget w j.val
    (affineUnit_mem_degree D Sc cutoff sy hc (appendTail_mem_degree D Sc sy q.index))
    (S q) (hS q)) (le_iSup_of_le q (le_iSup_of_le j le_rfl))

/-- Outside all shifted smaller supports, the actual quotient projection vanishes. -/
theorem appendFiniteRange_dproj_eq_zero (N : ℕ) (i : I) (v w : List I)
    (S : AppendCrossingSkeleton i v w → Set ℤ)
    (hS : ∀ q, (⊤ : Submodule k (TruncatedOld D Sc cutoff N v q.index.oldTarget)) =
      ⨆ a ∈ S q, truncatedDegree D Sc cutoff sy hc N v q.index.oldTarget a)
    (n : ℤ)
    (hn : ∀ (q : AppendCrossingSkeleton i v w)
      (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree)
      (a : ℤ), a ∈ S q → 2 * sy.d i * j.val + (a + appendTailDegree D sy q.index) ≠ n)
    (z : TruncatedOld D Sc cutoff N (v ++ [i]) w) :
    truncatedDproj D Sc cutoff sy hc N (v ++ [i]) w n z = 0 := by
  have hle : (⊤ : Submodule k (TruncatedOld D Sc cutoff N (v ++ [i]) w)) ≤
      LinearMap.ker (truncatedDproj D Sc cutoff sy hc N (v ++ [i]) w n) := by
    rw [appendFiniteRange_degree_support D Sc cutoff sy hc N i v w S hS]
    refine iSup_le fun q => iSup_le fun j => iSup_le fun a => iSup_le fun ha => ?_
    intro f hf
    exact (truncatedDproj_of_mem D Sc cutoff sy hc N hf n).trans (ite_eq_right (hn q j a ha))
  exact hle (Submodule.mem_top)

/-- The homogeneous part itself is zero outside the shifted smaller supports. -/
theorem appendFiniteRange_degree_eq_bot (N : ℕ) (i : I) (v w : List I)
    (S : AppendCrossingSkeleton i v w → Set ℤ)
    (hS : ∀ q, (⊤ : Submodule k (TruncatedOld D Sc cutoff N v q.index.oldTarget)) =
      ⨆ a ∈ S q, truncatedDegree D Sc cutoff sy hc N v q.index.oldTarget a)
    (n : ℤ)
    (hn : ∀ (q : AppendCrossingSkeleton i v w)
      (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree)
      (a : ℤ), a ∈ S q → 2 * sy.d i * j.val + (a + appendTailDegree D sy q.index) ≠ n) :
    truncatedDegree D Sc cutoff sy hc N (v ++ [i]) w n = ⊥ := by
  apply bot_unique
  intro z hz
  have he := truncatedDproj_of_mem D Sc cutoff sy hc N hz n
  rw [ite_eq_left rfl, appendFiniteRange_dproj_eq_zero D Sc cutoff sy hc N i v w S hS n hn] at he
  exact he.symm

end OddMath.QuiverHecke.ELVOld
