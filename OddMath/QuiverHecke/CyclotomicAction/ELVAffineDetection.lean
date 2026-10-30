/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedKernelDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendDegree
import OddMath.SKM.BubbleSubstitution
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Affine PBW detection by high cyclotomic cutoffs

The unit coefficient survives the ELV coefficient relations, and over a
field a linear functional splitting that unit makes affine insertion
injective. Bounded affine PBW degree spans therefore embed in the actual
coefficient-truncated cyclotomic quotient at sufficiently high cutoffs.
-/
noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [Field k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous)

/-- Even cutoff zero preserves the unit of the coefficient algebra. -/
theorem elvCoefficient_one_ne_zero (cutoff : I → ℕ) :
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ≠ 0 := by
  intro h
  have hi := SKM.SYM.elvCoefficient_quotient_injective D k
    (cutoff := cutoff) (d := 0) (fun i => Nat.zero_le (cutoff i))
  have he := hi (a₁ := ⟨1, SKM.SYM.one_mem_coefficientAtMost D k 0⟩) (a₂ := 0)
    (by simpa using h)
  have hz : (1 : SKM.SYM D k) = 0 := congrArg Subtype.val he
  let : Subsingleton (SKM.SYM D k) := subsingleton_of_zero_eq_one hz.symm
  exact (SKM.SYM.coefficientBasis D k).ne_zero (0, ∅) (Subsingleton.elim _ _)

/-- Injectivity follows from a proved surviving unit, not its notation. -/
theorem affineUnit_injective (cutoff : I → ℕ) (v w : List I) :
    Function.Injective (affineUnit D Sc cutoff v w) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k
    (elvCoefficient_one_ne_zero (k := k) D cutoff)
  let r : hom D Sc cutoff v w →ₗ[k]
      ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :=
    (TensorProduct.lid k _).toLinearMap.comp (TensorProduct.map φ LinearMap.id)
  have hr : ∀ f, r (affineUnit D Sc cutoff v w f) = f := by
    intro f
    change (TensorProduct.lid k _) (φ 1 ⊗ₜ[k] f) = f
    simp [hφ]
  intro f g h
  have he := congrArg r h
  simpa only [hr] using he

/-- The concrete affine PBW span with integer degrees strictly below `B`. -/
def affinePBWDegreeBelow (v w : List I) (B : ℤ) :
    Submodule k ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :=
  Submodule.span k ((fun i : NFIdx v w => i.nf (D := D) (Sc := Sc)) ''
    {i | i.deg D sy < B})

/-- Each bounded PBW combination inserts into the corresponding full-ELV
bounded-degree source submodule. -/
theorem affineUnit_mem_degreeBelow (cutoff : I → ℕ) (v w : List I) (B : ℤ)
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    (hf : f ∈ affinePBWDegreeBelow D sy Sc v w B) :
    affineUnit D Sc cutoff v w f ∈ degreeBelow D sy Sc hc cutoff v w B := by
  let _ := elvHomGrading D sy Sc hc cutoff
  change f ∈ Submodule.span k _ at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, hi, rfl⟩ := hf
    change i.deg D sy < B at hi
    simp only [degreeBelow, Submodule.mem_iInf, LinearMap.mem_ker]
    intro n hn
    exact dproj_of_mem_ne
      (affineUnit_mem_degree D Sc cutoff sy hc (i.nf_mem_homDegree D Sc sy)) (by omega)
  | zero => simpa only [map_zero] using (degreeBelow D sy Sc hc cutoff v w B).zero_mem
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul c f _ hf => simpa only [map_smul] using Submodule.smul_mem _ c hf

include hc in
/-- The actual affine-to-truncated quotient map is injective on the bounded
PBW span under the derived degree inequality. No coefficient specialization
or injectivity premise occurs. -/
theorem exists_affinePBW_truncated_injective (ν : List I) :
    ∃ L : ℤ, ∀ (cutoff : I → ℕ) (N : ℕ) (C B : ℤ),
      (∀ j ∈ ν, C ≤ 2 * sy.d j * cutoff j) → B ≤ L + min C (2 * N) + L →
      ∀ v w : List I, v.Perm ν → w.Perm ν →
      Function.Injective (fun x : affinePBWDegreeBelow D sy Sc v w B =>
        (truncatedIdeal D Sc cutoff N v w).mkQ (affineUnit D Sc cutoff v w x.val)) := by
  obtain ⟨L, hL⟩ := exists_truncated_degreeBelow_injective D sy Sc hc ν
  refine ⟨L, fun cutoff N C B hC hB v w hv hw x y hxy => ?_⟩
  have he := hL cutoff N C B hC hB v w hv hw
    (a₁ := ⟨affineUnit D Sc cutoff v w x.val,
      affineUnit_mem_degreeBelow D sy Sc hc cutoff v w B x.property⟩)
    (a₂ := ⟨affineUnit D Sc cutoff v w y.val,
      affineUnit_mem_degreeBelow D sy Sc hc cutoff v w B y.property⟩) hxy
  exact Subtype.ext (affineUnit_injective D Sc cutoff v w (congrArg Subtype.val he))

include hc in
/-- Every bounded affine PBW degree span is detected at all sufficiently
large non-uniform strand cutoffs and coefficient-weight cutoffs. The strand
cutoff condition only involves the finite boundary content. -/
theorem affinePBW_detected_at_high_cutoffs (ν : List I) (B : ℤ) :
    ∃ K : ℕ, ∀ (cutoff : I → ℕ) (N : ℕ),
      (∀ j ∈ ν, K ≤ cutoff j) → K ≤ N →
      ∀ v w : List I, v.Perm ν → w.Perm ν →
      Function.Injective (fun x : affinePBWDegreeBelow D sy Sc v w B =>
        (truncatedIdeal D Sc cutoff N v w).mkQ (affineUnit D Sc cutoff v w x.val)) := by
  obtain ⟨L, hL⟩ := exists_affinePBW_truncated_injective D sy Sc hc ν
  let K := (B - (L + L)).toNat
  refine ⟨K, fun cutoff N hcut hN v w hv hw => ?_⟩
  apply hL cutoff N (2 * K) B ?_ ?_ v w hv hw
  · intro j hj
    have hd : (1 : ℤ) ≤ sy.d j := by have := sy.pos j; omega
    have hkj : (K : ℤ) ≤ cutoff j := by exact_mod_cast hcut j hj
    have hm := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (cutoff j) : (0 : ℤ) ≤ _)
    nlinarith only [hm, hkj]
  · have hk : B - (L + L) ≤ (K : ℤ) := by dsimp [K]; omega
    have hkn : (K : ℤ) ≤ N := by exact_mod_cast hN
    have hk0 : (0 : ℤ) ≤ K := Nat.cast_nonneg _
    omega

end OddMath.QuiverHecke.ELVOld
