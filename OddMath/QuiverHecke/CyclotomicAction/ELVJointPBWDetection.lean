import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientWindowTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedKernelDegree

/-! # Joint coefficient and affine PBW windows
The bounded recovery input in SwappedVacuumCoordinates §6. A single
source window, defined before any quotient cutoff, retains full polynomial
and exterior coefficients through both actual quotient maps.
-/
noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous)

/-- Both bounds refer to the full source and do not depend on quotient cutoffs. -/
def jointPBWWindow (d : ℕ) (v w : List I) (B : ℤ) :
    Submodule k (coefficientObj D Sc v ⟶ coefficientObj D Sc w) :=
  Submodule.span k
    ((fun p : SKM.SYM.CoefficientIndex D × NFIdx v w =>
      sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k p.1)
        (p.2.nf (D := D) (Sc := Sc))) ''
      {p | SKM.SYM.coefficientWeight D p.1 ≤ d ∧
        SKM.SYM.coefficientDegree D sy p.1 + p.2.deg D sy < B})

theorem jointPBWWindow_le_coefficientWindow (d : ℕ) (v w : List I) (B : ℤ) :
    jointPBWWindow D sy Sc d v w B ≤ coefficientWindowSource D Sc d v w := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a, f⟩, ha, rfl⟩
  let a' : SKM.SYM.CoefficientAtMost D k d :=
    ⟨SKM.SYM.coefficientBasis D k a, Submodule.subset_span ⟨a, ha.1, rfl⟩⟩
  exact ⟨a' ⊗ₜ[k] f.nf, rfl⟩

theorem jointPBWWindow_quotient_mem_degreeBelow (cutoff : I → ℕ)
    (d : ℕ) (v w : List I) (B : ℤ)
    {f : coefficientObj D Sc v ⟶ coefficientObj D Sc w}
    (hf : f ∈ jointPBWWindow D sy Sc d v w B) :
    elvHomQuotient D Sc cutoff v w f ∈ degreeBelow D sy Sc hc cutoff v w B := by
  let _ := elvHomGrading D sy Sc hc cutoff
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨a, i⟩, ha, rfl⟩ := hf
    have hc' : SKM.SYM.coefficientBasis D k a ∈
        SKM.SYM.coefficientDegreePart D k sy (SKM.SYM.coefficientDegree D sy a) :=
      Submodule.subset_span ⟨a, rfl, rfl⟩
    have hg := elvQuotientMap_source_mem_degree D sy Sc hc cutoff hc'
      (i.nf_mem_homDegree D Sc sy)
    have hg' : elvHomQuotient D Sc cutoff v w
        (sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k a) i.nf) ∈
        elvHomDegree D sy Sc hc cutoff v w
          (SKM.SYM.coefficientDegree D sy a + i.deg D sy) := by
      simpa only [elvHomQuotient_source, elvQuotientMap_source] using hg
    simp only [degreeBelow, Submodule.mem_iInf, LinearMap.mem_ker]
    intro n hn
    have hi : SKM.SYM.coefficientDegree D sy a + i.deg D sy < B := ha.2
    exact dproj_of_mem_ne hg' (by omega)
  | zero => simpa only [map_zero] using (degreeBelow D sy Sc hc cutoff v w B).zero_mem
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul c f _ hf => simpa only [map_smul] using Submodule.smul_mem _ c hf

include hc in
/-- Joint source detection uses the actual cyclotomic and weighted coefficient
ideal, with the existing kernel bound and no action-faithfulness premise. -/
theorem exists_jointPBWWindow_truncated_injective (ν : List I) :
    ∃ L : ℤ, ∀ (cutoff : I → ℕ) (N d : ℕ) (C B : ℤ),
      (∀ i, d ≤ cutoff i) →
      (∀ j ∈ ν, C ≤ 2 * sy.d j * cutoff j) →
      B ≤ L + min C (2 * N) + L →
      ∀ v w : List I, v.Perm ν → w.Perm ν →
      Function.Injective (fun x : jointPBWWindow D sy Sc d v w B =>
        (truncatedIdeal D Sc cutoff N v w).mkQ
          (elvHomQuotient D Sc cutoff v w x.val)) := by
  obtain ⟨L, hL⟩ := exists_truncated_degreeBelow_injective D sy Sc hc ν
  refine ⟨L, fun cutoff N d C B hd hC hB v w hv hw x y hxy => ?_⟩
  have he := hL cutoff N C B hC hB v w hv hw
    (a₁ := ⟨_, jointPBWWindow_quotient_mem_degreeBelow D sy Sc hc cutoff d v w B x.property⟩)
    (a₂ := ⟨_, jointPBWWindow_quotient_mem_degreeBelow D sy Sc hc cutoff d v w B y.property⟩)
    hxy
  have hq := congrArg Subtype.val he
  have hs := elvHomQuotient_injective_coefficientWindow D Sc cutoff d hd v w
    (a₁ := ⟨x.val, jointPBWWindow_le_coefficientWindow D sy Sc d v w B x.property⟩)
    (a₂ := ⟨y.val, jointPBWWindow_le_coefficientWindow D sy Sc d v w B y.property⟩)
    hq
  have hval : x.val = y.val := congrArg
    (fun z : coefficientWindowSource D Sc d v w => z.val) hs
  exact Subtype.ext hval

include hc in
/-- A uniform cofinal schedule detects this fixed source window. The bound on
all colours retains coefficients supported outside the boundary content. -/
theorem jointPBWWindow_detected_at_high_cutoffs (ν : List I) (d : ℕ) (B : ℤ) :
    ∃ K : ℕ, ∀ (cutoff : I → ℕ) (N : ℕ),
      (∀ i, K ≤ cutoff i) → K ≤ N →
      ∀ v w : List I, v.Perm ν → w.Perm ν →
      Function.Injective (fun x : jointPBWWindow D sy Sc d v w B =>
        (truncatedIdeal D Sc cutoff N v w).mkQ
          (elvHomQuotient D Sc cutoff v w x.val)) := by
  obtain ⟨L, hL⟩ := exists_jointPBWWindow_truncated_injective D sy Sc hc ν
  let K := max d (B - (L + L)).toNat
  refine ⟨K, fun cutoff N hcut hN v w hv hw => ?_⟩
  apply hL cutoff N d (2 * K) B ?_ ?_ ?_ v w hv hw
  · intro i
    exact le_trans (Nat.le_max_left _ _) (hcut i)
  · intro j _
    have hd : (1 : ℤ) ≤ sy.d j := by have := sy.pos j; omega
    have hkj : (K : ℤ) ≤ cutoff j := by exact_mod_cast hcut j
    have hm := mul_le_mul_of_nonneg_right hd
      (Nat.cast_nonneg (cutoff j) : (0 : ℤ) ≤ _)
    nlinarith only [hm, hkj]
  · have hk : B - (L + L) ≤ (K : ℤ) := by dsimp [K]; omega
    have hkn : (K : ℤ) ≤ N := by exact_mod_cast hN
    have hk0 : (0 : ℤ) ≤ K := Nat.cast_nonneg _
    omega

end OddMath.QuiverHecke.ELVOld
