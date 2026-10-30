/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelDegree

/-! # Degree separation in the coefficient-truncated quotient

The coefficient-weight ideal also has a lower integer degree: coefficient
weight contributes at least twice its value. Together with the cyclotomic
bound this separates bounded-degree source Homs in the actual `TruncatedOld`.
-/
noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous)

/-- All coefficient colours, including those outside the boundary, have
integer degree at least twice their weight. -/
theorem twice_coefficientWeight_le_degree (a : SKM.SYM.CoefficientIndex D) :
    2 * (SKM.SYM.coefficientWeight D a : ℤ) ≤ SKM.SYM.coefficientDegree D sy a := by
  unfold SKM.SYM.coefficientDegree SKM.SYM.coefficientWeight
  push_cast
  rw [mul_add, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    have hd : (2 : ℤ) ≤ 2 * sy.d i.1 := by have := sy.pos i.1; omega
    have h := mul_le_mul_of_nonneg_right hd
      (Nat.cast_nonneg (SKM.SYM.elementaryWeight D i) : (0 : ℤ) ≤ _)
    have h' := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (a.1 i) : (0 : ℤ) ≤ _)
    nlinarith only [h']
  · calc
      2 * (a.2.card : ℤ) = ∑ _i ∈ a.2, (2 : ℤ) := by simp [mul_comm]
      _ ≤ ∑ i ∈ a.2, 2 * sy.d i.1 := Finset.sum_le_sum fun i _ => by
        have := sy.pos i.1
        omega

/-- The weight-truncation ideal cannot acquire low degrees from its two
arbitrary multipliers. -/
theorem coefficientHomIdeal_dproj_eq_zero_of_lower_bound (ν : List I) (L : ℤ)
    (hL : ∀ v w : List I, v.Perm ν → w.Perm ν →
      ∀ cutoff : I → ℕ, ∀ n, n < L → elvHomDegree D sy Sc hc cutoff v w n = ⊥)
    (cutoff : I → ℕ) (N : ℕ)
    {v w : List I} (hv : v.Perm ν) (hw : w.Perm ν)
    {f : hom D Sc cutoff v w} (hf : f ∈ coefficientHomIdeal D Sc cutoff N v w)
    (n : ℤ) (hn : n < L + 2 * N + L) :
    homDproj D sy Sc hc cutoff n f = 0 := by
  let _ := elvHomGrading D sy Sc hc cutoff
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t, c, hcw, a, b, rfl⟩ := hf
    by_cases ht : t.Perm ν
    · change dproj k n (a ≫ coefficientIdentity D Sc cutoff t
        (SKM.SYM.coefficientBasis D k c) ≫ b) = 0
      refine induction_on_degree (R := k) a (by simp) (fun r a ha => ?_)
        (fun a a' ha ha' => ?_)
      · refine induction_on_degree (R := k) b (by simp) (fun s b hb => ?_)
          (fun b b' hb hb' => ?_)
        · by_cases hr : r < L
          · have he : a = 0 := by
              change a ∈ elvHomDegree D sy Sc hc cutoff v t r at ha
              rwa [hL v t hv ht cutoff r hr] at ha
            subst a
            simp
          · by_cases hs : s < L
            · have he : b = 0 := by
                change b ∈ elvHomDegree D sy Sc hc cutoff t w s at hb
                rwa [hL t w ht hw cutoff s hs] at hb
              subst b
              simp
            · have hg := comp_mem_degree ha
                (comp_mem_degree (coefficientIdentity_basis_degree D Sc cutoff sy hc t c) hb)
              apply dproj_of_mem_ne hg
              have h := twice_coefficientWeight_le_degree D sy c
              have hw' : (N : ℤ) ≤ SKM.SYM.coefficientWeight D c := by exact_mod_cast hcw
              omega
        · simp only [Preadditive.comp_add, map_add, hb, hb', add_zero]
      · simp only [Preadditive.add_comp, map_add, ha, ha', add_zero]
    · have he : a = 0 := hom_eq_zero_of_not_perm D Sc cutoff
        (fun h => ht (h.trans hv)) a
      subst a
      simp
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

/-- The lower bound for the complete defining ideal of `TruncatedOld`. -/
theorem exists_truncatedIdeal_degree_bound (ν : List I) :
    ∃ L : ℤ, ∀ (cutoff : I → ℕ) (N : ℕ) (C : ℤ),
      (∀ j ∈ ν, C ≤ 2 * sy.d j * cutoff j) →
      ∀ v w : List I, v.Perm ν → w.Perm ν →
      ∀ f : hom D Sc cutoff v w, f ∈ truncatedIdeal D Sc cutoff N v w →
      ∀ n : ℤ, n < L + min C (2 * N) + L → homDproj D sy Sc hc cutoff n f = 0 := by
  obtain ⟨L, hL⟩ := exists_content_lower_bound D sy Sc hc ν
  refine ⟨L, fun cutoff N C hC v w hv hw f hf n hn => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add,
    ideal_dproj_eq_zero_of_lower_bound D sy Sc hc ν L hL cutoff C hC hv hw ha n (by omega),
    coefficientHomIdeal_dproj_eq_zero_of_lower_bound D sy Sc hc ν L hL cutoff N hv hw hb n
      (by omega), add_zero]

/-- The source submodule with integer support strictly below `B`. -/
def degreeBelow (cutoff : I → ℕ) (v w : List I) (B : ℤ) :
    Submodule k (hom D Sc cutoff v w) :=
  ⨅ n : ℤ, ⨅ (_ : B ≤ n), LinearMap.ker (homDproj D sy Sc hc cutoff n)

/-- The actual coefficient-truncated quotient detects every bounded-degree
source Hom once both cutoffs exceed its derived kernel bound. -/
theorem exists_truncated_degreeBelow_injective (ν : List I) :
    ∃ L : ℤ, ∀ (cutoff : I → ℕ) (N : ℕ) (C B : ℤ),
      (∀ j ∈ ν, C ≤ 2 * sy.d j * cutoff j) → B ≤ L + min C (2 * N) + L →
      ∀ v w : List I, v.Perm ν → w.Perm ν →
      Function.Injective (fun x : degreeBelow D sy Sc hc cutoff v w B =>
        (truncatedIdeal D Sc cutoff N v w).mkQ x.val) := by
  obtain ⟨L, hL⟩ := exists_truncatedIdeal_degree_bound D sy Sc hc ν
  refine ⟨L, fun cutoff N C B hC hB v w hv hw x y hxy => ?_⟩
  let _ := elvHomGrading D sy Sc hc cutoff
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hm : x.val - y.val ∈ truncatedIdeal D Sc cutoff N v w :=
    (Submodule.Quotient.eq _).mp hxy
  have hd : x.val - y.val ∈ degreeBelow D sy Sc hc cutoff v w B :=
    Submodule.sub_mem _ x.property y.property
  have hz : ∀ n : ℤ, dproj k n (x.val - y.val) = 0 := by
    intro n
    by_cases hn : n < B
    · exact hL cutoff N C hC v w hv hw (x.val - y.val) hm n (lt_of_lt_of_le hn hB)
    · have hh := hd
      simp only [degreeBelow, Submodule.mem_iInf] at hh
      exact hh n (by omega)
  have hzero := mem_degree_of_dproj (R := k) (n := 0) (fun m _ => hz m)
  have h := hz 0
  rwa [dproj_of_mem hzero] at h

end OddMath.QuiverHecke.ELVOld
