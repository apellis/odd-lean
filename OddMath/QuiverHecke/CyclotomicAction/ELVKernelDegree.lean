/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVLowerDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModule
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTruncation
import OddMath.QuiverHecke.CentreFinite

/-! # Lower degree bounds for cyclotomic kernels

Finite permutations of the boundary content give a uniform lower source
bound without finiteness of the colour set. Homogeneous sandwiches of the
first-position relation then have a cutoff-dependent lower degree.
-/
noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous)

/-- Different contents have zero full coefficient Hom. -/
theorem hom_eq_zero_of_not_perm (cutoff : I → ℕ) {v w : List I}
    (h : ¬ w.Perm v) (f : hom D Sc cutoff v w) : f = 0 := by
  change f = (0 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ⊗[k]
    ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)))
  refine TensorProduct.inductionOn (motive := fun z => z = 0) f
    (fun a g => ?_) (fun a b ha hb => ?_)
  · rw [QuiverHecke.hom_eq_zero_of_not_perm D Sc h g, TensorProduct.tmul_zero]
  · rw [ha, hb, add_zero]

/-- One lower bound for every pair of words in a fixed content and every cutoff. -/
theorem exists_content_lower_bound (ν : List I) :
    ∃ L : ℤ, ∀ (v w : List I), v.Perm ν → w.Perm ν →
      ∀ cutoff : I → ℕ, ∀ n, n < L →
        elvHomDegree D sy Sc hc cutoff v w n = ⊥ := by
  classical
  let b : ContentWords ν × ContentWords ν → ℤ := fun q =>
    (exists_elvHomDegree_lower_bound D sy Sc hc q.1.val q.2.val).choose
  obtain ⟨L, hL⟩ := (Set.finite_range b).bddBelow
  refine ⟨L, fun v w hv hw cutoff n hn => ?_⟩
  have h := hL (Set.mem_range_self (⟨⟨v, hv⟩, ⟨w, hw⟩⟩ : ContentWords ν × ContentWords ν))
  exact (exists_elvHomDegree_lower_bound D sy Sc hc v w).choose_spec cutoff n
    (lt_of_lt_of_le hn h)

/-- Low-degree projections of the old cyclotomic ideal vanish. The only
bound supplied as an argument concerns the source Hom, not this ideal. -/
theorem ideal_dproj_eq_zero_of_lower_bound (ν : List I) (L : ℤ)
    (hL : ∀ v w : List I, v.Perm ν → w.Perm ν →
      ∀ cutoff : I → ℕ, ∀ n, n < L → elvHomDegree D sy Sc hc cutoff v w n = ⊥)
    (cutoff : I → ℕ) (C : ℤ)
    (hC : ∀ j ∈ ν, C ≤ 2 * sy.d j * cutoff j)
    {v w : List I} (hv : v.Perm ν) (hw : w.Perm ν)
    {f : hom D Sc cutoff v w} (hf : f ∈ ideal D Sc cutoff v w)
    (n : ℤ) (hn : n < L + C + L) :
    homDproj D sy Sc hc cutoff n f = 0 := by
  let _ := elvHomGrading D sy Sc hc cutoff
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, t, a, b, rfl⟩ := hf
    by_cases ht : (j :: t).Perm ν
    · have hj : j ∈ ν := ht.mem_iff.mp (by simp)
      change dproj k n (a ≫ relation D Sc cutoff j t ≫ b) = 0
      refine induction_on_degree (R := k) a (by simp) (fun r a ha => ?_)
        (fun a a' ha ha' => ?_)
      · refine induction_on_degree (R := k) b (by simp) (fun s b hb => ?_)
          (fun b b' hb hb' => ?_)
        · by_cases hr : r < L
          · have he : a = 0 := by
              change a ∈ elvHomDegree D sy Sc hc cutoff v (j :: t) r at ha
              rwa [hL v (j :: t) hv ht cutoff r hr] at ha
            subst a
            simp
          · by_cases hs : s < L
            · have he : b = 0 := by
                change b ∈ elvHomDegree D sy Sc hc cutoff (j :: t) w s at hb
                rwa [hL (j :: t) w ht hw cutoff s hs] at hb
              subst b
              simp
            · have hg := comp_mem_degree ha
                (comp_mem_degree (relation_mem_degree D sy Sc hc cutoff j t) hb)
              apply dproj_of_mem_ne hg
              have h := hC j hj
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

/-- The old ideal has a lower degree bound derived from PBW, uniform in
non-uniform cyclotomic cutoffs at the colours of the boundary content. -/
theorem exists_ideal_degree_bound (ν : List I) :
    ∃ L : ℤ, ∀ (cutoff : I → ℕ) (C : ℤ),
      (∀ j ∈ ν, C ≤ 2 * sy.d j * cutoff j) →
      ∀ v w : List I, v.Perm ν → w.Perm ν →
      ∀ f : hom D Sc cutoff v w, f ∈ ideal D Sc cutoff v w →
      ∀ n : ℤ, n < L + C + L → homDproj D sy Sc hc cutoff n f = 0 := by
  obtain ⟨L, hL⟩ := exists_content_lower_bound D sy Sc hc ν
  exact ⟨L, fun cutoff C hC v w hv hw f hf n hn =>
    ideal_dproj_eq_zero_of_lower_bound D sy Sc hc ν L hL cutoff C hC hv hw hf n hn⟩

/-- On each sufficiently low homogeneous part the actual old quotient map
is injective, with its kernel bound derived rather than assumed. -/
theorem exists_old_degree_injective (ν : List I) :
    ∃ L : ℤ, ∀ (cutoff : I → ℕ) (C : ℤ),
      (∀ j ∈ ν, C ≤ 2 * sy.d j * cutoff j) →
      ∀ v w : List I, v.Perm ν → w.Perm ν →
      ∀ n : ℤ, n < L + C + L →
      Function.Injective (fun x : elvHomDegree D sy Sc hc cutoff v w n =>
        (ideal D Sc cutoff v w).mkQ x.val) := by
  obtain ⟨L, hL⟩ := exists_ideal_degree_bound D sy Sc hc ν
  refine ⟨L, fun cutoff C hC v w hv hw n hn x y hxy => ?_⟩
  let _ := elvHomGrading D sy Sc hc cutoff
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hm : x.val - y.val ∈ ideal D Sc cutoff v w :=
    (Submodule.Quotient.eq _).mp hxy
  have hz := hL cutoff C hC v w hv hw (x.val - y.val) hm n hn
  have hd : x.val - y.val ∈ elvHomDegree D sy Sc hc cutoff v w n :=
    Submodule.sub_mem _ x.property y.property
  change dproj k n (x.val - y.val) = 0 at hz
  rwa [dproj_of_mem hd] at hz

end OddMath.QuiverHecke.ELVOld
