/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVHomGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVOldBalancedTensor

/-! # Integer and super gradings of the old ELV quotient

Integer projections preserve the two-sided old cyclotomic ideal: decompose
both surrounding coefficient-category morphisms into homogeneous summands,
then use the homogeneity of the first-position relation. The quotient is
`ELVOld.Old` with its full exterior coefficients, not a replacement quotient.

The degree images form an internal direct sum under `Sc.Homogeneous`.
Total super parity descends independently and commutes with integer projection;
no invertibility of two is used. The existing signed `oldCompose` adds integer
degrees. No positive-content support bound or enlarged target action is claimed.
-/

noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous) (cutoff : I → ℕ)

/-- Integer projection on the coefficient-category Homs. -/
abbrev homDproj {v w : List I} (n : ℤ) : hom D Sc cutoff v w →ₗ[k] hom D Sc cutoff v w :=
  letI := elvHomGrading D sy Sc hc cutoff
  dproj k n

/-- Integer projection preserves the two-sided old cyclotomic ideal. -/
theorem ideal_dproj_mem {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ ideal D Sc cutoff v w) (n : ℤ) :
    homDproj D sy Sc hc cutoff n f ∈ ideal D Sc cutoff v w := by
  let _ := elvHomGrading D sy Sc hc cutoff
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, t, a, b, rfl⟩ := hf
    change dproj k n (a ≫ relation D Sc cutoff j t ≫ b) ∈ _
    refine induction_on_degree (R := k) a (by simp) (fun r a ha => ?_)
      (fun a a' ha ha' => ?_)
    · refine induction_on_degree (R := k) b (by simp) (fun s b hb => ?_)
        (fun b b' hb hb' => ?_)
      · have hg := comp_mem_degree ha
          (comp_mem_degree (relation_mem_degree D sy Sc hc cutoff j t) hb)
        by_cases h : r + (2 * sy.d j * cutoff j + s) = n
        · rw [← h, dproj_of_mem hg]
          exact Submodule.subset_span ⟨j, t, a, b, rfl⟩
        · rw [dproj_of_mem_ne hg h]
          exact Submodule.zero_mem _
      · simpa only [Preadditive.comp_add, map_add] using Submodule.add_mem _ hb hb'
    · simpa only [Preadditive.add_comp, map_add] using Submodule.add_mem _ ha ha'
  | zero => simpa only [map_zero] using (ideal D Sc cutoff v w).zero_mem
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

/-- The degree parts in the old quotient are images of the original Hom parts. -/
def oldDegree (v w : List I) (n : ℤ) : Submodule k (Old D Sc cutoff v w) :=
  (elvHomDegree D sy Sc hc cutoff v w n).map (ideal D Sc cutoff v w).mkQ

/-- Integer component projection on the old cyclotomic quotient. -/
def oldDproj (v w : List I) (n : ℤ) :
    Old D Sc cutoff v w →ₗ[k] Old D Sc cutoff v w :=
  (ideal D Sc cutoff v w).mapQ (ideal D Sc cutoff v w) (homDproj D sy Sc hc cutoff n)
    (fun _ hf => ideal_dproj_mem D sy Sc hc cutoff hf n)

@[simp] theorem oldDproj_mk (v w : List I) (n : ℤ) (f : hom D Sc cutoff v w) :
    oldDproj D sy Sc hc cutoff v w n ((ideal D Sc cutoff v w).mkQ f) =
      (ideal D Sc cutoff v w).mkQ (homDproj D sy Sc hc cutoff n f) := rfl

theorem oldDproj_of_mem {v w : List I} {m : ℤ} {f : Old D Sc cutoff v w}
    (hf : f ∈ oldDegree D sy Sc hc cutoff v w m) (n : ℤ) :
    oldDproj D sy Sc hc cutoff v w n f = if m = n then f else 0 := by
  let _ := elvHomGrading D sy Sc hc cutoff
  obtain ⟨a, ha, rfl⟩ := hf
  rw [oldDproj_mk]
  split_ifs with h
  · subst n
    rw [dproj_of_mem ha]
  · rw [dproj_of_mem_ne ha h, map_zero]

/-- The original old quotient has an internal integer grading. -/
theorem oldDegree_internal (v w : List I) :
    DirectSum.IsInternal (oldDegree D sy Sc hc cutoff v w) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s f hf he n hn
    have hh := congrArg (oldDproj D sy Sc hc cutoff v w n) he
    rw [map_sum, map_zero] at hh
    have hsum : (∑ i ∈ s, oldDproj D sy Sc hc cutoff v w n (f i)) = f n := by
      calc
        _ = ∑ i ∈ s, if i = n then f i else 0 :=
          Finset.sum_congr rfl (fun i hi => oldDproj_of_mem D sy Sc hc cutoff (hf i hi) n)
        _ = f n := by simp [hn]
    exact hsum.symm.trans hh
  · change (⨆ n, (elvHomDegree D sy Sc hc cutoff v w n).map
      (ideal D Sc cutoff v w).mkQ) = ⊤
    rw [← Submodule.map_iSup, (elvHomDegree_internal D sy Sc hc cutoff v w).submodule_iSup_eq_top]
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)

/-- The quotient projection is homogeneous of degree zero. -/
theorem mkQ_mem_oldDegree {v w : List I} {n : ℤ} {f : hom D Sc cutoff v w}
    (hf : f ∈ elvHomDegree D sy Sc hc cutoff v w n) :
    (ideal D Sc cutoff v w).mkQ f ∈ oldDegree D sy Sc hc cutoff v w n :=
  Submodule.mem_map_of_mem hf

/-- Total super parity preserves the integer degree on the old quotient. -/
theorem oldTwist_mem_oldDegree (p : ZMod 2) {v w : List I} {n : ℤ}
    {f : Old D Sc cutoff v w} (hf : f ∈ oldDegree D sy Sc hc cutoff v w n) :
    oldTwist D Sc cutoff p v w f ∈ oldDegree D sy Sc hc cutoff v w n := by
  let _ := elvHomGrading D sy Sc hc cutoff
  obtain ⟨a, ha, rfl⟩ := hf
  exact Submodule.mem_map_of_mem (twist_mem_degree p ha)

/-- The existing signed old action adds integer degrees; its twist uses total parity. -/
theorem oldCompose_mem_oldDegree (p : ZMod 2) {v s t : List I} {m n : ℤ}
    {r : hom D Sc cutoff s t} {f : Old D Sc cutoff v s}
    (hr : r ∈ elvHomDegree D sy Sc hc cutoff s t n)
    (hf : f ∈ oldDegree D sy Sc hc cutoff v s m) :
    oldCompose D Sc cutoff p r f ∈ oldDegree D sy Sc hc cutoff v t (m + n) := by
  let _ := elvHomGrading D sy Sc hc cutoff
  obtain ⟨a, ha, rfl⟩ := hf
  rw [oldCompose_mk]
  exact mkQ_mem_oldDegree D sy Sc hc cutoff (comp_mem_degree ha (twist_mem_degree p hr))

/-- Super parity projections also preserve the ideal, without dividing by two. -/
theorem ideal_proj_mem {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ ideal D Sc cutoff v w) (p : ZMod 2) :
    Supercategory.proj k p f ∈ ideal D Sc cutoff v w := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, t, a, b, rfl⟩ := hf
    refine Supercategory.induction_on (R := k) a (by simp) (fun r a ha => ?_)
      (fun a a' ha ha' => ?_)
    · refine Supercategory.induction_on (R := k) b (by simp) (fun s b hb => ?_)
        (fun b b' hb hb' => ?_)
      · have hg := Supercategory.comp_mem ha
          (Supercategory.comp_mem (relation_mem_parity D Sc cutoff j t) hb)
        by_cases h : r + ((cutoff j : ZMod 2) * D.parity j + s) = p
        · rw [← h, Supercategory.proj_of_mem hg]
          exact Submodule.subset_span ⟨j, t, a, b, rfl⟩
        · rw [Supercategory.proj_of_mem_ne hg h]
          exact Submodule.zero_mem _
      · simpa only [Preadditive.comp_add, map_add] using Submodule.add_mem _ hb hb'
    · simpa only [Preadditive.add_comp, map_add] using Submodule.add_mem _ ha ha'
  | zero => simpa only [map_zero] using (ideal D Sc cutoff v w).zero_mem
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

/-- Super parity on the old quotient, distinct from integer degree modulo two. -/
def oldParity (v w : List I) (p : ZMod 2) : Submodule k (Old D Sc cutoff v w) :=
  (Supercategory.parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff w) p).map
    (ideal D Sc cutoff v w).mkQ

/-- The descended total parity projection. -/
def oldProj (v w : List I) (p : ZMod 2) :
    Old D Sc cutoff v w →ₗ[k] Old D Sc cutoff v w :=
  (ideal D Sc cutoff v w).mapQ (ideal D Sc cutoff v w) (Supercategory.proj k p)
    (fun _ hf => ideal_proj_mem D Sc cutoff hf p)

@[simp] theorem oldProj_mk (v w : List I) (p : ZMod 2) (f : hom D Sc cutoff v w) :
    oldProj D Sc cutoff v w p ((ideal D Sc cutoff v w).mkQ f) =
      (ideal D Sc cutoff v w).mkQ (Supercategory.proj k p f) := rfl

theorem oldProj_of_mem {v w : List I} {q : ZMod 2} {f : Old D Sc cutoff v w}
    (hf : f ∈ oldParity D Sc cutoff v w q) (p : ZMod 2) :
    oldProj D Sc cutoff v w p f = if q = p then f else 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [oldProj_mk]
  split_ifs with h
  · subst p
    rw [Supercategory.proj_of_mem ha]
  · rw [Supercategory.proj_of_mem_ne ha h, map_zero]

/-- The parity images form an internal direct sum over the same ground ring. -/
theorem oldParity_internal (v w : List I) :
    DirectSum.IsInternal (oldParity D Sc cutoff v w) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s f hf he n hn
    have hh := congrArg (oldProj D Sc cutoff v w n) he
    rw [map_sum, map_zero] at hh
    have hsum : (∑ i ∈ s, oldProj D Sc cutoff v w n (f i)) = f n := by
      calc
        _ = ∑ i ∈ s, if i = n then f i else 0 :=
          Finset.sum_congr rfl (fun i hi => oldProj_of_mem D Sc cutoff (hf i hi) n)
        _ = f n := by simp [hn]
    exact hsum.symm.trans hh
  · change (⨆ p, (Supercategory.parity (R := k) (obj D Sc cutoff v)
      (obj D Sc cutoff w) p).map (ideal D Sc cutoff v w).mkQ) = ⊤
    let _ := Supercategory.decomposition k (obj D Sc cutoff v) (obj D Sc cutoff w)
    rw [← Submodule.map_iSup,
      (DirectSum.Decomposition.isInternal (Supercategory.parity (R := k)
        (obj D Sc cutoff v) (obj D Sc cutoff w))).submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)

/-- Parity projection preserves each integer component in the old quotient. -/
theorem oldProj_mem_oldDegree (p : ZMod 2) {v w : List I} {n : ℤ}
    {f : Old D Sc cutoff v w} (hf : f ∈ oldDegree D sy Sc hc cutoff v w n) :
    oldProj D Sc cutoff v w p f ∈ oldDegree D sy Sc hc cutoff v w n := by
  let _ := elvHomGrading D sy Sc hc cutoff
  obtain ⟨a, ha, rfl⟩ := hf
  exact Submodule.mem_map_of_mem (proj_mem_degree p ha)

/-- The integer and total-parity component projections commute after quotienting. -/
theorem oldProj_oldDproj (p : ZMod 2) (n : ℤ) (v w : List I)
    (f : Old D Sc cutoff v w) :
    oldProj D Sc cutoff v w p (oldDproj D sy Sc hc cutoff v w n f) =
      oldDproj D sy Sc hc cutoff v w n (oldProj D Sc cutoff v w p f) := by
  let _ := elvHomGrading D sy Sc hc cutoff
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v w).mkQ_surjective f
  simp only [oldDproj_mk, oldProj_mk]
  exact congrArg (ideal D Sc cutoff v w).mkQ (proj_dproj p n a)

end OddMath.QuiverHecke.ELVOld
