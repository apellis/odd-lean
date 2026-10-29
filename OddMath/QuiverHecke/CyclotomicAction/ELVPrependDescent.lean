/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPrependCrossTail

/-!
# Descent of ELV prepend extraction through all old relations

The old-only coordinate comparison needed by `DeformedGlobalQP.md` §1.
Cross-source rebasing retains the prescribed moving tail. A normal-form index
is selected only from a nonzero old Hom, so empty old Hom spaces are allowed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace PrependIdx
variable {i : I} {v s w : List I}

private theorem shuffle_word_transport {n m : ℕ} (h : n = m) (d : PrependShuffle m) :
    Categorification.TypeA.canWord (n + 1) (↑(h.symm ▸ d : PrependShuffle n))⁻¹ =
      Categorification.TypeA.canWord (m + 1) d.1⁻¹ := by
  subst m
  rfl

/-- Rebase a moving tail to another source using an actual old normal form. -/
def rebase (z : PrependIdx i s w) (y : NFIdx v z.oldTarget) : PrependIdx i v w := by
  have hl : v.length = s.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt, oldTarget] using hh
  refine ⟨(z.1.1, y.1.1, y.1.2, hl.symm ▸ z.1.2.2.2), y.2.1, y.2.2.1, ?_⟩
  have he := tgt_shift [i] v (cw (Categorification.TypeA.canWord v.length y.1.2))
  simp only [List.length_singleton, cw_map_shift, List.singleton_append] at he
  simp only [prependCrossingWord, cw_append, tgt_append, he, y.tgt_cw]
  rw [shuffle_word_transport hl z.1.2.2.2]
  exact z.moving_target

 theorem rebase_target (z : PrependIdx i s w) (y : NFIdx v z.oldTarget) :
    (z.rebase y).oldTarget = z.oldTarget := y.tgt_cw

end PrependIdx
namespace ELVOld

private theorem tail_cl_heq {a b w : List I} {L M : List PG}
    (hab : a = b) (hLM : L = M) (ha : SChain a (pl a L) w)
    (hb : SChain b (pl b M) w) : HEq (cl D Sc a w L ha) (cl D Sc b w M hb) := by
  subst b
  subst M
  rfl

/-- Rebasing changes only the old index, not the positioned moving diagram. -/
theorem prependTail_rebase {i : I} {v s w : List I} (z : PrependIdx i s w)
    (y : NFIdx v z.oldTarget) :
    HEq (prependTail D Sc (z.rebase y)) (prependTail D Sc z) := by
  apply tail_cl_heq
  · exact congrArg (List.cons i) (z.rebase_target y)
  · dsimp only [PrependIdx.rebase]
    have hl : v.length = s.length := by
      have hh := congrArg List.length y.tgt_cw
      simpa only [length_tgt, PrependIdx.oldTarget] using hh
    rw [PrependIdx.shuffle_word_transport hl z.1.2.2.2]

/-- Equal moving keys give the same positioned tail, including its source. -/
theorem prependTail_heq_of_tailKey_eq {i : I} {v w : List I}
    (x z : PrependIdx i v w) (h : x.tailKey = z.tailKey) :
    HEq (prependTail D Sc x) (prependTail D Sc z) := by
  apply tail_cl_heq
  · exact congrArg (List.cons i) (x.oldTarget_eq_of_tailKey_eq z h)
  · have hn := congrArg Prod.fst h
    have hd := congrArg Prod.snd h
    change x.1.1 = z.1.1 at hn
    change x.1.2.2.2 = z.1.2.2.2 at hd
    rw [hn, hd]

private theorem insert_tail_transport {i : I} {v t t' w : List I}
    (e : t = t') (r : hom D Sc cutoff v t)
    (f : (pres D Sc).obj (ob D (i :: t)) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D (i :: t')) ⟶ (pres D Sc).obj (ob D w))
    (h : HEq f g) :
    insert D Sc cutoff i v t r ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f :
        hom D Sc cutoff (i :: t) w) =
    insert D Sc cutoff i v t' (e ▸ r) ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] g :
        hom D Sc cutoff (i :: t') w) := by
  subst t'
  cases h
  rfl

/-- Old ideal coefficients vanish at every moving coordinate. -/
theorem prependExtractOldQuotient_insert_ideal_tail (p : ZMod 2)
    {i : I} {v w : List I} (x z : PrependIdx i v w)
    (r : hom D Sc cutoff v z.oldTarget) (hr : r ∈ ideal D Sc cutoff v z.oldTarget) :
    prependExtractOldQuotient D Sc cutoff p x
      (insert D Sc cutoff i v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc z : hom D Sc cutoff (i :: z.oldTarget) w)) = 0 := by
  by_cases h : x.tailKey = z.tailKey
  · have ht := z.oldTarget_eq_of_tailKey_eq x h.symm
    rw [insert_tail_transport D Sc cutoff ht r _ _
      (prependTail_heq_of_tailKey_eq D Sc z x h.symm)]
    apply (prependExtractOldQuotient_insert_tail_eq_zero_iff D Sc cutoff p x _).mpr
    exact (show ∀ {t t' : List I} (e : t = t') (a : hom D Sc cutoff v t),
      a ∈ ideal D Sc cutoff v t → (e ▸ a) ∈ ideal D Sc cutoff v t' from
        by intro t t' e; subst t'; exact fun _ ha => ha) ht r hr
  · exact prependExtractOldQuotient_insert_off_tail D Sc cutoff p x z h r

/-- A nonzero old Hom supplies an actual normal-form index; empty Homs are not assumed inhabited. -/
theorem exists_oldIndex_of_ne_zero {v t : List I} (r : hom D Sc cutoff v t) (hr : r ≠ 0) :
    Nonempty (NFIdx v t) := by
  by_contra hn
  have : IsEmpty (NFIdx v t) := not_nonempty_iff.mp hn
  apply hr
  apply (oldAffineEquiv D Sc cutoff v t).injective
  ext y
  exact isEmptyElim y

/-- Cross-source old ideal coefficients vanish, without an inhabitation assumption on old Homs. -/
theorem prependExtractOldQuotient_insert_ideal_cross_source (p : ZMod 2)
    {i : I} {v s w : List I} (x : PrependIdx i v w) (z : PrependIdx i s w)
    (r : hom D Sc cutoff v z.oldTarget) (hr : r ∈ ideal D Sc cutoff v z.oldTarget) :
    prependExtractOldQuotient D Sc cutoff p x
      (insert D Sc cutoff i v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc z : hom D Sc cutoff (i :: z.oldTarget) w)) = 0 := by
  by_cases hz : r = 0
  · simp only [hz, map_zero, Limits.zero_comp]
  · obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff r hz
    have ht := (z.rebase_target y).symm
    rw [insert_tail_transport D Sc cutoff ht r _ _ (prependTail_rebase D Sc z y).symm]
    apply prependExtractOldQuotient_insert_ideal_tail
    exact (show ∀ {t t' : List I} (e : t = t') (a : hom D Sc cutoff v t),
      a ∈ ideal D Sc cutoff v t → (e ▸ a) ∈ ideal D Sc cutoff v t' from
        by intro t t' e; subst t'; exact fun _ ha => ha) ht r hr

/-- Every old-only generator has zero extracted old quotient coordinate, for arbitrary continuation. -/
theorem prependExtractOldQuotient_old_generator (p : ZMod 2)
    {i : I} {v s w : List I} (x : PrependIdx i v w)
    (r : hom D Sc cutoff v s) (hr : r ∈ ideal D Sc cutoff v s)
    (h : hom D Sc cutoff (i :: s) w) :
    prependExtractOldQuotient D Sc cutoff p x (insert D Sc cutoff i v s r ≫ h) = 0 := by
  obtain ⟨f, rfl⟩ := (prependAffineEquiv D Sc cutoff i s w).symm.surjective h
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Limits.comp_zero]
  | add f g hf hg => simp only [map_add, Preadditive.comp_add, hf, hg, add_zero]
  | single z a =>
    rw [prependAffineEquiv_symm_single, ← prepend_insert_twisted_coefficient D Sc cutoff z a,
      ← Category.assoc, ← insert_comp]
    exact prependExtractOldQuotient_insert_ideal_cross_source D Sc cutoff p x z _
      (ideal_comp D Sc cutoff hr _)

/-- Extraction kills the entire old-only relation span, not just prescribed-source tails. -/
theorem prependExtractOldQuotient_relations (p : ZMod 2)
    {i : I} {v w : List I} (x : PrependIdx i v w) :
    relations D Sc cutoff i v w ≤ LinearMap.ker (prependExtractOldQuotient D Sc cutoff p x) := by
  apply Submodule.span_le.mpr
  rintro f ⟨s, r, hr, h, rfl⟩
  exact prependExtractOldQuotient_old_generator D Sc cutoff p x r hr h

/-- An actual old quotient coordinate on the old-only target. -/
def prependOldCoordinate (p : ZMod 2) {i : I} {v w : List I} (x : PrependIdx i v w) :
    Target D Sc cutoff i v w →ₗ[k] Old D Sc cutoff v x.oldTarget :=
  (relations D Sc cutoff i v w).liftQ (prependExtractOldQuotient D Sc cutoff p x)
    (prependExtractOldQuotient_relations D Sc cutoff p x)

@[simp] theorem prependOldCoordinate_projection (p : ZMod 2)
    {i : I} {v w : List I} (x : PrependIdx i v w) (h : hom D Sc cutoff (i :: v) w) :
    prependOldCoordinate D Sc cutoff p x (projection D Sc cutoff i v w h) =
      prependExtractOldQuotient D Sc cutoff p x h := rfl

/-- Simultaneous old quotient coefficients, with finite support in the existing moving tails. -/
abbrev PrependOldCoordinates (i : I) (v w : List I) :=
  ⨁ (q : PrependIdx.Tail i v w), Old D Sc cutoff v q.representative.oldTarget

/-- Reconstruct the old-only target from all moving-tail old quotient coefficients. -/
def prependOldReconstruct (p : ZMod 2) (i : I) (v w : List I) :
    PrependOldCoordinates D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  DirectSum.toModule k _ _ fun q => pair D Sc cutoff p i
    ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
      prependTail D Sc q.representative)

/-- Reconstruction followed by extraction is the specified direct-sum component. -/
theorem prependOldCoordinate_reconstruct (p : ZMod 2) {i : I} {v w : List I}
    (q : PrependIdx.Tail i v w) (f : PrependOldCoordinates D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p q.representative
      (prependOldReconstruct D Sc cutoff p i v w f) = f q := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply]
  | add f g hf hg => simp only [map_add, hf, hg, DirectSum.add_apply]
  | of t a =>
    change prependOldCoordinate D Sc cutoff p q.representative
      (prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ t a)) = _
    rw [prependOldReconstruct, DirectSum.toModule_lof]
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t.representative.oldTarget).mkQ_surjective a
    rw [pair_mk, prependOldCoordinate_projection]
    by_cases ht : t = q
    · subst t
      rw [prependExtractOldQuotient_insert_tail, twist_twist, DirectSum.of_eq_same]
    · rw [prependExtractOldQuotient_insert_off_tail]
      · symm
        exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm ht)
      · intro h
        apply ht
        apply Subtype.ext
        exact t.representative_tailKey.symm.trans (h.symm.trans q.representative_tailKey)

/-- Simultaneous old quotient reconstruction is injective. -/
theorem prependOldReconstruct_injective (p : ZMod 2) (i : I) (v w : List I) :
    Function.Injective (prependOldReconstruct D Sc cutoff p i v w) := by
  intro f g h
  apply DFinsupp.ext
  intro q
  rw [← prependOldCoordinate_reconstruct D Sc cutoff p q f,
    ← prependOldCoordinate_reconstruct D Sc cutoff p q g, h]

private theorem prependOldReconstruct_range_tail (p : ZMod 2)
    {i : I} {v w : List I} (x : PrependIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    projection D Sc cutoff i v w
      (insert D Sc cutoff i v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w)) ∈
      LinearMap.range (prependOldReconstruct D Sc cutoff p i v w) := by
  let q : PrependIdx.Tail i v w := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  refine ⟨DirectSum.lof k _ _ q
    ((ideal D Sc cutoff v q.representative.oldTarget).mkQ (twist k p (ht ▸ r))), ?_⟩
  rw [prependOldReconstruct, DirectSum.toModule_lof, pair_mk, twist_twist]
  exact congrArg (projection D Sc cutoff i v w)
    (insert_tail_transport D Sc cutoff ht r _ _
      (prependTail_heq_of_tailKey_eq D Sc x q.representative hk)).symm

/-- Every old-only class has finite simultaneous old quotient coordinates. -/
theorem prependOldReconstruct_surjective (p : ZMod 2) (i : I) (v w : List I) :
    Function.Surjective (prependOldReconstruct D Sc cutoff p i v w) := by
  intro z
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  obtain ⟨f, rfl⟩ := (prependAffineEquiv D Sc cutoff i v w).symm.surjective h
  change projection D Sc cutoff i v w ((prependAffineEquiv D Sc cutoff i v w).symm f) ∈
    LinearMap.range (prependOldReconstruct D Sc cutoff p i v w)
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg => simp only [map_add]; exact Submodule.add_mem _ hf hg
  | single x a =>
    rw [prependAffineEquiv_symm_single, ← prepend_insert_twisted_coefficient D Sc cutoff x a]
    exact prependOldReconstruct_range_tail D Sc cutoff p x _

/-- The full ELV old-only quotient is the direct sum of old quotient Hom coordinates.
No flatness, finite-colour assumption, or moving cyclotomic relation is imposed. -/
def prependOldCoordinateEquiv (p : ZMod 2) (i : I) (v w : List I) :
    Target D Sc cutoff i v w ≃ₗ[k] PrependOldCoordinates D Sc cutoff i v w :=
  (LinearEquiv.ofBijective (prependOldReconstruct D Sc cutoff p i v w)
    ⟨prependOldReconstruct_injective D Sc cutoff p i v w,
      prependOldReconstruct_surjective D Sc cutoff p i v w⟩).symm

@[simp] theorem prependOldCoordinateEquiv_apply (p : ZMod 2) {i : I} {v w : List I}
    (z : Target D Sc cutoff i v w) (q : PrependIdx.Tail i v w) :
    prependOldCoordinateEquiv D Sc cutoff p i v w z q =
      prependOldCoordinate D Sc cutoff p q.representative z := by
  rw [← prependOldCoordinate_reconstruct D Sc cutoff p q]
  exact congrArg (prependOldCoordinate D Sc cutoff p q.representative)
    ((prependOldCoordinateEquiv D Sc cutoff p i v w).symm_apply_apply z)

/-- Reconstruction is the left inverse of simultaneous extraction. -/
@[simp] theorem prependOldReconstruct_coordinateEquiv (p : ZMod 2) (i : I) (v w : List I)
    (z : Target D Sc cutoff i v w) :
    prependOldReconstruct D Sc cutoff p i v w
      (prependOldCoordinateEquiv D Sc cutoff p i v w z) = z :=
  (prependOldCoordinateEquiv D Sc cutoff p i v w).symm_apply_apply z

/-- Reconstruction is the right inverse of simultaneous extraction as well. -/
@[simp] theorem prependOldCoordinateEquiv_reconstruct (p : ZMod 2) (i : I) (v w : List I)
    (f : PrependOldCoordinates D Sc cutoff i v w) :
    prependOldCoordinateEquiv D Sc cutoff p i v w
      (prependOldReconstruct D Sc cutoff p i v w f) = f :=
  (prependOldCoordinateEquiv D Sc cutoff p i v w).apply_symm_apply f

end ELVOld
end OddMath.QuiverHecke
