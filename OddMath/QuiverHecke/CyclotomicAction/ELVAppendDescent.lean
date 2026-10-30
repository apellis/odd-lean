/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendCrossTail
import OddMath.QuiverHecke.CyclotomicAction.ELVPrependDescent

/-!
# Descent of ELV append extraction through all old relations

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

namespace AppendIdx
variable {i : I} {v s w : List I}

private def shuffleTransport {n m n' m' : ℕ} (h : n + 1 = m)
    (h' : n' + 1 = m') (e : n = n') (d : AppendShuffle h) : AppendShuffle h' := by
  subst n'; subst m; subst m'; exact d

private theorem shuffle_word_transport {n m n' m' : ℕ} (h : n + 1 = m)
    (h' : n' + 1 = m') (e : n = n') (d : AppendShuffle h) :
    Categorification.TypeA.canWord m' (shuffleTransport h h' e d).1⁻¹ =
      Categorification.TypeA.canWord m d.1⁻¹ := by
  subst n'; subst m; subst m'; rfl

/-- Rebase a moving tail to another source using an actual old normal form. -/
def rebase (z : AppendIdx i s w) (y : NFIdx v z.oldTarget) : AppendIdx i v w := by
  have hl : v.length = s.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt, oldTarget] using hh
  refine ⟨(z.1.1, y.1.1, y.1.2, shuffleTransport (appendLen s i) (appendLen v i) hl.symm z.1.2.2.2), y.2.1, y.2.2.1, ?_⟩
  have he := tgt_append_right [i] (t := v)
    (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2))
  simp only [appendCrossingWord, cw_append, tgt_append, he, y.tgt_cw]
  rw [shuffle_word_transport]
  exact z.moving_target

 theorem rebase_target (z : AppendIdx i s w) (y : NFIdx v z.oldTarget) :
    (z.rebase y).oldTarget = z.oldTarget := y.tgt_cw

end AppendIdx
namespace ELVOld

private theorem tail_cl_heq {a b w : List I} {L M : List PG}
    (hab : a = b) (hLM : L = M) (ha : SChain a (pl a L) w)
    (hb : SChain b (pl b M) w) : HEq (cl D Sc a w L ha) (cl D Sc b w M hb) := by
  subst b
  subst M
  rfl

/-- Rebasing changes only the old index, not the positioned moving diagram. -/
theorem appendTail_rebase {i : I} {v s w : List I} (z : AppendIdx i s w)
    (y : NFIdx v z.oldTarget) :
    HEq (appendTail D Sc (z.rebase y)) (appendTail D Sc z) := by
  apply tail_cl_heq
  · exact congrArg (fun t => t ++ [i]) (z.rebase_target y)
  · dsimp only [AppendIdx.rebase]
    have hl : v.length = s.length := by
      have hh := congrArg List.length y.tgt_cw
      simpa only [length_tgt, AppendIdx.oldTarget] using hh
    rw [AppendIdx.shuffle_word_transport, hl]

/-- Equal moving keys give the same positioned tail, including its source. -/
theorem appendTail_heq_of_tailKey_eq {i : I} {v w : List I}
    (x z : AppendIdx i v w) (h : x.tailKey = z.tailKey) :
    HEq (appendTail D Sc x) (appendTail D Sc z) := by
  apply tail_cl_heq
  · exact congrArg (fun t => t ++ [i]) (x.oldTarget_eq_of_tailKey_eq z h)
  · have hn := congrArg Prod.fst h
    have hd := congrArg Prod.snd h
    change x.1.1 = z.1.1 at hn
    change x.1.2.2.2 = z.1.2.2.2 at hd
    rw [hn, hd]

private theorem insert_tail_transport {i : I} {v t t' w : List I}
    (e : t = t') (r : hom D Sc cutoff v t)
    (f : (pres D Sc).obj (ob D (t ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D (t' ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (h : HEq f g) :
    rightContext D Sc cutoff [i] v t r ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f :
        hom D Sc cutoff (t ++ [i]) w) =
    rightContext D Sc cutoff [i] v t' (e ▸ r) ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] g :
        hom D Sc cutoff (t' ++ [i]) w) := by
  subst t'
  cases h
  rfl

/-- Old ideal coefficients vanish at every moving coordinate. -/
theorem appendExtractOldQuotient_insert_ideal_tail (p : ZMod 2)
    {i : I} {v w : List I} (x z : AppendIdx i v w)
    (r : hom D Sc cutoff v z.oldTarget) (hr : r ∈ ideal D Sc cutoff v z.oldTarget) :
    appendExtractOldQuotient D Sc cutoff p x
      (rightContext D Sc cutoff [i] v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc z : hom D Sc cutoff (z.oldTarget ++ [i]) w)) = 0 := by
  by_cases h : x.tailKey = z.tailKey
  · have ht := z.oldTarget_eq_of_tailKey_eq x h.symm
    rw [insert_tail_transport D Sc cutoff ht r _ _
      (appendTail_heq_of_tailKey_eq D Sc z x h.symm)]
    apply (appendExtractOldQuotient_insert_tail_eq_zero_iff D Sc cutoff p x _).mpr
    exact (show ∀ {t t' : List I} (e : t = t') (a : hom D Sc cutoff v t),
      a ∈ ideal D Sc cutoff v t → (e ▸ a) ∈ ideal D Sc cutoff v t' from
        by intro t t' e; subst t'; exact fun _ ha => ha) ht r hr
  · exact appendExtractOldQuotient_insert_off_tail D Sc cutoff p x z h r

/-- Cross-source old ideal coefficients vanish, without an inhabitation assumption on old Homs. -/
theorem appendExtractOldQuotient_insert_ideal_cross_source (p : ZMod 2)
    {i : I} {v s w : List I} (x : AppendIdx i v w) (z : AppendIdx i s w)
    (r : hom D Sc cutoff v z.oldTarget) (hr : r ∈ ideal D Sc cutoff v z.oldTarget) :
    appendExtractOldQuotient D Sc cutoff p x
      (rightContext D Sc cutoff [i] v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc z : hom D Sc cutoff (z.oldTarget ++ [i]) w)) = 0 := by
  by_cases hz : r = 0
  · simp only [hz, map_zero, Limits.zero_comp]
  · obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff r hz
    have ht := (z.rebase_target y).symm
    rw [insert_tail_transport D Sc cutoff ht r _ _ (appendTail_rebase D Sc z y).symm]
    apply appendExtractOldQuotient_insert_ideal_tail
    exact (show ∀ {t t' : List I} (e : t = t') (a : hom D Sc cutoff v t),
      a ∈ ideal D Sc cutoff v t → (e ▸ a) ∈ ideal D Sc cutoff v t' from
        by intro t t' e; subst t'; exact fun _ ha => ha) ht r hr

/-- Every old-only generator has zero extracted old quotient coordinate, for arbitrary continuation. -/
theorem appendExtractOldQuotient_old_generator (p : ZMod 2)
    {i : I} {v s w : List I} (x : AppendIdx i v w)
    (r : hom D Sc cutoff v s) (hr : r ∈ ideal D Sc cutoff v s)
    (h : hom D Sc cutoff (s ++ [i]) w) :
    appendExtractOldQuotient D Sc cutoff p x (rightContext D Sc cutoff [i] v s r ≫ h) = 0 := by
  obtain ⟨f, rfl⟩ := (appendAffineEquiv D Sc cutoff i s w).symm.surjective h
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Limits.comp_zero]
  | add f g hf hg => simp only [map_add, Preadditive.comp_add, hf, hg, add_zero]
  | single z a =>
    rw [appendAffineEquiv_symm_single, ← append_insert_twisted_coefficient D Sc cutoff z a,
      ← Category.assoc, ← rightContext_comp]
    exact appendExtractOldQuotient_insert_ideal_cross_source D Sc cutoff p x z _
      (ideal_comp D Sc cutoff hr _)

/-- Extraction kills the entire old-only relation span, not just prescribed-source tails. -/
theorem appendExtractOldQuotient_relations (p : ZMod 2)
    {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendRelations D Sc cutoff i v w ≤ LinearMap.ker (appendExtractOldQuotient D Sc cutoff p x) := by
  apply Submodule.span_le.mpr
  rintro f ⟨s, r, hr, h, rfl⟩
  exact appendExtractOldQuotient_old_generator D Sc cutoff p x r hr h

/-- An actual old quotient coordinate on the old-only target. -/
def appendOldCoordinate (p : ZMod 2) {i : I} {v w : List I} (x : AppendIdx i v w) :
    AppendTarget D Sc cutoff i v w →ₗ[k] Old D Sc cutoff v x.oldTarget :=
  (appendRelations D Sc cutoff i v w).liftQ (appendExtractOldQuotient D Sc cutoff p x)
    (appendExtractOldQuotient_relations D Sc cutoff p x)

@[simp] theorem appendOldCoordinate_projection (p : ZMod 2)
    {i : I} {v w : List I} (x : AppendIdx i v w) (h : hom D Sc cutoff (v ++ [i]) w) :
    appendOldCoordinate D Sc cutoff p x (appendProjection D Sc cutoff i v w h) =
      appendExtractOldQuotient D Sc cutoff p x h := rfl

/-- Simultaneous old quotient coefficients, with finite support in the existing moving tails. -/
abbrev AppendOldCoordinates (i : I) (v w : List I) :=
  ⨁ (q : AppendIdx.Tail i v w), Old D Sc cutoff v q.representative.oldTarget

/-- Signed old quotient coefficient followed by an append continuation. -/
def appendPair (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (t ++ [i]) w) :
    Old D Sc cutoff v t →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (ideal D Sc cutoff v t).liftQ
    ((appendProjection D Sc cutoff i v w).comp
      ((Linear.rightComp k _ h).comp ((rightContext D Sc cutoff [i] v t).comp (twist k p))))
    (fun _ hr => appendProjection_old_ideal D Sc cutoff i (twist_ideal D Sc cutoff p hr) h)

@[simp] theorem appendPair_mk (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (t ++ [i]) w) (b : hom D Sc cutoff v t) :
    appendPair D Sc cutoff p i h ((ideal D Sc cutoff v t).mkQ b) =
      appendProjection D Sc cutoff i v w
        (rightContext D Sc cutoff [i] v t (twist k p b) ≫ h) := rfl

/-- Reconstruct the old-only target from all moving-tail old quotient coefficients. -/
def appendOldReconstruct (p : ZMod 2) (i : I) (v w : List I) :
    AppendOldCoordinates D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  DirectSum.toModule k _ _ fun q => appendPair D Sc cutoff p i
    ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
      appendTail D Sc q.representative)

/-- Reconstruction followed by extraction is the specified direct-sum component. -/
theorem appendOldCoordinate_reconstruct (p : ZMod 2) {i : I} {v w : List I}
    (q : AppendIdx.Tail i v w) (f : AppendOldCoordinates D Sc cutoff i v w) :
    appendOldCoordinate D Sc cutoff p q.representative
      (appendOldReconstruct D Sc cutoff p i v w f) = f q := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply]
  | add f g hf hg => simp only [map_add, hf, hg, DirectSum.add_apply]
  | of t a =>
    change appendOldCoordinate D Sc cutoff p q.representative
      (appendOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ t a)) = _
    rw [appendOldReconstruct, DirectSum.toModule_lof]
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t.representative.oldTarget).mkQ_surjective a
    rw [appendPair_mk, appendOldCoordinate_projection]
    by_cases ht : t = q
    · subst t
      rw [appendExtractOldQuotient_insert_tail, twist_twist, DirectSum.of_eq_same]
    · rw [appendExtractOldQuotient_insert_off_tail]
      · symm
        exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm ht)
      · intro h
        apply ht
        apply Subtype.ext
        exact t.representative_tailKey.symm.trans (h.symm.trans q.representative_tailKey)

/-- Simultaneous old quotient reconstruction is injective. -/
theorem appendOldReconstruct_injective (p : ZMod 2) (i : I) (v w : List I) :
    Function.Injective (appendOldReconstruct D Sc cutoff p i v w) := by
  intro f g h
  apply DFinsupp.ext
  intro q
  rw [← appendOldCoordinate_reconstruct D Sc cutoff p q f,
    ← appendOldCoordinate_reconstruct D Sc cutoff p q g, h]

private theorem appendOldReconstruct_range_tail (p : ZMod 2)
    {i : I} {v w : List I} (x : AppendIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    appendProjection D Sc cutoff i v w
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w)) ∈
      LinearMap.range (appendOldReconstruct D Sc cutoff p i v w) := by
  let q : AppendIdx.Tail i v w := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  refine ⟨DirectSum.lof k _ _ q
    ((ideal D Sc cutoff v q.representative.oldTarget).mkQ (twist k p (ht ▸ r))), ?_⟩
  rw [appendOldReconstruct, DirectSum.toModule_lof, appendPair_mk, twist_twist]
  exact congrArg (appendProjection D Sc cutoff i v w)
    (insert_tail_transport D Sc cutoff ht r _ _
      (appendTail_heq_of_tailKey_eq D Sc x q.representative hk)).symm

/-- Every old-only class has finite simultaneous old quotient coordinates. -/
theorem appendOldReconstruct_surjective (p : ZMod 2) (i : I) (v w : List I) :
    Function.Surjective (appendOldReconstruct D Sc cutoff p i v w) := by
  intro z
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v w z
  obtain ⟨f, rfl⟩ := (appendAffineEquiv D Sc cutoff i v w).symm.surjective h
  change appendProjection D Sc cutoff i v w ((appendAffineEquiv D Sc cutoff i v w).symm f) ∈
    LinearMap.range (appendOldReconstruct D Sc cutoff p i v w)
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg => simp only [map_add]; exact Submodule.add_mem _ hf hg
  | single x a =>
    rw [appendAffineEquiv_symm_single, ← append_insert_twisted_coefficient D Sc cutoff x a]
    exact appendOldReconstruct_range_tail D Sc cutoff p x _

/-- The full ELV old-only quotient is the direct sum of old quotient Hom coordinates.
No flatness, finite-colour assumption, or moving cyclotomic relation is imposed. -/
def appendOldCoordinateEquiv (p : ZMod 2) (i : I) (v w : List I) :
    AppendTarget D Sc cutoff i v w ≃ₗ[k] AppendOldCoordinates D Sc cutoff i v w :=
  (LinearEquiv.ofBijective (appendOldReconstruct D Sc cutoff p i v w)
    ⟨appendOldReconstruct_injective D Sc cutoff p i v w,
      appendOldReconstruct_surjective D Sc cutoff p i v w⟩).symm

@[simp] theorem appendOldCoordinateEquiv_apply (p : ZMod 2) {i : I} {v w : List I}
    (z : AppendTarget D Sc cutoff i v w) (q : AppendIdx.Tail i v w) :
    appendOldCoordinateEquiv D Sc cutoff p i v w z q =
      appendOldCoordinate D Sc cutoff p q.representative z := by
  rw [← appendOldCoordinate_reconstruct D Sc cutoff p q]
  exact congrArg (appendOldCoordinate D Sc cutoff p q.representative)
    ((appendOldCoordinateEquiv D Sc cutoff p i v w).symm_apply_apply z)

/-- Reconstruction is the left inverse of simultaneous extraction. -/
@[simp] theorem appendOldReconstruct_coordinateEquiv (p : ZMod 2) (i : I) (v w : List I)
    (z : AppendTarget D Sc cutoff i v w) :
    appendOldReconstruct D Sc cutoff p i v w
      (appendOldCoordinateEquiv D Sc cutoff p i v w z) = z :=
  (appendOldCoordinateEquiv D Sc cutoff p i v w).symm_apply_apply z

/-- Reconstruction is the right inverse of simultaneous extraction as well. -/
@[simp] theorem appendOldCoordinateEquiv_reconstruct (p : ZMod 2) (i : I) (v w : List I)
    (f : AppendOldCoordinates D Sc cutoff i v w) :
    appendOldCoordinateEquiv D Sc cutoff p i v w
      (appendOldReconstruct D Sc cutoff p i v w f) = f :=
  (appendOldCoordinateEquiv D Sc cutoff p i v w).apply_symm_apply f

end ELVOld
end OddMath.QuiverHecke
