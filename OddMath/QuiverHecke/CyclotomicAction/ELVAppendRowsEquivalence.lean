/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendRows

/-! # Common-row equivalence for the append endpoint

Wordwise old-quotient coefficients regroup by common old target, input shuffle
and moving exponent. Nonzero old coefficients supply old normal-form indices;
zero old Hom spaces require no nonemptiness hypothesis. Reconstruction and
extraction are inverse over the full opposite old content ring. The appended
strand uses parity-zero coefficient normalization for the untwisted K₀ action.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def appendRowsShuffleTransport {n m n' m' : ℕ} (h : n + 1 = m)
    (h' : n' + 1 = m') (e : n = n') (d : AppendShuffle h) : AppendShuffle h' := by
  subst n'; subst m; subst m'; exact d

private theorem appendRowsShuffleTransport_heq {n m n' m' : ℕ}
    (h : n + 1 = m) (h' : n' + 1 = m') (e : n = n') (d : AppendShuffle h) :
    HEq (appendRowsShuffleTransport h h' e d) d := by
  subst n'; subst m; subst m'; rfl

private theorem appendRowsShuffleTransport_word {n m n' m' : ℕ}
    (h : n + 1 = m) (h' : n' + 1 = m') (e : n = n') (d : AppendShuffle h) :
    Categorification.TypeA.canWord m' (appendRowsShuffleTransport h h' e d).1⁻¹ =
      Categorification.TypeA.canWord m d.1⁻¹ := by
  subst n'; subst m; subst m'; rfl

/-- Regroup a wordwise moving coordinate by its common old target. -/
def appendIndex {i : I} {ν w : List I} (v : ContentWords ν)
    (x : AppendIdx i v.val w) : AppendTailIndex i ν × ℕ :=
  (⟨⟨x.oldTarget, (tgt_perm _ _).trans v.property⟩,
    appendRowsShuffleTransport (appendLen v.val i) (appendLen x.oldTarget i)
      (by simp [AppendIdx.oldTarget]) x.1.2.2.2⟩, x.1.1)

theorem appendIndex_word {i : I} {ν w : List I} (v : ContentWords ν)
    (x : AppendIdx i v.val w) : (appendTailWord i (appendIndex v x).1).val = w := by
  dsimp only [appendTailWord, appendIndex]
  rw [appendRowsShuffleTransport_word]
  exact x.moving_target

private theorem append_rows_cl_heq {a b w z : List I} {L M : List PG}
    (hab : a = b) (hwz : w = z) (hLM : L = M) (ha : SChain a (pl a L) w)
    (hb : SChain b (pl b M) z) : HEq (cl D Sc a w L ha) (cl D Sc b z M hb) := by
  subst b
  subst z
  subst M
  rfl

theorem appendIndex_tail {i : I} {ν w : List I} (v : ContentWords ν)
    (x : AppendIdx i v.val w) :
    HEq (appendCommonTail D Sc cutoff i (appendIndex v x).1 (appendIndex v x).2)
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        appendTail D Sc x : hom D Sc cutoff (x.oldTarget ++ [i]) w) := by
  have ht : HEq (appendTail D Sc (appendTailPBW i (appendIndex v x).1 (appendIndex v x).2))
      (appendTail D Sc x) := by
    apply append_rows_cl_heq
    · exact congrArg (fun t => t ++ [i]) (appendTailPBW_oldTarget i _ _)
    · exact appendIndex_word v x
    · dsimp only [appendTailPBW, appendIndex]
      rw [appendRowsShuffleTransport_word]
      simp only [AppendIdx.oldTarget, length_tgt]
  unfold appendCommonTail
  exact (show ∀ {t z : List I} (e : t = x.oldTarget) (hz : z = w)
    (f : (pres D Sc).obj (ob D (t ++ [i])) ⟶ (pres D Sc).obj (ob D z)),
    HEq f (appendTail D Sc x) →
    HEq (e ▸ ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f :
      hom D Sc cutoff (t ++ [i]) z))
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x :
        hom D Sc cutoff (x.oldTarget ++ [i]) w) from by
      intro t z e hz f hf
      subst t
      subst z
      cases hf
      rfl) (appendTailPBW_oldTarget i _ _) (appendIndex_word v x) _ ht

theorem appendIndex_eq_of_tailKey_eq {i : I} {ν w : List I} (v : ContentWords ν)
    (x z : AppendIdx i v.val w) (h : x.tailKey = z.tailKey) :
    appendIndex v x = appendIndex v z := by
  have ht := x.oldTarget_eq_of_tailKey_eq z h
  have hm := congrArg Prod.fst h
  have hd := congrArg Prod.snd h
  apply Prod.ext
  · apply Sigma.ext
    · exact Subtype.ext ht
    · dsimp only [appendIndex]
      exact (appendRowsShuffleTransport_heq _ _ _ _).trans
        ((heq_of_eq hd).trans (appendRowsShuffleTransport_heq _ _ _ _).symm)
  · exact hm

/-- Attach a common tail to any old normal form ending at its old target. -/
def appendCommonPBW {i : I} {ν : List I} (v : ContentWords ν)
    (q : AppendTailIndex i ν) (m : ℕ) (y : NFIdx v.val q.1.val) :
    AppendIdx i v.val (appendTailWord i q).val := by
  have hl : q.1.val.length = v.val.length :=
    q.1.property.length_eq.trans v.property.length_eq.symm
  refine ⟨(m, y.1.1, y.1.2,
    appendRowsShuffleTransport (appendLen q.1.val i) (appendLen v.val i) hl q.2),
      y.2.1, y.2.2.1, ?_⟩
  have he := tgt_append_right [i] (t := v.val)
    (fits_cw (Categorification.TypeA.validWord_canWord v.val.length y.1.2))
  simp only [appendCrossingWord, cw_append, tgt_append, he, y.tgt_cw]
  rw [appendRowsShuffleTransport_word]
  rfl

theorem appendIndex_commonPBW {i : I} {ν : List I} (v : ContentWords ν)
    (q : AppendTailIndex i ν) (m : ℕ) (y : NFIdx v.val q.1.val) :
    appendIndex v (appendCommonPBW v q m y) = (q, m) := by
  apply Prod.ext
  · apply Sigma.ext
    · exact Subtype.ext y.tgt_cw
    · dsimp only [appendIndex, appendCommonPBW]
      exact (appendRowsShuffleTransport_heq _ _ _ _).trans
        (appendRowsShuffleTransport_heq _ _ _ _)
  · rfl

open Classical in
private theorem append_pair_transport {i : I} {v t t' w w' : List I}
    (ht : t = t') (hw : w = w')
    (h : hom D Sc cutoff (t ++ [i]) w) (h' : hom D Sc cutoff (t' ++ [i]) w')
    (hh : HEq h h') (b : Old D Sc cutoff v t) :
    HEq (appendPair D Sc cutoff 0 i h b) (appendPair D Sc cutoff 0 i h' (ht ▸ b)) := by
  subst t'
  subst w'
  cases hh
  rfl

open Classical in
theorem appendTailRow_appendIndex {i : I} {ν : List I}
    (v : ContentWords ν) (w : ContentWords (i :: ν))
    (x : AppendIdx i v.val w.val) (b : Old D Sc cutoff v.val x.oldTarget) :
    appendTailRow D Sc cutoff i ν (appendIndex v x).1 (appendIndex v x).2
      (Pi.single v b) =
      Pi.single w (Pi.single v (appendPair D Sc cutoff 0 i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc x) b)) := by
  have hw : appendTailWord i (appendIndex v x).1 = w := Subtype.ext (appendIndex_word v x)
  have hp := append_pair_transport D Sc cutoff (v := v.val) rfl
    (appendIndex_word v x) _ _ (appendIndex_tail D Sc cutoff v x) b
  have hs : appendPairRow D Sc cutoff i ν
      (appendCommonTail D Sc cutoff i (appendIndex v x).1 (appendIndex v x).2)
      (Pi.single v b) = (Pi.single v
        (appendPair D Sc cutoff 0 i (appendCommonTail D Sc cutoff i (appendIndex v x).1
          (appendIndex v x).2) b) : AppendRow D Sc cutoff i ν
            (appendTailWord i (appendIndex v x).1).val) := by
    funext v'
    by_cases hv : v' = v
    · subst v'
      simp only [appendPairRow_apply, Pi.single_eq_same]
    · simp [appendPairRow_apply, Pi.single_eq_of_ne hv]
  change Pi.single _ _ = _
  rw [hs]
  exact (show ∀ (a b : ContentWords (i :: ν)) (hab : a = b)
    (f : AppendTarget D Sc cutoff i v.val a.val) (g : AppendTarget D Sc cutoff i v.val b.val),
    HEq f g → (Pi.single a (Pi.single v f) : AppendContent D Sc cutoff i ν) =
      Pi.single b (Pi.single v g) from by
        intro a b hab f g hfg
        subst b
        cases hfg
        rfl) _ _ hw _ _ hp

open Classical in
private theorem appendOldReconstruct_lof (i : I) (v w : List I)
    (t : AppendIdx.Tail i v w) (b : Old D Sc cutoff v t.representative.oldTarget) :
    appendOldReconstruct D Sc cutoff 0 i v w (DirectSum.lof k _ _ t b) =
      appendPair D Sc cutoff 0 i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc t.representative) b :=
  DirectSum.toModule_lof _ _ _

open Classical in
theorem appendRowsReconstruct_surjective (i : I) (ν : List I) :
    Function.Surjective (appendRowsReconstruct D Sc cutoff i ν) := by
  let F := appendRowsReconstruct D Sc cutoff i ν
  have hcol (w : ContentWords (i :: ν)) (v : ContentWords ν)
      (z : AppendTarget D Sc cutoff i v.val w.val) :
      Pi.single w (Pi.single v z) ∈ LinearMap.range F := by
    obtain ⟨f, rfl⟩ := (appendOldCoordinateEquiv D Sc cutoff 0 i v.val w.val).symm.surjective z
    change (Pi.single w (Pi.single v (appendOldReconstruct D Sc cutoff 0 i v.val w.val f)) :
      AppendContent D Sc cutoff i ν) ∈ _
    induction f using DirectSum.induction_on with
    | zero => simp
    | add f g hf hg =>
      simpa only [map_add, Pi.single_add] using (LinearMap.range F).add_mem hf hg
    | of q b =>
      refine ⟨DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ (appendIndex v q.representative)
        (Pi.single v b), ?_⟩
      change appendRowsReconstruct D Sc cutoff i ν _ = _
      rw [appendRowsReconstruct_lof, appendTailRow_appendIndex]
      congr 2
      exact (appendOldReconstruct_lof D Sc cutoff i v.val w.val q b).symm
  intro z
  have hz : z = ∑ w : ContentWords (i :: ν), ∑ v : ContentWords ν,
      Pi.single w (Pi.single v (z w v)) := by
    funext w v
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single w]
    · simp only [Pi.single_eq_same]
      rw [Finset.sum_eq_single v]
      · simp
      · intro v' _ hv'
        simp [Pi.single_eq_of_ne (Ne.symm hv')]
      · simp
    · intro w' _ hw'
      simp [Pi.single_eq_of_ne (Ne.symm hw')]
    · simp
  rw [hz]
  exact (LinearMap.range F).sum_mem fun w _ =>
    (LinearMap.range F).sum_mem fun v _ => hcol w v (z w v)

open Classical in
def appendColumnLift {i : I} {ν : List I} (w : ContentWords (i :: ν))
    (v : ContentWords ν) : AppendOldCoordinates D Sc cutoff i v.val w.val →ₗ[k]
      AppendRows D Sc cutoff i ν :=
  DirectSum.toModule k _ _ fun q =>
    (DirectSum.lof k _ _ (appendIndex v q.representative)).comp
      (LinearMap.single (R := k) (φ := fun a : ContentWords ν =>
        Old D Sc cutoff a.val q.representative.oldTarget) v)

open Classical in
def appendDecode (i : I) (ν : List I) :
    AppendContent D Sc cutoff i ν →ₗ[k] AppendRows D Sc cutoff i ν :=
  ∑ w : ContentWords (i :: ν), ∑ v : ContentWords ν,
    (appendColumnLift D Sc cutoff w v).comp
      ((appendOldCoordinateEquiv D Sc cutoff 0 i v.val w.val).toLinearMap.comp
        ((LinearMap.proj (R := k) (φ := fun v : ContentWords ν =>
          AppendTarget D Sc cutoff i v.val w.val) v).comp
          (LinearMap.proj (R := k) (φ := fun w : ContentWords (i :: ν) =>
            AppendRow D Sc cutoff i ν w.val) w)))

open Classical in
theorem appendDecode_single {i : I} {ν : List I}
    (w : ContentWords (i :: ν)) (v : ContentWords ν)
    (z : AppendTarget D Sc cutoff i v.val w.val) :
    appendDecode D Sc cutoff i ν (Pi.single w (Pi.single v z)) =
      appendColumnLift D Sc cutoff w v
        (appendOldCoordinateEquiv D Sc cutoff 0 i v.val w.val z) := by
  simp only [appendDecode, LinearMap.sum_apply, LinearMap.comp_apply]
  change (∑ w' : ContentWords (i :: ν), ∑ v' : ContentWords ν,
    appendColumnLift D Sc cutoff w' v'
      (appendOldCoordinateEquiv D Sc cutoff 0 i v'.val w'.val
        ((Pi.single w (Pi.single v z) : AppendContent D Sc cutoff i ν) w' v'))) = _
  rw [Finset.sum_eq_single w]
  · simp only [Pi.single_eq_same]
    rw [Finset.sum_eq_single v]
    · simp
    · intro v' _ hv'
      simp [Pi.single_eq_of_ne hv']
    · simp
  · intro w' _ hw'
    simp [Pi.single_eq_of_ne hw']
  · simp

open Classical in
theorem appendDecode_reconstruct_canonical {i : I} {ν : List I}
    (w : ContentWords (i :: ν)) (v : ContentWords ν)
    (t : AppendIdx.Tail i v.val w.val)
    (b : Old D Sc cutoff v.val t.representative.oldTarget) :
    appendDecode D Sc cutoff i ν
      (appendRowsReconstruct D Sc cutoff i ν
        (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _
          (appendIndex v t.representative) (Pi.single v b))) =
      DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _
          (appendIndex v t.representative) (Pi.single v b) := by
  rw [appendRowsReconstruct_lof, appendTailRow_appendIndex, appendDecode_single]
  have hr := appendOldReconstruct_lof D Sc cutoff i v.val w.val t b
  rw [← hr, appendOldCoordinateEquiv_reconstruct]
  exact DirectSum.toModule_lof _ _ _

open Classical in
theorem exists_appendIndex_of_ne_zero {i : I} {ν : List I}
    (v : ContentWords ν) (q : AppendTailIndex i ν × ℕ)
    (b : Old D Sc cutoff v.val q.1.1.val) (hb : b ≠ 0) :
    ∃ (w : ContentWords (i :: ν)) (t : AppendIdx.Tail i v.val w.val),
      appendIndex v t.representative = q := by
  obtain ⟨r, hr⟩ := (ideal D Sc cutoff v.val q.1.1.val).mkQ_surjective b
  have hn : r ≠ 0 := by intro h; subst r; simp at hr; exact hb hr.symm
  obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff r hn
  let x := appendCommonPBW v q.1 q.2 y
  let t : AppendIdx.Tail i v.val (appendTailWord i q.1).val := ⟨x.tailKey, x, rfl⟩
  refine ⟨appendTailWord i q.1, t, ?_⟩
  exact (appendIndex_eq_of_tailKey_eq v t.representative x t.representative_tailKey).trans
    (appendIndex_commonPBW v q.1 q.2 y)

open Classical in
theorem appendDecode_reconstruct (i : I) (ν : List I)
    (f : AppendRows D Sc cutoff i ν) :
    appendDecode D Sc cutoff i ν (appendRowsReconstruct D Sc cutoff i ν f) = f := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | of q b =>
    have hs (v : ContentWords ν) (c : Old D Sc cutoff v.val q.1.1.val) :
        appendDecode D Sc cutoff i ν
          (appendRowsReconstruct D Sc cutoff i ν
            (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q (Pi.single v c))) =
          DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q (Pi.single v c) := by
      by_cases hc : c = 0
      · subst c
        simp
      · obtain ⟨w, t, ht⟩ := exists_appendIndex_of_ne_zero D Sc cutoff (i := i) v q c hc
        have h : ∀ c : Old D Sc cutoff v.val (appendIndex v t.representative).1.1.val,
            appendDecode D Sc cutoff i ν
              (appendRowsReconstruct D Sc cutoff i ν
                (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _
                  (appendIndex v t.representative) (Pi.single v c))) =
              DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _
                  (appendIndex v t.representative) (Pi.single v c) :=
          appendDecode_reconstruct_canonical D Sc cutoff w v t
        rw [ht] at h
        exact h c
    have hb : b = ∑ v : ContentWords ν, Pi.single v (b v) := by
      funext v
      simp only [Finset.sum_apply]
      rw [Finset.sum_eq_single v]
      · simp
      · intro v' _ hv'
        simp [Pi.single_eq_of_ne (Ne.symm hv')]
      · simp
    change appendDecode D Sc cutoff i ν
      (appendRowsReconstruct D Sc cutoff i ν
        (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b)) = _
    rw [hb]
    simp only [map_sum, hs]
    rfl

open Classical in
theorem appendRowsReconstruct_decode (i : I) (ν : List I)
    (z : AppendContent D Sc cutoff i ν) :
    appendRowsReconstruct D Sc cutoff i ν (appendDecode D Sc cutoff i ν z) = z := by
  obtain ⟨f, rfl⟩ := appendRowsReconstruct_surjective D Sc cutoff i ν z
  rw [appendDecode_reconstruct]

open Classical in
theorem appendRowsReconstruct_injective (i : I) (ν : List I) :
    Function.Injective (appendRowsReconstruct D Sc cutoff i ν) :=
  Function.LeftInverse.injective (appendDecode_reconstruct D Sc cutoff i ν)

open Classical in
/-- The concrete common-tail reconstruction is linear over the full opposite old ring. -/
def appendRowsEquiv (i : I) (ν : List I) :
    AppendRows D Sc cutoff i ν ≃ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendContent D Sc cutoff i ν :=
  LinearEquiv.ofBijective (appendRowsReconstruct D Sc cutoff i ν)
    ⟨appendRowsReconstruct_injective D Sc cutoff i ν,
      appendRowsReconstruct_surjective D Sc cutoff i ν⟩

open Classical in
@[simp] theorem appendRowsEquiv_apply (i : I) (ν : List I)
    (f : AppendRows D Sc cutoff i ν) :
    appendRowsEquiv D Sc cutoff i ν f = appendRowsReconstruct D Sc cutoff i ν f := rfl

/-- The inverse over the full old ring is the wordwise coefficient decoder. -/
@[simp] theorem appendRowsEquiv_symm_apply (i : I) (ν : List I)
    (z : AppendContent D Sc cutoff i ν) :
    (appendRowsEquiv D Sc cutoff i ν).symm z = appendDecode D Sc cutoff i ν z := by
  apply appendRowsReconstruct_injective D Sc cutoff i ν
  change appendRowsEquiv D Sc cutoff i ν ((appendRowsEquiv D Sc cutoff i ν).symm z) = _
  rw [LinearEquiv.apply_symm_apply, appendRowsReconstruct_decode]

/-- Coefficient extraction respects every element of the full old matrix ring. -/
theorem appendDecode_smul (i : I) (ν : List I)
    (a : (ContentRing D Sc cutoff ν)ᵐᵒᵖ) (z : AppendContent D Sc cutoff i ν) :
    appendDecode D Sc cutoff i ν (a • z) = a • appendDecode D Sc cutoff i ν z := by
  rw [← appendRowsEquiv_symm_apply, ← appendRowsEquiv_symm_apply]
  exact (appendRowsEquiv D Sc cutoff i ν).symm.map_smul a z

end OddMath.QuiverHecke.ELVOld
