/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVSourceRows

/-!
# Common-source row coordinates

This supplies the inverse laws for the concrete reconstruction in `ELVSourceRows`,
a supporting step for the prepend endpoint of the deformed square resolution.
Existing wordwise old-quotient coordinates are regrouped by their common old target,
shuffle and exponent. A nonzero old coefficient supplies an old normal-form index;
zero Hom spaces therefore require no nonemptiness hypothesis. The equivalence is
linear over the full opposite old content ring, with arbitrary total parity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped TensorProduct DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

open Classical in
private theorem shuffle_transport_word {n m : ℕ} (h : n = m) (d : PrependShuffle n) :
    Categorification.TypeA.canWord (m + 1) (↑(h ▸ d : PrependShuffle m))⁻¹ =
      Categorification.TypeA.canWord (n + 1) d.1⁻¹ := by
  subst m
  rfl

open Classical in
def sourceIndex {i : I} {ν w : List I} (v : ContentWords ν)
    (x : PrependIdx i v.val w) : SourceTailIndex ν × ℕ :=
  (⟨⟨x.oldTarget, (tgt_perm _ _).trans v.property⟩,
    (show v.val.length = x.oldTarget.length by simp [PrependIdx.oldTarget]) ▸ x.1.2.2.2⟩,
    x.1.1)

open Classical in
theorem sourceIndex_word {i : I} {ν w : List I} (v : ContentWords ν)
    (x : PrependIdx i v.val w) : (sourceTailWord i (sourceIndex v x).1).val = w := by
  dsimp only [sourceTailWord, sourceIndex]
  rw [shuffle_transport_word]
  exact x.moving_target

open Classical in
private theorem cl_heq {a b w z : List I} {L M : List PG}
    (hab : a = b) (hwz : w = z) (hLM : L = M) (ha : SChain a (pl a L) w)
    (hb : SChain b (pl b M) z) : HEq (cl D Sc a w L ha) (cl D Sc b z M hb) := by
  subst b
  subst z
  subst M
  rfl

open Classical in
theorem sourceIndex_tail {i : I} {ν w : List I} (v : ContentWords ν)
    (x : PrependIdx i v.val w) :
    HEq (sourceTail D Sc cutoff i (sourceIndex v x).1 (sourceIndex v x).2)
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w) := by
  have ht : HEq (prependTail D Sc (sourceTailPBW i (sourceIndex v x).1 (sourceIndex v x).2))
      (prependTail D Sc x) := by
    apply cl_heq
    · exact congrArg (List.cons i) (sourceTailPBW_oldTarget i _ _)
    · exact sourceIndex_word v x
    · dsimp only [sourceTailPBW, sourceIndex]
      rw [shuffle_transport_word]
  unfold sourceTail
  exact (show ∀ {t z : List I} (e : t = x.oldTarget) (hz : z = w)
    (f : (pres D Sc).obj (ob D (i :: t)) ⟶ (pres D Sc).obj (ob D z)),
    HEq f (prependTail D Sc x) →
    HEq (e ▸ ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f :
      hom D Sc cutoff (i :: t) z))
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x :
        hom D Sc cutoff (i :: x.oldTarget) w) from by
      intro t z e hz f hf
      subst t
      subst z
      cases hf
      rfl) (sourceTailPBW_oldTarget i _ _) (sourceIndex_word v x) _ ht

open Classical in
theorem sourceIndex_eq_of_tailKey_eq {i : I} {ν w : List I} (v : ContentWords ν)
    (x z : PrependIdx i v.val w) (h : x.tailKey = z.tailKey) :
    sourceIndex v x = sourceIndex v z := by
  have ht := x.oldTarget_eq_of_tailKey_eq z h
  have hm := congrArg Prod.fst h
  have hd := congrArg Prod.snd h
  apply Prod.ext
  · apply Sigma.ext
    · exact Subtype.ext ht
    · dsimp only [sourceIndex]
      exact (show ∀ {n a b : ℕ} (ha : n = a) (hb : n = b)
        (d e : PrependShuffle n), d = e → HEq (ha ▸ d) (hb ▸ e) from by
          intro n a b ha hb d e hde
          subst a
          subst b
          subst e
          rfl) _ _ _ _ hd
  · exact hm

open Classical in
theorem sourceIndex_rebase {i : I} {ν : List I} (v : ContentWords ν)
    (q : SourceTailIndex ν) (m : ℕ)
    (y : NFIdx v.val (sourceTailPBW i q m).oldTarget) :
    sourceIndex v ((sourceTailPBW i q m).rebase y) = (q, m) := by
  apply Prod.ext
  · apply Sigma.ext
    · exact Subtype.ext ((PrependIdx.rebase_target _ _).trans
        (sourceTailPBW_oldTarget i q m))
    · dsimp only [sourceIndex, PrependIdx.rebase, sourceTailPBW]
      exact (show ∀ {n a b : ℕ} (ha : a = n) (hb : a = b)
        (d : PrependShuffle n), HEq (hb ▸ (ha.symm ▸ d)) d from by
          intro n a b ha hb d
          subst n
          subst b
          rfl) (v.property.length_eq.trans q.1.property.length_eq.symm) _ _
  · rfl

open Classical in
private theorem pair_transport {p : ZMod 2} {i : I} {v t t' w w' : List I}
    (ht : t = t') (hw : w = w')
    (h : hom D Sc cutoff (i :: t) w) (h' : hom D Sc cutoff (i :: t') w')
    (hh : HEq h h') (b : Old D Sc cutoff v t) :
    HEq (pair D Sc cutoff p i h b) (pair D Sc cutoff p i h' (ht ▸ b)) := by
  subst t'
  subst w'
  cases hh
  rfl

open Classical in
theorem sourceTailRow_sourceIndex (p : ZMod 2) {i : I} {ν : List I}
    (v : ContentWords ν) (w : ContentWords (i :: ν))
    (x : PrependIdx i v.val w.val) (b : Old D Sc cutoff v.val x.oldTarget) :
    sourceTailRow D Sc cutoff p i ν (sourceIndex v x).1 (sourceIndex v x).2
      (Pi.single v b) =
      Pi.single w (Pi.single v (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc x) b)) := by
  have hw : sourceTailWord i (sourceIndex v x).1 = w := Subtype.ext (sourceIndex_word v x)
  have hp := pair_transport D Sc cutoff (p := p) (v := v.val) rfl
    (sourceIndex_word v x) _ _ (sourceIndex_tail D Sc cutoff v x) b
  have hs : sourcePairRow D Sc cutoff p i ν
      (sourceTail D Sc cutoff i (sourceIndex v x).1 (sourceIndex v x).2)
      (Pi.single v b) = (Pi.single v
        (pair D Sc cutoff p i (sourceTail D Sc cutoff i (sourceIndex v x).1
          (sourceIndex v x).2) b) : SourceRow D Sc cutoff p i ν
            (sourceTailWord i (sourceIndex v x).1).val) := by
    funext v'
    by_cases hv : v' = v
    · subst v'
      simp only [sourcePairRow_apply, Pi.single_eq_same]
    · simp [sourcePairRow_apply, Pi.single_eq_of_ne hv]
  change Pi.single _ _ = _
  rw [hs]
  exact (show ∀ (a b : ContentWords (i :: ν)) (hab : a = b)
    (f : Target D Sc cutoff i v.val a.val) (g : Target D Sc cutoff i v.val b.val),
    HEq f g → (Pi.single a (Pi.single v f) : SourceContent D Sc cutoff p i ν) =
      Pi.single b (Pi.single v g) from by
        intro a b hab f g hfg
        subst b
        cases hfg
        rfl) _ _ hw _ _ hp

open Classical in
private theorem prependOldReconstruct_lof (p : ZMod 2) (i : I) (v w : List I)
    (t : PrependIdx.Tail i v w) (b : Old D Sc cutoff v t.representative.oldTarget) :
    prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ t b) =
      pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc t.representative) b :=
  DirectSum.toModule_lof _ _ _

open Classical in
theorem sourceRowsReconstruct_surjective (p : ZMod 2) (i : I) (ν : List I) :
    Function.Surjective (sourceRowsReconstruct D Sc cutoff p i ν) := by
  let F := sourceRowsReconstruct D Sc cutoff p i ν
  have hcol (w : ContentWords (i :: ν)) (v : ContentWords ν)
      (z : Target D Sc cutoff i v.val w.val) :
      Pi.single w (Pi.single v z) ∈ LinearMap.range F := by
    obtain ⟨f, rfl⟩ := (prependOldCoordinateEquiv D Sc cutoff p i v.val w.val).symm.surjective z
    change (Pi.single w (Pi.single v (prependOldReconstruct D Sc cutoff p i v.val w.val f)) :
      SourceContent D Sc cutoff p i ν) ∈ _
    induction f using DirectSum.induction_on with
    | zero => simp
    | add f g hf hg =>
      simpa only [map_add, Pi.single_add] using (LinearMap.range F).add_mem hf hg
    | of q b =>
      refine ⟨DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ (sourceIndex v q.representative)
        (Pi.single v b), ?_⟩
      change sourceRowsReconstruct D Sc cutoff p i ν _ = _
      rw [sourceRowsReconstruct_lof, sourceTailRow_sourceIndex]
      congr 2
      exact (prependOldReconstruct_lof D Sc cutoff p i v.val w.val q b).symm
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
def sourceColumnLift {i : I} {ν : List I} (w : ContentWords (i :: ν))
    (v : ContentWords ν) : PrependOldCoordinates D Sc cutoff i v.val w.val →ₗ[k]
      SourceRows D Sc cutoff ν :=
  DirectSum.toModule k _ _ fun q =>
    (DirectSum.lof k _ _ (sourceIndex v q.representative)).comp
      (LinearMap.single (R := k) (φ := fun a : ContentWords ν =>
        Old D Sc cutoff a.val q.representative.oldTarget) v)

open Classical in
def sourceDecode (p : ZMod 2) (i : I) (ν : List I) :
    SourceContent D Sc cutoff p i ν →ₗ[k] SourceRows D Sc cutoff ν :=
  ∑ w : ContentWords (i :: ν), ∑ v : ContentWords ν,
    (sourceColumnLift D Sc cutoff w v).comp
      ((prependOldCoordinateEquiv D Sc cutoff p i v.val w.val).toLinearMap.comp
        ((LinearMap.proj (R := k) (φ := fun v : ContentWords ν =>
          Target D Sc cutoff i v.val w.val) v).comp
          (LinearMap.proj (R := k) (φ := fun w : ContentWords (i :: ν) =>
            SourceRow D Sc cutoff p i ν w.val) w)))

open Classical in
theorem sourceDecode_single (p : ZMod 2) {i : I} {ν : List I}
    (w : ContentWords (i :: ν)) (v : ContentWords ν)
    (z : Target D Sc cutoff i v.val w.val) :
    sourceDecode D Sc cutoff p i ν (Pi.single w (Pi.single v z)) =
      sourceColumnLift D Sc cutoff w v
        (prependOldCoordinateEquiv D Sc cutoff p i v.val w.val z) := by
  simp only [sourceDecode, LinearMap.sum_apply, LinearMap.comp_apply]
  change (∑ w' : ContentWords (i :: ν), ∑ v' : ContentWords ν,
    sourceColumnLift D Sc cutoff w' v'
      (prependOldCoordinateEquiv D Sc cutoff p i v'.val w'.val
        ((Pi.single w (Pi.single v z) : SourceContent D Sc cutoff p i ν) w' v'))) = _
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
theorem sourceDecode_reconstruct_canonical (p : ZMod 2) {i : I} {ν : List I}
    (w : ContentWords (i :: ν)) (v : ContentWords ν)
    (t : PrependIdx.Tail i v.val w.val)
    (b : Old D Sc cutoff v.val t.representative.oldTarget) :
    sourceDecode D Sc cutoff p i ν
      (sourceRowsReconstruct D Sc cutoff p i ν
        (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _
          (sourceIndex v t.representative) (Pi.single v b))) =
      DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _
          (sourceIndex v t.representative) (Pi.single v b) := by
  rw [sourceRowsReconstruct_lof, sourceTailRow_sourceIndex, sourceDecode_single]
  have hr := prependOldReconstruct_lof D Sc cutoff p i v.val w.val t b
  rw [← hr, prependOldCoordinateEquiv_reconstruct]
  exact DirectSum.toModule_lof _ _ _

open Classical in
theorem exists_sourceIndex_of_ne_zero {i : I} {ν : List I}
    (v : ContentWords ν) (q : SourceTailIndex ν × ℕ)
    (b : Old D Sc cutoff v.val q.1.1.val) (hb : b ≠ 0) :
    ∃ (w : ContentWords (i :: ν)) (t : PrependIdx.Tail i v.val w.val),
      sourceIndex v t.representative = q := by
  obtain ⟨r, hr⟩ := (ideal D Sc cutoff v.val q.1.1.val).mkQ_surjective b
  have hn : r ≠ 0 := by intro h; subst r; simp at hr; exact hb hr.symm
  obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff r hn
  let z := sourceTailPBW i q.1 q.2
  let x := z.rebase ((sourceTailPBW_oldTarget i q.1 q.2).symm ▸ y)
  let t : PrependIdx.Tail i v.val (sourceTailWord i q.1).val := ⟨x.tailKey, x, rfl⟩
  refine ⟨sourceTailWord i q.1, t, ?_⟩
  exact (sourceIndex_eq_of_tailKey_eq v t.representative x t.representative_tailKey).trans
    (sourceIndex_rebase v q.1 q.2 _)

open Classical in
theorem sourceDecode_reconstruct (p : ZMod 2) (i : I) (ν : List I)
    (f : SourceRows D Sc cutoff ν) :
    sourceDecode D Sc cutoff p i ν (sourceRowsReconstruct D Sc cutoff p i ν f) = f := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | of q b =>
    have hs (v : ContentWords ν) (c : Old D Sc cutoff v.val q.1.1.val) :
        sourceDecode D Sc cutoff p i ν
          (sourceRowsReconstruct D Sc cutoff p i ν
            (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q (Pi.single v c))) =
          DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q (Pi.single v c) := by
      by_cases hc : c = 0
      · subst c
        simp
      · obtain ⟨w, t, ht⟩ := exists_sourceIndex_of_ne_zero D Sc cutoff (i := i) v q c hc
        have h : ∀ c : Old D Sc cutoff v.val (sourceIndex v t.representative).1.1.val,
            sourceDecode D Sc cutoff p i ν
              (sourceRowsReconstruct D Sc cutoff p i ν
                (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _
                  (sourceIndex v t.representative) (Pi.single v c))) =
              DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _
                  (sourceIndex v t.representative) (Pi.single v c) :=
          sourceDecode_reconstruct_canonical D Sc cutoff p w v t
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
    change sourceDecode D Sc cutoff p i ν
      (sourceRowsReconstruct D Sc cutoff p i ν
        (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b)) = _
    rw [hb]
    simp only [map_sum, hs]
    rfl

open Classical in
theorem sourceRowsReconstruct_decode (p : ZMod 2) (i : I) (ν : List I)
    (z : SourceContent D Sc cutoff p i ν) :
    sourceRowsReconstruct D Sc cutoff p i ν (sourceDecode D Sc cutoff p i ν z) = z := by
  obtain ⟨f, rfl⟩ := sourceRowsReconstruct_surjective D Sc cutoff p i ν z
  rw [sourceDecode_reconstruct]

open Classical in
theorem sourceRowsReconstruct_injective (p : ZMod 2) (i : I) (ν : List I) :
    Function.Injective (sourceRowsReconstruct D Sc cutoff p i ν) :=
  Function.LeftInverse.injective (sourceDecode_reconstruct D Sc cutoff p i ν)

open Classical in
/-- The concrete common-tail reconstruction is linear over the full opposite old ring. -/
def sourceRowsEquiv (p : ZMod 2) (i : I) (ν : List I) :
    SourceRows D Sc cutoff ν ≃ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourceContent D Sc cutoff p i ν :=
  LinearEquiv.ofBijective (sourceRowsReconstruct D Sc cutoff p i ν)
    ⟨sourceRowsReconstruct_injective D Sc cutoff p i ν,
      sourceRowsReconstruct_surjective D Sc cutoff p i ν⟩

open Classical in
@[simp] theorem sourceRowsEquiv_apply (p : ZMod 2) (i : I) (ν : List I)
    (f : SourceRows D Sc cutoff ν) :
    sourceRowsEquiv D Sc cutoff p i ν f = sourceRowsReconstruct D Sc cutoff p i ν f := rfl
end OddMath.QuiverHecke.ELVOld
