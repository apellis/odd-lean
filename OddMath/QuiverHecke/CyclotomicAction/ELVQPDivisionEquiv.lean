/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVQPBoundaryDivision
/-! # Canonical quotient and remainder for the actual endpoint–QP numerator

The concrete highest old-Hom action separates the numerator image from the
low-degree remainder submodule. This yields `endpointQPDivisionEquiv`, a
canonical linear quotient/remainder decomposition on the old-only append target.
It is not an identification with the prescribed categorical reverse matrix.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def endpointQPAction (i : I) (v w : List I) :
    hom D Sc cutoff (v ++ [i]) w →ₗ[k] AppendTarget D Sc cutoff i v w where
  toFun g := appendProjection D Sc cutoff i v w
    (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
      endpointELV D Sc cutoff i v ≫ g)
  map_add' _ _ := by simp only [Preadditive.comp_add, map_add]
  map_smul' _ _ := by simp only [Linear.comp_smul, map_smul, RingHom.id_apply]

theorem endpointQPAction_zero_of_projection_zero (i : I) (v w : List I)
    (g : hom D Sc cutoff (v ++ [i]) w)
    (hg : appendProjection D Sc cutoff i v w g = 0) :
    endpointQPAction D Sc cutoff i v w g = 0 := by
  apply (appendOldCoordinateEquiv D Sc cutoff 0 i v w).injective
  ext t
  rw [map_zero, DFinsupp.zero_apply, appendOldCoordinateEquiv_apply]
  exact endpointQP_above D Sc cutoff i v w g t.representative (by
    simp only [hg, map_zero, DFinsupp.support_zero, Finset.notMem_empty,
      false_implies, implies_true])

theorem endpointQPAction_low (i : I) (v w : List I)
    (g : hom D Sc cutoff (v ++ [i]) w)
    (hlow : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (endpointQPAction D Sc cutoff i v w g)).support,
      t.1.1 < endpointQPDegree D cutoff i v) :
    appendProjection D Sc cutoff i v w g = 0 ∧
      endpointQPAction D Sc cutoff i v w g = 0 := by
  have hg : appendProjection D Sc cutoff i v w g = 0 := by
    apply (appendOldCoordinateEquiv D Sc cutoff 0 i v w).injective
    rw [map_zero]
    by_contra hn
    let E := appendOldCoordinateEquiv D Sc cutoff 0 i v w
    have hne : (E (appendProjection D Sc cutoff i v w g)).support.Nonempty := by
      by_contra he
      have hz := Finset.not_nonempty_iff_eq_empty.mp he
      apply hn
      ext t
      exact DFinsupp.notMem_support_iff.mp (by rw [hz]; exact Finset.notMem_empty t)
    obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image _ (fun t : AppendIdx.Tail i v w => t.1.1) hne
    let x := q.representative.shift (endpointQPDegree D cutoff i v)
    let s : AppendIdx.Tail i v w := ⟨x.tailKey, x, rfl⟩
    have hs : ¬ s ∈ (E (endpointQPAction D Sc cutoff i v w g)).support := by
      intro hs
      have H := hlow s hs
      have hk := congrArg Prod.fst q.representative_tailKey
      change q.representative.1.1 = q.1.1 at hk
      change endpointQPDegree D cutoff i v + q.representative.1.1 <
        endpointQPDegree D cutoff i v at H
      omega
    have hz : appendOldCoordinate D Sc cutoff 0 x
        (endpointQPAction D Sc cutoff i v w g) = 0 := by
      have H := DFinsupp.notMem_support_iff.mp hs
      rw [appendOldCoordinateEquiv_apply] at H
      exact appendOldCoefficient_zero_heq D Sc cutoff
        (s.representative.oldTarget_eq_of_tailKey_eq x s.representative_tailKey)
        (appendOldCoordinate_heq D Sc cutoff 0 _ _ s.representative_tailKey _) H
    have ht := endpointQP_top D Sc cutoff i v w g q hmax
    change appendOldCoordinate D Sc cutoff 0 x (endpointQPAction D Sc cutoff i v w g) =
      (appendQPProductUnit D Sc i v) • oldTwist D Sc cutoff (cutoff i • D.parity i)
        v q.representative.oldTarget (E (appendProjection D Sc cutoff i v w g) q) at ht
    rw [hz] at ht
    have ht0 : oldTwist D Sc cutoff (cutoff i • D.parity i)
        v q.representative.oldTarget (E (appendProjection D Sc cutoff i v w g) q) = 0 := by
      have H := ht.symm
      change (appendQPProductUnit D Sc i v : k) •
        oldTwist D Sc cutoff (cutoff i • D.parity i) v q.representative.oldTarget
          (E (appendProjection D Sc cutoff i v w g) q) =
            (0 : Old D Sc cutoff v q.representative.oldTarget) at H
      exact (appendQPProductUnit D Sc i v).isUnit.smul_eq_zero.mp H
    have hzero := congrArg (oldTwist D Sc cutoff (cutoff i • D.parity i)
      v q.representative.oldTarget) ht0
    rw [oldTwist_twice, map_zero] at hzero
    exact (DFinsupp.mem_support_iff.mp hq) hzero
  exact ⟨hg, endpointQPAction_zero_of_projection_zero D Sc cutoff i v w g hg⟩

theorem endpointQPAction_congr (i : I) (v w : List I)
    (g h : hom D Sc cutoff (v ++ [i]) w)
    (he : appendProjection D Sc cutoff i v w g = appendProjection D Sc cutoff i v w h) :
    endpointQPAction D Sc cutoff i v w g = endpointQPAction D Sc cutoff i v w h := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply endpointQPAction_zero_of_projection_zero
  rw [map_sub, he, sub_self]

theorem endpointQP_division_unique (i : I) (v w : List I)
    (g h : hom D Sc cutoff (v ++ [i]) w)
    (r s : AppendTarget D Sc cutoff i v w)
    (hr : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w r).support,
      t.1.1 < endpointQPDegree D cutoff i v)
    (hs : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w s).support,
      t.1.1 < endpointQPDegree D cutoff i v)
    (he : endpointQPAction D Sc cutoff i v w g + r =
      endpointQPAction D Sc cutoff i v w h + s) :
    appendProjection D Sc cutoff i v w g = appendProjection D Sc cutoff i v w h ∧ r = s := by
  have hd : endpointQPAction D Sc cutoff i v w (g - h) = s - r := by
    rw [map_sub]; apply (sub_eq_sub_iff_add_eq_add).mpr
    exact he.trans (add_comm _ _)
  have hl : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (endpointQPAction D Sc cutoff i v w (g - h))).support,
      t.1.1 < endpointQPDegree D cutoff i v := by
    intro t ht
    rw [hd, map_sub] at ht
    by_contra hn
    have hs0 : (appendOldCoordinateEquiv D Sc cutoff 0 i v w s) t = 0 :=
      DFinsupp.notMem_support_iff.mp (fun ht => hn (hs t ht))
    have hr0 : (appendOldCoordinateEquiv D Sc cutoff 0 i v w r) t = 0 :=
      DFinsupp.notMem_support_iff.mp (fun ht => hn (hr t ht))
    exact (DFinsupp.mem_support_iff.mp ht) (by
      rw [DFinsupp.sub_apply, hs0, hr0, sub_self])
  obtain ⟨hp, ha⟩ := endpointQPAction_low D Sc cutoff i v w (g - h) hl
  rw [map_sub, sub_eq_zero] at hp
  exact ⟨hp, (sub_eq_zero.mp (hd.symm.trans ha)).symm⟩

def endpointQPDescended (i : I) (v w : List I) :
    AppendTarget D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v w := by
  let P := appendProjection D Sc cutoff i v w
  let A := endpointQPAction D Sc cutoff i v w
  let lift := fun z => (appendProjection_surjective D Sc cutoff i v w z).choose
  have hl (z) : P (lift z) = z :=
    (appendProjection_surjective D Sc cutoff i v w z).choose_spec
  exact {
    toFun := fun z => A (lift z)
    map_add' := fun a b => by
      rw [← map_add]
      apply endpointQPAction_congr
      rw [map_add, hl, hl, hl]
    map_smul' := fun c a => by
      change A (lift (c • a)) = c • A (lift a)
      rw [← map_smul]
      apply endpointQPAction_congr
      rw [map_smul, hl, hl] }

theorem endpointQPDescended_projection (i : I) (v w : List I)
    (g : hom D Sc cutoff (v ++ [i]) w) :
    endpointQPDescended D Sc cutoff i v w (appendProjection D Sc cutoff i v w g) =
      endpointQPAction D Sc cutoff i v w g := by
  apply endpointQPAction_congr
  exact (appendProjection_surjective D Sc cutoff i v w _).choose_spec

theorem endpointQPDescended_low (i : I) (v w : List I)
    (z : AppendTarget D Sc cutoff i v w)
    (hz : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (endpointQPDescended D Sc cutoff i v w z)).support,
      t.1.1 < endpointQPDegree D cutoff i v) : z = 0 := by
  obtain ⟨g, rfl⟩ := appendProjection_surjective D Sc cutoff i v w z
  rw [endpointQPDescended_projection] at hz
  exact (endpointQPAction_low D Sc cutoff i v w g hz).1

theorem endpointQPDescended_division_unique (i : I) (v w : List I)
    (a b r s : AppendTarget D Sc cutoff i v w)
    (hr : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w r).support,
      t.1.1 < endpointQPDegree D cutoff i v)
    (hs : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w s).support,
      t.1.1 < endpointQPDegree D cutoff i v)
    (he : endpointQPDescended D Sc cutoff i v w a + r =
      endpointQPDescended D Sc cutoff i v w b + s) : a = b ∧ r = s := by
  obtain ⟨g, rfl⟩ := appendProjection_surjective D Sc cutoff i v w a
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v w b
  rw [endpointQPDescended_projection, endpointQPDescended_projection] at he
  exact endpointQP_division_unique D Sc cutoff i v w g h r s hr hs he

theorem endpointQP_division_existsUnique (i : I) (v w : List I)
    (z : AppendTarget D Sc cutoff i v w) :
    ∃! qr : AppendTarget D Sc cutoff i v w × AppendTarget D Sc cutoff i v w,
      z = endpointQPDescended D Sc cutoff i v w qr.1 + qr.2 ∧
      ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w qr.2).support,
        t.1.1 < endpointQPDegree D cutoff i v := by
  obtain ⟨g, r, he, hr⟩ := endpointQP_division D Sc cutoff i v w z
  refine ⟨⟨appendProjection D Sc cutoff i v w g, r⟩, ⟨?_, hr⟩, ?_⟩
  · rw [endpointQPDescended_projection]
    exact he
  · intro qr hqr
    apply Prod.ext
    · exact (endpointQPDescended_division_unique D Sc cutoff i v w _ _ _ _ hqr.2 hr
        (hqr.1.symm.trans (by rw [endpointQPDescended_projection]; exact he))).1
    · exact (endpointQPDescended_division_unique D Sc cutoff i v w _ _ _ _ hqr.2 hr
        (hqr.1.symm.trans (by rw [endpointQPDescended_projection]; exact he))).2

def endpointQPLow (i : I) (v w : List I) : Submodule k (AppendTarget D Sc cutoff i v w) where
  carrier := {r | ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w r).support,
    t.1.1 < endpointQPDegree D cutoff i v}
  zero_mem' := by simp only [map_zero, DFinsupp.support_zero, Finset.notMem_empty,
    false_implies, implies_true, Set.mem_ofPred_eq]
  add_mem' := by
    intro a b ha hb t ht
    rw [map_add] at ht
    rcases Finset.mem_union.mp (DFinsupp.support_add ht) with ht | ht
    · exact ha t ht
    · exact hb t ht
  smul_mem' := by
    intro c a ha t ht
    by_contra hn
    have hz : (appendOldCoordinateEquiv D Sc cutoff 0 i v w a) t = 0 :=
      DFinsupp.notMem_support_iff.mp (fun ht => hn (ha t ht))
    exact (DFinsupp.mem_support_iff.mp ht) (by rw [map_smul, DFinsupp.smul_apply, hz, smul_zero])

def endpointQPRecompose (i : I) (v w : List I) :
    (AppendTarget D Sc cutoff i v w × endpointQPLow D Sc cutoff i v w) →ₗ[k]
      AppendTarget D Sc cutoff i v w where
  toFun qr := endpointQPDescended D Sc cutoff i v w qr.1 + qr.2.val
  map_add' a b := by
    change endpointQPDescended D Sc cutoff i v w (a.1 + b.1) + (a.2.val + b.2.val) = _
    rw [map_add]
    abel
  map_smul' c a := by
    change endpointQPDescended D Sc cutoff i v w (c • a.1) + c • a.2.val = _
    simp only [map_smul, smul_add, RingHom.id_apply]

theorem endpointQPRecompose_bijective (i : I) (v w : List I) :
    Function.Bijective (endpointQPRecompose D Sc cutoff i v w) := by
  constructor
  · intro a b he
    have H := endpointQPDescended_division_unique D Sc cutoff i v w
      a.1 b.1 a.2.val b.2.val a.2.property b.2.property he
    exact Prod.ext H.1 (Subtype.ext H.2)
  · intro z
    obtain ⟨qr, hqr, _⟩ := endpointQP_division_existsUnique D Sc cutoff i v w z
    exact ⟨⟨qr.1, ⟨qr.2, hqr.2⟩⟩, hqr.1.symm⟩

/-- Canonical linear quotient and low-degree remainder for the concrete numerator. -/
def endpointQPDivisionEquiv (i : I) (v w : List I) :
    AppendTarget D Sc cutoff i v w ≃ₗ[k]
      (AppendTarget D Sc cutoff i v w × endpointQPLow D Sc cutoff i v w) :=
  (LinearEquiv.ofBijective (endpointQPRecompose D Sc cutoff i v w)
    (endpointQPRecompose_bijective D Sc cutoff i v w)).symm

theorem endpointQPDivisionEquiv_spec (i : I) (v w : List I)
    (z : AppendTarget D Sc cutoff i v w) :
    endpointQPDescended D Sc cutoff i v w (endpointQPDivisionEquiv D Sc cutoff i v w z).1 +
      (endpointQPDivisionEquiv D Sc cutoff i v w z).2.val = z :=
  (LinearEquiv.ofBijective (endpointQPRecompose D Sc cutoff i v w)
    (endpointQPRecompose_bijective D Sc cutoff i v w)).apply_symm_apply z


/-- Division of a recomposed quotient/remainder pair is the prescribed pair. -/
theorem endpointQPDivisionEquiv_recompose (i : I) (v w : List I)
    (q : AppendTarget D Sc cutoff i v w) (r : endpointQPLow D Sc cutoff i v w) :
    endpointQPDivisionEquiv D Sc cutoff i v w
      (endpointQPDescended D Sc cutoff i v w q + r.val) = (q, r) :=
  (LinearEquiv.ofBijective (endpointQPRecompose D Sc cutoff i v w)
    (endpointQPRecompose_bijective D Sc cutoff i v w)).symm_apply_apply (q, r)

/-- The local division inverse on the literal numerator image. -/
theorem endpointQPDivisionEquiv_numerator (i : I) (v w : List I)
    (g : hom D Sc cutoff (v ++ [i]) w) :
    endpointQPDivisionEquiv D Sc cutoff i v w
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ g)) =
      (appendProjection D Sc cutoff i v w g, 0) := by
  change endpointQPDivisionEquiv D Sc cutoff i v w (endpointQPAction D Sc cutoff i v w g) = _
  simpa only [endpointQPDescended_projection, Submodule.coe_zero, add_zero] using
    endpointQPDivisionEquiv_recompose D Sc cutoff i v w
      (appendProjection D Sc cutoff i v w g) 0

/-- Exact divisibility by the actual numerator is equivalent to vanishing canonical remainder. -/
theorem endpointQP_remainder_zero_iff (i : I) (v w : List I)
    (z : AppendTarget D Sc cutoff i v w) :
    (endpointQPDivisionEquiv D Sc cutoff i v w z).2 = 0 ↔
      ∃ g : hom D Sc cutoff (v ++ [i]) w,
        appendProjection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
            endpointELV D Sc cutoff i v ≫ g) = z := by
  constructor
  · intro hz
    obtain ⟨g, hg⟩ := appendProjection_surjective D Sc cutoff i v w
      (endpointQPDivisionEquiv D Sc cutoff i v w z).1
    refine ⟨g, ?_⟩
    have H := endpointQPDivisionEquiv_spec D Sc cutoff i v w z
    rw [hz, Submodule.coe_zero, add_zero, ← hg, endpointQPDescended_projection] at H
    exact H
  · rintro ⟨g, rfl⟩
    rw [endpointQPDivisionEquiv_numerator]

end OddMath.QuiverHecke.ELVOld

