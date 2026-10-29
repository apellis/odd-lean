/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVRelationRegularity
import OddMath.QuiverHecke.CyclotomicAction.ELVQPProduct

/-!
# Regularity of the signed QP product

The actual factors have invertible highest moving coefficients. Finite moving
support in the old-only quotient proves cancellation factor by factor, retaining
the total old-coefficient parity involution and the repeated-even minus signs.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem oldSource_movingPower_above (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) (c : hom D Sc cutoff v v)
    (f : PrependOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, d + q.1.1 < x.1.1) :
    prependOldCoordinate D Sc cutoff p x
      (oldSourceTarget D Sc cutoff i v w c
        (signedMovingPowerTarget D Sc cutoff i v w d
          (prependOldReconstruct D Sc cutoff p i v w f))) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) :=
    (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [prependOldReconstruct, DirectSum.toModule_lof, signedMovingPower_pair_shift,
    oldSourceTarget_pair]
  apply prependOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst he
  have hk := congrArg Prod.fst q.representative_tailKey
  have hh := h q hq
  change x.1.1 = d + q.representative.1.1 at hn
  change q.representative.1.1 = q.1.1 at hk
  omega

theorem affineUnit_dotPower (v : List I) (b d : ℕ) :
    affineUnit D Sc cutoff v v (dotE D Sc v b ^ d) =
      sourceDotPower D Sc cutoff v b d := rfl

theorem projection_moving_dotPower (i : I) (v w : List I) (d : ℕ)
    (h : hom D Sc cutoff (i :: v) w) :
    projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ d) ≫ h) =
      signedMovingPowerTarget D Sc cutoff i v w d (projection D Sc cutoff i v w h) := rfl

theorem projection_old_dotPower (i : I) (v w : List I) (b d : ℕ)
    (h : hom D Sc cutoff (i :: v) w) :
    projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) (b + 1) ^ d) ≫ h) =
      oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b d)
        (projection D Sc cutoff i v w h) := by
  rw [oldSourceTarget_projection, insert_sourceDotPower, affineUnit_dotPower]

/-- The linear moving difference is regular even when its moving dot is odd. -/
theorem projection_dotDifference_regular (i : I) (v w : List I) (b : ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        (dotE D Sc (i :: v) (b + 1) - dotE D Sc (i :: v) 0) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  let z := projection D Sc cutoff i v w h
  let f := prependOldCoordinateEquiv D Sc cutoff 0 i v w z
  suffices hf : f = 0 by
    exact (prependOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have hb : ∀ t ∈ f.support, t.1.1 < (q.representative.shift 1).1.1 := by
    intro t ht
    have hm := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change t.1.1 < 1 + q.representative.1.1
    omega
  rw [map_sub, Preadditive.sub_comp, map_sub] at hh
  have hp : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) (b + 1)) ≫ h) =
      oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b 1) z := by
    simpa only [pow_one] using projection_old_dotPower D Sc cutoff i v w b 1 h
  have hm : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0) ≫ h) =
      signedMovingPowerTarget D Sc cutoff i v w 1 z := by
    simpa only [pow_one] using projection_moving_dotPower D Sc cutoff i v w 1 h
  rw [hp, hm] at hh
  change oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b 1) z -
    signedMovingPowerTarget D Sc cutoff i v w 1 z = 0 at hh
  have he := congrArg (prependOldCoordinate D Sc cutoff 0 (q.representative.shift 1)) hh
  rw [map_sub, map_zero, signedMovingPower_coordinate] at he
  have ho := oldSourceTarget_above D Sc cutoff 0 (q.representative.shift 1)
    (sourceDotPower D Sc cutoff v b 1) f hb
  rw [prependOldReconstruct_coordinateEquiv] at ho
  rw [ho, zero_sub, neg_eq_zero] at he
  have hh' := congrArg (oldTwist D Sc cutoff (1 • D.parity i) v q.representative.oldTarget) he
  rw [oldTwist_twice, map_zero] at hh'
  exact (DFinsupp.mem_support_iff.mp hq) hh'

/-- The prescribed distinct-colour factor has the unit `t i x` as highest moving coefficient. -/
theorem projection_qPoly_regular (i x : I) (hix : i ≠ x) (v w : List I) (b : ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        (qPoly D Sc (dotE D Sc (i :: v) 0) (dotE D Sc (i :: v) (b + 1)) i x) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  by_cases hd : D.d i x = 0
  · rw [qPoly, ite_eq_left hd, map_smul, End.one_def, affineUnit_id,
      Linear.smul_comp, Category.id_comp, map_smul] at hh
    exact (Sc.t i x).isUnit.smul_eq_zero.mp hh
  let z := projection D Sc cutoff i v w h
  let f := prependOldCoordinateEquiv D Sc cutoff 0 i v w z
  suffices hf : f = 0 by
    exact (prependOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have hpos : 0 < D.dn i x := by
    have hc := D.dn_cast hix
    omega
  have hb (d : ℕ) (hlt : d < D.dn i x) :
      ∀ t ∈ f.support, d + t.1.1 < (q.representative.shift (D.dn i x)).1.1 := by
    intro t ht
    have hm := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change d + t.1.1 < D.dn i x + q.representative.1.1
    omega
  have hlow (d e : ℕ) (hlt : d < D.dn i x) :
      prependOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i x))
        (projection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (i :: v) 0 ^ d * dotE D Sc (i :: v) (b + 1) ^ e) ≫ h)) = 0 := by
    rw [End.mul_def, affineUnit_comp, Category.assoc, projection_old_dotPower,
      projection_moving_dotPower]
    simpa only [f, prependOldReconstruct_coordinateEquiv] using
      oldSource_movingPower_above D Sc cutoff 0 (q.representative.shift (D.dn i x))
        d (sourceDotPower D Sc cutoff v b e) f (hb d hlt)
  have hold : prependOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i x))
      (projection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) (b + 1) ^ D.dn x i) ≫ h)) = 0 := by
    simpa only [pow_zero, one_mul] using hlow 0 (D.dn x i) hpos
  rw [qPoly, ite_eq_right hd, map_add, map_add, Preadditive.add_comp,
    Preadditive.add_comp, map_add, map_add] at hh
  have he := congrArg (prependOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i x))) hh
  simp only [map_add, map_zero, map_sum, Preadditive.sum_comp, map_smul,
    Linear.smul_comp] at he
  have hl : (∑ d ∈ Finset.Ioo 0 (D.dn i x), ∑ e ∈ Finset.Ioo 0 (D.dn x i),
      Sc.s i x d e • prependOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i x))
        (projection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (i :: v) 0 ^ d * dotE D Sc (i :: v) (b + 1) ^ e) ≫ h))) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd'
    apply Finset.sum_eq_zero
    intro e _
    rw [hlow d e (Finset.mem_Ioo.mp hd').2, smul_zero]
  rw [hl, hold, smul_zero, add_zero, zero_add, projection_moving_dotPower,
    signedMovingPower_coordinate] at he
  have ht := (Sc.t i x).isUnit.smul_eq_zero.mp he
  have ht' := congrArg (oldTwist D Sc cutoff (D.dn i x • D.parity i) v q.representative.oldTarget) ht
  rw [oldTwist_twice, map_zero] at ht'
  exact (DFinsupp.mem_support_iff.mp hq) ht'

/-- Every actual signed QP factor cancels in the old-only quotient. -/
theorem projection_qpFactor_regular (i : I) (v w : List I) (x : I) (b : ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (qpFactor D Sc i v x b) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  unfold qpFactor at hh
  split_ifs at hh with hx hi
  · rw [pow_two, End.mul_def, affineUnit_comp, Category.assoc] at hh
    exact projection_dotDifference_regular D Sc cutoff i v w b h
      (projection_dotDifference_regular D Sc cutoff i v w b _ hh)
  · rw [map_neg, End.one_def, affineUnit_id, Preadditive.neg_comp,
      Category.id_comp, map_neg, neg_eq_zero] at hh
    exact hh
  · exact projection_qPoly_regular D Sc cutoff i x (Ne.symm hx) v w b h hh

/-- Cancellation for a list of the prescribed factors, in their actual multiplication order. -/
theorem projection_qpFactorList_regular (i : I) (v w : List I) (l : List ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        ((l.map fun b => qpFactor D Sc i v (v.getD b i) b).prod) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  induction l generalizing h with
  | nil => simpa only [List.map_nil, List.prod_nil, End.one_def, affineUnit_id,
      Category.id_comp] using hh
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons, End.mul_def, affineUnit_comp, Category.assoc] at hh
    exact projection_qpFactor_regular D Sc cutoff i v w (v.getD b i) b h (ih _ hh)

/-- The signed all-word product is regular, without assuming any monicity or support bound. -/
theorem projection_qpProduct_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 :=
  projection_qpFactorList_regular D Sc cutoff i v w (List.range v.length) h hh

/-- Actual full-ELV QP regularity in diagram composition order.
This is the raw-quotient injectivity input to the deformed square resolution;
it does not assume that the displayed operation descends to an endomorphism. -/
theorem projection_qp_relation_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫
        relation D Sc cutoff i v ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 :=
  projection_relation_regular D Sc cutoff i v w h
    (projection_qpProduct_regular D Sc cutoff i v w _ hh)

/-- The actual crossing composite followed by the relation detects every old-only class.
Combining this with descent of Q and P proves injectivity of P. -/
theorem projection_move_relation_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (moveHom D Sc i [] v ≫ lastToFirstHom D Sc i v) ≫
        relation D Sc cutoff i v ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  have he := congrArg (act D Sc cutoff i h) (qp_projection_product D Sc cutoff i v)
  change projection D Sc cutoff i v w
      ((affineUnit D Sc cutoff _ _ (moveHom D Sc i [] v ≫ lastToFirstHom D Sc i v) ≫
        relation D Sc cutoff i v) ≫ h) =
    projection D Sc cutoff i v w
      ((affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ relation D Sc cutoff i v) ≫ h) at he
  simp only [Category.assoc] at he
  exact projection_qp_relation_regular D Sc cutoff i v w h (he.symm.trans hh)

end OddMath.QuiverHecke.ELVOld
