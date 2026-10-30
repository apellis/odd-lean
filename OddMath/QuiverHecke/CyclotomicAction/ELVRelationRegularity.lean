/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVSignedMovingPower

/-!
# Regularity of the moving cyclotomic relation

The explicit odd ELV and even monic coefficients express the moving relation
as its top unsigned moving power plus lower powers with old coefficient actions.
At a maximal moving-support coordinate the lower terms vanish. The top term
is the total-parity involution of the original coefficient, hence detects it.
This proves cancellation in the old-only quotient over arbitrary commutative
rings, including zero cutoffs, without flatness or nonvanishing hypotheses.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem movingPower_oldSource_above (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) (c : hom D Sc cutoff v v)
    (f : PrependOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, d + q.1.1 < x.1.1) :
    prependOldCoordinate D Sc cutoff p x
      (signedMovingPowerTarget D Sc cutoff i v w d
        (oldSourceTarget D Sc cutoff i v w c
          (prependOldReconstruct D Sc cutoff p i v w f))) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) :=
    (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [prependOldReconstruct, DirectSum.toModule_lof, oldSourceTarget_pair,
    signedMovingPower_pair_shift]
  apply prependOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst he
  have hk := congrArg Prod.fst q.representative_tailKey
  have hh := h q hq
  change x.1.1 = d + q.representative.1.1 at hn
  change q.representative.1.1 = q.1.1 at hk
  omega

theorem movingPower_comp_coefficient (i : I) (v : List I) (d : ℕ)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    movingPower D Sc cutoff i v d ≫
      insert D Sc cutoff i v v (a ⊗ₜ[k] 𝟙 ((pres D Sc).obj (ob D v))) =
      (a ⊗ₜ[k] (dotE D Sc (i :: v) 0 ^ d : End _)) := by
  rw [insert_tmul]
  have hi : affineInsert D Sc i v v (𝟙 _) = 𝟙 _ :=
    MonoidalSupercategory.whiskerLeft_id (R := k)
      ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D v))
  rw [hi]
  change BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
    (Y := obj D Sc cutoff (i :: v)) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) _ ≫
      BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
        (Y := obj D Sc cutoff (i :: v)) a (𝟙 _) = _
  rw [BoxProd.tmulHom_comp_tmulHom
    (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: v))
    (Z := obj D Sc cutoff (i :: v))
    (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
      SKM.SYM.elvCoefficientParity D cutoff 0 from SetLike.GradedOne.one_mem)
    _ a (id_mem (R := k) _)]
  simp only [koszulSign_zero_left, one_smul, Category.comp_id]
  change (a * 1) ⊗ₜ[k] _ = _
  rw [mul_one]

theorem deformedCyclotomic_expansion (i : I) (v : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) :
    (elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (i :: v) N c) =
      ∑ j : Fin (N + 1), movingPower D Sc cutoff i v j.val ≫
        insert D Sc cutoff i v v
          (SKM.SYM.elvCoefficientQuotient D cutoff (c j) ⊗ₜ[k] 𝟙 ((pres D Sc).obj (ob D v))) := by
  change elvQuotientMap D Sc cutoff _ _ (deformedCyclotomic D Sc (i :: v) N c) = _
  unfold deformedCyclotomic
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [elvQuotientMap_source, movingPower_comp_coefficient]
  congr 1
  simp only [firstDotPower, dotE_pow, List.map_replicate]

theorem oldSourceTarget_projection (i : I) (v w : List I) (c : hom D Sc cutoff v v)
    (h : hom D Sc cutoff (i :: v) w) :
    oldSourceTarget D Sc cutoff i v w c (projection D Sc cutoff i v w h) =
      projection D Sc cutoff i v w (insert D Sc cutoff i v v c ≫ h) := rfl

theorem oldSourceTarget_id (i : I) (v w : List I) (z : Target D Sc cutoff i v w) :
    oldSourceTarget D Sc cutoff i v w (𝟙 _) z = z := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  change projection D Sc cutoff i v w (insert D Sc cutoff i v v (𝟙 _) ≫ h) = _
  rw [insert_id, Category.id_comp]

/-- Finite moving support proves cancellation for a polynomial whose top coefficient is one. -/
theorem monic_moving_sum_regular (i : I) (v w : List I) (N : ℕ)
    (c : Fin (N + 1) → hom D Sc cutoff v v) (hc : c (Fin.last N) = 𝟙 _)
    (z : Target D Sc cutoff i v w)
    (hz : (∑ j : Fin (N + 1), signedMovingPowerTarget D Sc cutoff i v w j.val
      (oldSourceTarget D Sc cutoff i v w (c j) z)) = 0) : z = 0 := by
  let f := prependOldCoordinateEquiv D Sc cutoff 0 i v w z
  suffices hf : f = 0 by
    exact (prependOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  rw [Fin.sum_univ_castSucc, hc, oldSourceTarget_id] at hz
  have he := congrArg (prependOldCoordinate D Sc cutoff 0 (q.representative.shift N)) hz
  rw [map_add, map_sum, map_zero] at he
  have hl : (∑ j : Fin N, prependOldCoordinate D Sc cutoff 0 (q.representative.shift N)
      (signedMovingPowerTarget D Sc cutoff i v w j.val
        (oldSourceTarget D Sc cutoff i v w (c j.castSucc) z))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hb : ∀ t ∈ f.support, j.val + t.1.1 < (q.representative.shift N).1.1 := by
      intro t ht
      have hm := hmax t ht
      have hk := congrArg Prod.fst q.representative_tailKey
      change q.representative.1.1 = q.1.1 at hk
      change j.val + t.1.1 < N + q.representative.1.1
      have hj := j.isLt
      omega
    simpa only [f, prependOldReconstruct_coordinateEquiv] using
      movingPower_oldSource_above D Sc cutoff 0 (q.representative.shift N)
        j.val (c j.castSucc) f hb
  change (∑ j : Fin N, prependOldCoordinate D Sc cutoff 0 (q.representative.shift N)
      (signedMovingPowerTarget D Sc cutoff i v w j.val
        (oldSourceTarget D Sc cutoff i v w (c j.castSucc) z))) +
      prependOldCoordinate D Sc cutoff 0 (q.representative.shift N)
        (signedMovingPowerTarget D Sc cutoff i v w N z) = 0 at he
  rw [hl, zero_add, signedMovingPower_coordinate] at he
  have hh := congrArg (oldTwist D Sc cutoff (N • D.parity i) v q.representative.oldTarget) he
  rw [oldTwist_twice, map_zero] at hh
  exact (DFinsupp.mem_support_iff.mp hq) hh

/-- Cancellation for the explicit coefficient-valued monic polynomial. -/
theorem projection_deformedCyclotomic_regular (i : I) (v w : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) (hc : c (Fin.last N) = 1)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      ((elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (i :: v) N c) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  apply monic_moving_sum_regular D Sc cutoff i v w N
    (fun j => SKM.SYM.elvCoefficientQuotient D cutoff (c j) ⊗ₜ[k] 𝟙 ((pres D Sc).obj (ob D v)))
  · rw [hc, map_one]
    rfl
  · rw [deformedCyclotomic_expansion, Preadditive.sum_comp, map_sum] at hh
    simpa only [oldSourceTarget_projection, signedMovingPowerTarget_projection, Category.assoc] using hh

/-- The moving cyclotomic relation is regular on the old-only quotient over every commutative ring. -/
theorem projection_relation_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w (relation D Sc cutoff i v ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  unfold relation at hh
  split_ifs at hh with hi
  · exact projection_deformedCyclotomic_regular D Sc cutoff i v w (cutoff i)
      (SKM.SYM.elvMonicCoefficient D k ⟨i, hi⟩ (cutoff i))
      (SKM.SYM.elvMonicCoefficient_top D k ⟨i, hi⟩ (cutoff i)) h hh
  · exact projection_deformedCyclotomic_regular D Sc cutoff i v w (cutoff i)
      (SKM.SYM.evenMonicCoefficient D k i (cutoff i))
      (SKM.SYM.evenMonicCoefficient_top D k i (cutoff i)) h hh

end OddMath.QuiverHecke.ELVOld
