/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendRowsShift
/-! # Moving support in append quotient coordinates

Positive even moving powers shift the actual append PBW exponent. Arbitrary old
operators change only the full old quotient coefficient. Finite maximal support
therefore proves moving-minus-old cancellation, without exterior flatness.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem appendPower_tail {i : I} {v w : List I}
    (x : AppendIdx i v w) (d : ℕ) :
    appendMovingPower D Sc cutoff i x.oldTarget d ≫
      affineUnit D Sc cutoff _ _ (appendTail D Sc x) =
      affineUnit D Sc cutoff _ _ (appendTail D Sc (x.shift d)) := by
  rw [appendMovingPower, ← affineUnit_comp, appendTail_shift]
  rfl

/-- The moving dot power shifts the exponent, with every old quotient coefficient retained. -/
theorem appendMovingPower_pair_shift (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (d : ℕ) (hd : d • D.parity i = 0)
    (b : Old D Sc cutoff v x.oldTarget) :
    appendMovingPowerTarget D Sc cutoff i v w d
      (appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x) b) =
      appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc (x.shift d)) b := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  change appendMovingPowerTarget D Sc cutoff i v w d
    (appendProjection D Sc cutoff i v w (rightContext D Sc cutoff [i] v x.oldTarget (twist k p r) ≫
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x)) =
    appendProjection D Sc cutoff i v w (rightContext D Sc cutoff [i] v x.oldTarget (twist k p r) ≫
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc (x.shift d))
  rw [appendMovingPowerTarget_projection, ← Category.assoc,
    appendMovingPower_rightContext_cross D Sc cutoff i d hd, Category.assoc]
  exact congrArg (fun f => appendProjection D Sc cutoff i v w
    (rightContext D Sc cutoff [i] v x.oldTarget (twist k p r) ≫ f))
      (appendPower_tail D Sc cutoff x d)

/-- Read back the old coefficient of a normalized single tail. -/
theorem appendOldCoordinate_pair (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (b : Old D Sc cutoff v x.oldTarget) :
    appendOldCoordinate D Sc cutoff p x
      (appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x) b) = b := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  rw [appendPair_mk, appendOldCoordinate_projection, appendExtractOldQuotient_insert_tail, twist_twist]

/-- Different moving tails have disjoint old quotient coordinates. -/
theorem appendOldCoordinate_pair_off (p : ZMod 2) {i : I} {v w : List I}
    (x z : AppendIdx i v w) (h : x.tailKey ≠ z.tailKey)
    (b : Old D Sc cutoff v z.oldTarget) :
    appendOldCoordinate D Sc cutoff p x
      (appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc z) b) = 0 := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v z.oldTarget).mkQ_surjective b
  rw [appendPair_mk, appendOldCoordinate_projection]
  exact appendExtractOldQuotient_insert_off_tail D Sc cutoff p x z h _

/-- Simultaneous coordinates detect the shifted coefficient for every finite coordinate vector. -/
theorem appendMovingPower_coordinate_shift (p : ZMod 2) {i : I} {v w : List I}
    (q : AppendIdx.Tail i v w) (d : ℕ) (hd : d • D.parity i = 0)
    (f : AppendOldCoordinates D Sc cutoff i v w) :
    appendOldCoordinate D Sc cutoff p (q.representative.shift d)
      (appendMovingPowerTarget D Sc cutoff i v w d
        (appendOldReconstruct D Sc cutoff p i v w f)) = f q := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply]
  | add f g hf hg => simp only [map_add, hf, hg, DirectSum.add_apply]
  | of t b =>
    change appendOldCoordinate D Sc cutoff p (q.representative.shift d)
      (appendMovingPowerTarget D Sc cutoff i v w d
        (appendOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ t b))) = _
    rw [appendOldReconstruct, DirectSum.toModule_lof, appendMovingPower_pair_shift D Sc cutoff p _ d hd]
    by_cases ht : t = q
    · subst t
      rw [appendOldCoordinate_pair, DirectSum.of_eq_same]
    · rw [appendOldCoordinate_pair_off]
      · symm
        exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm ht)
      · intro he
        apply ht
        apply Subtype.ext
        have hk : q.representative.tailKey = t.representative.tailKey := by
          apply Prod.ext
          · have hn := congrArg Prod.fst he
            change d + q.representative.1.1 = d + t.representative.1.1 at hn
            exact Nat.add_left_cancel hn
          · have hs := congrArg Prod.snd he
            exact hs
        exact t.representative_tailKey.symm.trans (hk.symm.trans q.representative_tailKey)


/-- The other operator changes only the old coefficient; the total parity twist is retained. -/
theorem appendOldSourceTarget_pair (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (c : hom D Sc cutoff v v)
    (b : Old D Sc cutoff v x.oldTarget) :
    appendOldSourceTarget D Sc cutoff i v w c
      (appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x) b) =
      appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x)
        (oldPrecomp D Sc cutoff v x.oldTarget (twist k p c) b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  change appendProjection D Sc cutoff i v w
    (rightContext D Sc cutoff [i] v v c ≫ (rightContext D Sc cutoff [i] v x.oldTarget (twist k p r) ≫
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x)) =
    appendProjection D Sc cutoff i v w
    (rightContext D Sc cutoff [i] v x.oldTarget (twist k p (twist k p c ≫ r)) ≫
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x)
  rw [twist_comp, twist_twist, rightContext_comp, Category.assoc]

/-- A coordinate above the input moving-exponent bound stays zero under the actual old action. -/
theorem appendOldSourceTarget_above (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (c : hom D Sc cutoff v v)
    (f : AppendOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, q.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff p x
      (appendOldSourceTarget D Sc cutoff i v w c (appendOldReconstruct D Sc cutoff p i v w f)) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) := by
    exact (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [appendOldReconstruct, DirectSum.toModule_lof, appendOldSourceTarget_pair]
  apply appendOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst (he.trans q.representative_tailKey)
  have hh := h q hq
  change x.1.1 = q.1.1 at hn
  omega

/-- Finite support cancels the actual positive moving power against any old source action. -/
theorem appendMovingPower_eq_oldSource (p : ZMod 2) (i : I) (v w : List I)
    (d : ℕ) (hd : d • D.parity i = 0) (hpos : 0 < d)
    (c : hom D Sc cutoff v v) (z : AppendTarget D Sc cutoff i v w)
    (hz : appendMovingPowerTarget D Sc cutoff i v w d z = appendOldSourceTarget D Sc cutoff i v w c z) :
    z = 0 := by
  let f := appendOldCoordinateEquiv D Sc cutoff p i v w z
  suffices hf : f = 0 by
    exact (appendOldCoordinateEquiv D Sc cutoff p i v w).injective (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have he := appendMovingPower_coordinate_shift D Sc cutoff p q d hd f
  rw [appendOldReconstruct_coordinateEquiv, hz] at he
  have hb : ∀ t ∈ f.support, t.1.1 < (q.representative.shift d).1.1 := by
    intro t ht
    have hm := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change t.1.1 < d + q.representative.1.1
    omega
  have ho := appendOldSourceTarget_above D Sc cutoff p (q.representative.shift d) c f hb
  rw [appendOldReconstruct_coordinateEquiv] at ho
  exact (DFinsupp.mem_support_iff.mp hq) (he.symm.trans ho)

/-- The actual moving-minus-old right operator is injective; no filtration assumption is supplied. -/
theorem appendMovingPower_sub_oldSource_injective (p : ZMod 2) (i : I) (v w : List I)
    (d : ℕ) (hd : d • D.parity i = 0) (hpos : 0 < d) (c : hom D Sc cutoff v v) :
    Function.Injective (appendMovingPowerTarget D Sc cutoff i v w d -
      appendOldSourceTarget D Sc cutoff i v w c) := by
  intro z y h
  apply sub_eq_zero.mp
  apply appendMovingPower_eq_oldSource D Sc cutoff p i v w d hd hpos c (z - y)
  simp only [LinearMap.sub_apply] at h
  simp only [map_sub]
  exact sub_eq_sub_iff_sub_eq_sub.mp h


theorem appendOldSource_movingPower_above (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (d : ℕ) (hd : d • D.parity i = 0) (c : hom D Sc cutoff v v)
    (f : AppendOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, d + q.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff p x
      (appendOldSourceTarget D Sc cutoff i v w c
        (appendMovingPowerTarget D Sc cutoff i v w d
          (appendOldReconstruct D Sc cutoff p i v w f))) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) :=
    (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [appendOldReconstruct, DirectSum.toModule_lof, appendMovingPower_pair_shift D Sc cutoff p _ d hd,
    appendOldSourceTarget_pair]
  apply appendOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst he
  have hk := congrArg Prod.fst q.representative_tailKey
  have hh := h q hq
  change x.1.1 = d + q.representative.1.1 at hn
  change q.representative.1.1 = q.1.1 at hk
  omega


end OddMath.QuiverHecke.ELVOld
