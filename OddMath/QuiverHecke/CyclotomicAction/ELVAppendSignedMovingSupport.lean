/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendMovingSupport
/-! # Signed append moving powers in every degree

The actual append moving power shifts finite append-PBW support and twists
the entire old-Hom coefficient by its parity. No even-power hypothesis is
imposed. These signed top and support formulas supply the odd-cutoff step
in the literal endpoint ELV polynomial normalization of
`DeformedBoundaryDivision.md` §3.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem appendMovingPower_rightContext_twist (i : I) {u v : List I} (d : ℕ)
    (c : hom D Sc cutoff u v) :
    appendMovingPower D Sc cutoff i u d ≫ rightContext D Sc cutoff [i] u v c =
      rightContext D Sc cutoff [i] u v (twist k (d • D.parity i) c) ≫
        appendMovingPower D Sc cutoff i v d := by
  rw [appendMovingPower_whisker, appendMovingPower_whisker,
    trailing_comp_rightContext D Sc cutoff (v := u) (w := v)
      (firstDot_pow_parity D Sc i [] d)]

private theorem appendPower_tail_signed {i : I} {v w : List I}
    (x : AppendIdx i v w) (d : ℕ) :
    appendMovingPower D Sc cutoff i x.oldTarget d ≫
      affineUnit D Sc cutoff _ _ (appendTail D Sc x) =
      affineUnit D Sc cutoff _ _ (appendTail D Sc (x.shift d)) := by
  rw [appendMovingPower, ← affineUnit_comp, appendTail_shift]
  rfl

/-- Every moving power shifts the append exponent with the total old-Hom twist. -/
theorem signedAppendMovingPower_pair_shift (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (d : ℕ) (b : Old D Sc cutoff v x.oldTarget) :
    appendMovingPowerTarget D Sc cutoff i v w d
      (appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x) b) =
      appendPair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          appendTail D Sc (x.shift d))
        (oldTwist D Sc cutoff (d • D.parity i) v x.oldTarget b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  change appendProjection D Sc cutoff i v w
    (appendMovingPower D Sc cutoff i v d ≫
      (rightContext D Sc cutoff [i] v x.oldTarget (twist k p r) ≫
        affineUnit D Sc cutoff _ _ (appendTail D Sc x))) =
    appendProjection D Sc cutoff i v w
      (rightContext D Sc cutoff [i] v x.oldTarget (twist k p (twist k (d • D.parity i) r)) ≫
        affineUnit D Sc cutoff _ _ (appendTail D Sc (x.shift d)))
  rw [← Category.assoc, appendMovingPower_rightContext_twist, Category.assoc,
    appendPower_tail_signed]
  rw [← twist_add, ← twist_add]
  exact congrArg (fun a : ZMod 2 => appendProjection D Sc cutoff i v w
    (rightContext D Sc cutoff [i] v x.oldTarget (twist k a r) ≫
      affineUnit D Sc cutoff _ _ (appendTail D Sc (x.shift d))))
    (add_comm (d • D.parity i) p)

/-- Simultaneous coordinates detect the shifted coefficient for every finite coordinate vector. -/
theorem signedAppendMovingPower_coordinate_shift (p : ZMod 2) {i : I} {v w : List I}
    (q : AppendIdx.Tail i v w) (d : ℕ)
    (f : AppendOldCoordinates D Sc cutoff i v w) :
    appendOldCoordinate D Sc cutoff p (q.representative.shift d)
      (appendMovingPowerTarget D Sc cutoff i v w d
        (appendOldReconstruct D Sc cutoff p i v w f)) = oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget (f q) := by
  induction f using DirectSum.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
    exact (map_zero (oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget)).symm
  | add f g hf hg =>
    rw [map_add, map_add, map_add]
    exact (congrArg₂ (fun a b : Old D Sc cutoff v q.representative.oldTarget => a + b) hf hg).trans
      (map_add (oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget) (f q) (g q)).symm
  | of t b =>
    change appendOldCoordinate D Sc cutoff p (q.representative.shift d)
      (appendMovingPowerTarget D Sc cutoff i v w d
        (appendOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ t b))) = _
    rw [appendOldReconstruct, DirectSum.toModule_lof, signedAppendMovingPower_pair_shift]
    by_cases ht : t = q
    · subst t
      erw [appendOldCoordinate_pair, DirectSum.of_eq_same]
    · erw [appendOldCoordinate_pair_off]
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm ht)]
        exact (map_zero (oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget)).symm
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



/-- Exact shifted coordinate of an arbitrary quotient element. -/
theorem signedAppendMovingPower_coordinate (p : ZMod 2) {i : I} {v w : List I}
    (q : AppendIdx.Tail i v w) (d : ℕ) (z : AppendTarget D Sc cutoff i v w) :
    appendOldCoordinate D Sc cutoff p (q.representative.shift d)
      (appendMovingPowerTarget D Sc cutoff i v w d z) =
      oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget
        (appendOldCoordinateEquiv D Sc cutoff p i v w z q) := by
  simpa only [appendOldReconstruct_coordinateEquiv] using
    signedAppendMovingPower_coordinate_shift D Sc cutoff p q d
      (appendOldCoordinateEquiv D Sc cutoff p i v w z)

/-- No output coordinate lies above the input moving support shifted by the power. -/
theorem signedAppendMovingPower_above (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (d : ℕ) (f : AppendOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, d + q.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff p x
      (appendMovingPowerTarget D Sc cutoff i v w d
        (appendOldReconstruct D Sc cutoff p i v w f)) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) :=
    (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [appendOldReconstruct, DirectSum.toModule_lof, signedAppendMovingPower_pair_shift]
  apply appendOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst he
  have hk := congrArg Prod.fst q.representative_tailKey
  have hh := h q hq
  change x.1.1 = d + q.representative.1.1 at hn
  change q.representative.1.1 = q.1.1 at hk
  omega

theorem appendOldSource_signedMovingPower_above (p : ZMod 2) {i : I} {v w : List I}
    (x : AppendIdx i v w) (d : ℕ) (c : hom D Sc cutoff v v)
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
  rw [appendOldReconstruct, DirectSum.toModule_lof, signedAppendMovingPower_pair_shift]
  have hoff : x.tailKey ≠ (q.representative.shift d).tailKey := by
    intro he
    have hn := congrArg Prod.fst he
    have hk := congrArg Prod.fst q.representative_tailKey
    have hh := h q hq
    change x.1.1 = d + q.representative.1.1 at hn
    change q.representative.1.1 = q.1.1 at hk
    omega
  exact (congrArg (appendOldCoordinate D Sc cutoff p x)
    (appendOldSourceTarget_pair D Sc cutoff p (q.representative.shift d) c
      (oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget (f q)))).trans
    (appendOldCoordinate_pair_off D Sc cutoff p x (q.representative.shift d) hoff _)


end OddMath.QuiverHecke.ELVOld
