/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVQPOdd
/-!
# Signed moving-power coordinates

Every unsigned moving dot power descends through the old cyclotomic relations.
Its coordinate action shifts the moving exponent and applies the total-parity
involution to the old coefficient. The exact coordinate and support bound are
inputs to signed polynomial regularity; no parity-zero restriction is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem movingPower_succ_comp (i : I) (v : List I) (d : ℕ) :
    movingPower D Sc cutoff i v (d + 1) =
      movingPower D Sc cutoff i v 1 ≫ movingPower D Sc cutoff i v d := by
  change affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ (d + 1) : End _) =
    affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ 1 : End _) ≫
      affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ d : End _)
  rw [pow_succ, End.mul_def, affineUnit_comp, pow_one]

theorem movingPower_insert_twist (i : I) {v t : List I} (d : ℕ)
    (r : hom D Sc cutoff v t) :
    movingPower D Sc cutoff i v d ≫ insert D Sc cutoff i v t r =
      insert D Sc cutoff i v t (twist k (d • D.parity i) r) ≫
        movingPower D Sc cutoff i t d := by
  induction d with
  | zero =>
    change (𝟙 (obj D Sc cutoff (i :: v))) ≫ insert D Sc cutoff i v t r =
      insert D Sc cutoff i v t (twist k (0 • D.parity i) r) ≫ 𝟙 _
    simp
  | succ d ih =>
    rw [movingPower_succ_comp, Category.assoc, ih, ← Category.assoc,
      movingDot_insert, Category.assoc, ← movingPower_succ_comp]
    rw [← twist_add, succ_nsmul, add_comm]

/-- Every moving power preserves the old cyclotomic relations. -/
theorem movingPower_relations_twist (i : I) {v w : List I} (d : ℕ)
    {h : hom D Sc cutoff (i :: v) w} (hh : h ∈ relations D Sc cutoff i v w) :
    movingPower D Sc cutoff i v d ≫ h ∈ relations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, f, rfl⟩ := hh
    rw [← Category.assoc, movingPower_insert_twist, Category.assoc]
    exact Submodule.subset_span ⟨t, _, twist_ideal D Sc cutoff _ hr, _, rfl⟩
  | zero => simp only [Limits.comp_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c ha

/-- Unsigned moving powers on the quotient, without a parity restriction. -/
def signedMovingPowerTarget (i : I) (v w : List I) (d : ℕ) :
    Target D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  (relations D Sc cutoff i v w).mapQ (relations D Sc cutoff i v w)
    (Linear.leftComp k _ (movingPower D Sc cutoff i v d))
    (fun _ hh => movingPower_relations_twist D Sc cutoff i d hh)

@[simp] theorem signedMovingPowerTarget_projection (i : I) (v w : List I) (d : ℕ)
    (h : hom D Sc cutoff (i :: v) w) :
    signedMovingPowerTarget D Sc cutoff i v w d (projection D Sc cutoff i v w h) =
      projection D Sc cutoff i v w (movingPower D Sc cutoff i v d ≫ h) := rfl

private theorem movingPower_tail_shift {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) :
    movingPower D Sc cutoff i x.oldTarget d ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x :
        hom D Sc cutoff (i :: x.oldTarget) w) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc (x.shift d) : hom D Sc cutoff (i :: x.oldTarget) w) := by
  change affineUnit D Sc cutoff _ _ _ ≫ affineUnit D Sc cutoff _ _ _ =
    affineUnit D Sc cutoff _ _ _
  rw [← affineUnit_comp, prependTail_shift]

/-- The signed coefficient shift for the unsigned moving operator. -/
theorem signedMovingPower_pair_shift (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) (b : Old D Sc cutoff v x.oldTarget) :
    signedMovingPowerTarget D Sc cutoff i v w d
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) b) =
      pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc (x.shift d))
        (oldTwist D Sc cutoff (d • D.parity i) v x.oldTarget b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  let h : hom D Sc cutoff (i :: x.oldTarget) w :=
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x
  let h' : hom D Sc cutoff (i :: x.oldTarget) w :=
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc (x.shift d)
  change projection D Sc cutoff i v w
    (movingPower D Sc cutoff i v d ≫ (insert D Sc cutoff i v x.oldTarget (twist k p r) ≫ h)) =
    projection D Sc cutoff i v w
      (insert D Sc cutoff i v x.oldTarget (twist k p (twist k (d • D.parity i) r)) ≫ h')
  apply congrArg (projection D Sc cutoff i v w)
  calc
    _ = (movingPower D Sc cutoff i v d ≫
        insert D Sc cutoff i v x.oldTarget (twist k p r)) ≫ h :=
      (Category.assoc _ _ _).symm
    _ = (insert D Sc cutoff i v x.oldTarget (twist k (d • D.parity i) (twist k p r)) ≫
        movingPower D Sc cutoff i x.oldTarget d) ≫ h :=
      congrArg (fun a => a ≫ h) (movingPower_insert_twist D Sc cutoff i d _)
    _ = insert D Sc cutoff i v x.oldTarget (twist k (d • D.parity i) (twist k p r)) ≫
        (movingPower D Sc cutoff i x.oldTarget d ≫ h) := Category.assoc _ _ _
    _ = insert D Sc cutoff i v x.oldTarget (twist k (d • D.parity i) (twist k p r)) ≫ h' :=
      congrArg (fun a => insert D Sc cutoff i v x.oldTarget
        (twist k (d • D.parity i) (twist k p r)) ≫ a) (movingPower_tail_shift D Sc cutoff x d)
    _ = _ := by rw [← twist_add, ← twist_add, add_comm p]

/-- Simultaneous coordinates detect the shifted coefficient for every finite coordinate vector. -/
theorem signedMovingPower_coordinate_shift (p : ZMod 2) {i : I} {v w : List I}
    (q : PrependIdx.Tail i v w) (d : ℕ)
    (f : PrependOldCoordinates D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p (q.representative.shift d)
      (signedMovingPowerTarget D Sc cutoff i v w d
        (prependOldReconstruct D Sc cutoff p i v w f)) = oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget (f q) := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply]
  | add f g hf hg => simp only [map_add, hf, hg, DirectSum.add_apply, map_add]
  | of t b =>
    change prependOldCoordinate D Sc cutoff p (q.representative.shift d)
      (signedMovingPowerTarget D Sc cutoff i v w d
        (prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ t b))) = _
    rw [prependOldReconstruct, DirectSum.toModule_lof, signedMovingPower_pair_shift]
    by_cases ht : t = q
    · subst t
      erw [prependOldCoordinate_pair, DirectSum.of_eq_same]
    · erw [prependOldCoordinate_pair_off]
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm ht), map_zero]
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
theorem signedMovingPower_coordinate (p : ZMod 2) {i : I} {v w : List I}
    (q : PrependIdx.Tail i v w) (d : ℕ) (z : Target D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p (q.representative.shift d)
      (signedMovingPowerTarget D Sc cutoff i v w d z) =
      oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget
        (prependOldCoordinateEquiv D Sc cutoff p i v w z q) := by
  simpa only [prependOldReconstruct_coordinateEquiv] using
    signedMovingPower_coordinate_shift D Sc cutoff p q d
      (prependOldCoordinateEquiv D Sc cutoff p i v w z)

/-- No output coordinate lies above the input moving support shifted by the power. -/
theorem signedMovingPower_above (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) (f : PrependOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, d + q.1.1 < x.1.1) :
    prependOldCoordinate D Sc cutoff p x
      (signedMovingPowerTarget D Sc cutoff i v w d
        (prependOldReconstruct D Sc cutoff p i v w f)) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) :=
    (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [prependOldReconstruct, DirectSum.toModule_lof, signedMovingPower_pair_shift]
  apply prependOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst he
  have hk := congrArg Prod.fst q.representative_tailKey
  have hh := h q hq
  change x.1.1 = d + q.representative.1.1 at hn
  change q.representative.1.1 = q.1.1 at hk
  omega

end OddMath.QuiverHecke.ELVOld
