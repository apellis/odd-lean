/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPostCoordinates
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.SignedCoefficientTransport

/-! Unsigned transport of the prescribed coefficient through the reservoir crossing. -/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace RepeatedOuterPost
open ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hj0 : StepValid (true, j) false s)
  (hi0 : StepValid (true, i) false (nextSector (true, j) false s))
  (Z : P.H (nextSector (true, i) false
    (nextSector (true, j) false (nextSector (true, i) true s))))

section Transport
variable (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (hs : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) =
    nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)))
  (Y : P.H (nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s))))

def reservoirCross :=
  (P.step (true, i) true s trivial).map
    (P.postCrossNe j i (nextSector (true, i) true s) hj0 hi0 hi hj hs Y)

def targetAlg := conjAlg (k := k)
  (P.mixedJ i i s hi (P.distinctReservoirRest i i j s hj Y)).symm

lemma targetAlg_pre :
    targetAlg P i j s hi hj Y (P.rpPreDot i s hi (P.distinctReservoirRest i i j s hj Y)) =
      zsign k (D.parity i) • P.prPreDot i i s hi (P.distinctReservoirRest i i j s hj Y) := by
  have h := P.mixedJ_conj_rpPreDot i s hi (P.distinctReservoirRest i i j s hj Y)
  rw [koszulSign_smul_eq_zsign (k := k), SKM.zmod2_mul_self] at h
  exact h

lemma targetAlg_post :
    targetAlg P i j s hi hj Y (P.rpPostDot i s hi (P.distinctReservoirRest i i j s hj Y)) =
      zsign k (D.parity i) • P.prPostDot i i s hi (P.distinctReservoirRest i i j s hj Y) := by
  have h := P.mixedJ_conj_rpPostDot i s hi (P.distinctReservoirRest i i j s hj Y)
  rw [koszulSign_smul_eq_zsign (k := k), SKM.zmod2_mul_self] at h
  exact h

private lemma cancel_slide {C : Type u} [Category C] [Preadditive C] [Linear k C]
    {A B : C} (x : End A) (y : End B) (f : A ⟶ B) (q ε : k)
    (hε : ε * ε = 1) (h : x ≫ f = ε • (f ≫ y)) :
    ((q * ε) • x) ≫ f = f ≫ (q • y) := by
  rw [Linear.smul_comp, h, smul_smul, mul_assoc, hε, mul_one, Linear.comp_smul]

lemma pre_slide :
    coefficientAlg P i j s hj0 hi0 (hs ▸ Y)
        (P.rpPreDot i (nextSector (true, j) false s) hi0 (hs ▸ Y)) ≫
      reservoirCross P i j s hj0 hi0 hi hj hs Y =
    reservoirCross P i j s hj0 hi0 hi hj hs Y ≫
      targetAlg P i j s hi hj Y
        (P.rpPreDot i s hi (P.distinctReservoirRest i i j s hj Y)) := by
  rw [coefficientAlg_pre, targetAlg_pre]
  apply cancel_slide _ _ _ _ _ (ProbeReservoir.zsign_mul_self' _)
  have hθ := (P.postCrossNe_supernatural j i (nextSector (true, i) true s)
    hj0 hi0 hi hj hs).mem Y
  have h := TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i (P.muP_preE i s)) hθ
  rw [koszulSign_smul_eq_zsign (k := k)] at h
  have hp : D.parity i * (D.parity j * D.parity i) = D.parity i * D.parity j := by
    rw [← mul_assoc, mul_right_comm, SKM.zmod2_mul_self]
  rw [hp] at h
  exact h

lemma post_slide (hij : i ≠ j) :
    coefficientAlg P i j s hj0 hi0 (hs ▸ Y)
        (P.rpPostDot i (nextSector (true, j) false s) hi0 (hs ▸ Y)) ≫
      reservoirCross P i j s hj0 hi0 hi hj hs Y =
    reservoirCross P i j s hj0 hi0 hi hj hs Y ≫
      targetAlg P i j s hi hj Y
        (P.rpPostDot i s hi (P.distinctReservoirRest i i j s hj Y)) := by
  rw [coefficientAlg_post, targetAlg_post]
  apply cancel_slide _ _ _ _ _ (ProbeReservoir.zsign_mul_self' _)
  have h := congrArg (P.step (true, i) true s trivial).map
    (P.postCrossNe_slideR j i hij.symm (nextSector (true, i) true s) hj0 hi0 hi hj hs Y)
  simp only [Functor.map_comp, Functor.map_smul] at h
  rw [mul_comm (D.parity j)] at h
  have h' := congrArg (fun f => zsign k (D.parity i * D.parity j) • f) h
  simp only [smul_smul, ProbeReservoir.zsign_mul_self', one_smul] at h'
  exact h'.symm
lemma coeff_slide (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    coefficientAlg P i j s hj0 hi0 (hs ▸ Y)
        (c.a i (nextSector (true, j) false s) hi0 (hs ▸ Y)) ≫
      reservoirCross P i j s hj0 hi0 hi hj hs Y =
    reservoirCross P i j s hj0 hi0 hi hj hs Y ≫
      targetAlg P i j s hi hj Y (c.a i s hi (P.distinctReservoirRest i i j s hj Y)) := by
  let φ := coefficientAlg P i j s hj0 hi0 (hs ▸ Y)
  let ψ := targetAlg P i j s hi hj Y
  let W := P.distinctReservoirRest i i j s hj Y
  have hφ (a b : End (P.rpObj i i (nextSector (true, j) false s) hi0 (hs ▸ Y))) :
      φ (a ≫ b) = φ a ≫ φ b := φ.map_mul b a
  have hψ (a b : End (P.rpObj i i s hi W)) : ψ (a ≫ b) = ψ a ≫ ψ b := ψ.map_mul b a
  have hx := pre_slide P i j s hj0 hi0 hi hj hs Y
  have hz := post_slide P i j s hj0 hi0 hi hj hs Y hij
  by_cases hp : D.parity i = 0
  · have ha := congrArg φ (hc.even i hp (nextSector (true, j) false s) hi0 (hs ▸ Y)).1
    have hb := congrArg ψ (hc.even i hp s hi W).2
    simp only [hφ, map_sub, show φ (𝟙 _) = 𝟙 _ from φ.map_one] at ha
    simp only [hψ, map_sub] at hb
    simpa only [one_smul] using signed_inverse_difference_transport
      _ _ _ _ _ _ (reservoirCross P i j s hj0 hi0 hi hj hs Y) (1 : k) (one_mul _)
      (hx.trans (one_smul _ _).symm) (hz.trans (one_smul _ _).symm) ha (hb.trans ψ.map_one)
  · have hp' := (Supercategory.parity_eq_zero_or_one (D.parity i)).resolve_left hp
    have ha := congrArg φ (hc.odd i hp' (nextSector (true, j) false s) hi0 (hs ▸ Y)).1
    have hb := congrArg ψ (hc.odd i hp' s hi W).1
    simp only [hφ, map_sub] at ha
    simp only [hψ, map_sub] at hb
    have hd : (P.crossDenom h i s hi W : End (P.rpObj i i s hi W)) =
        P.rpPreDot i s hi W ≫ P.rpPreDot i s hi W -
          P.rpPostDot i s hi W ≫ P.rpPostDot i s hi W := by
      simp [crossDenom, hp, sub_eq_add_neg, add_comm, pow_two, End.mul_def]
    have hd' := congrArg ψ hd
    simp only [hψ, map_sub] at hd'
    simpa only [one_smul] using signed_odd_coefficient_transport
      _ _ _ _ _ _ (reservoirCross P i j s hj0 hi0 hi hj hs Y) (1 : k) (one_mul _)
      (hx.trans (one_smul _ _).symm) (hz.trans (one_smul _ _).symm) ha hb
      (Units.map ψ.toMonoidHom (P.crossDenom h i s hi W)) hd'

end Transport

end RepeatedOuterPost
end OddMath.QuiverHecke.SwappedAssembly
