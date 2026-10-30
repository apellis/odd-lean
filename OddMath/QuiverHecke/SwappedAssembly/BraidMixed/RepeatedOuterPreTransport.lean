/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPreCoordinates

/-! Coefficient transport for the Ri Rj Pi diagonal of Brundan–Ellis (1.9). -/
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
namespace RepeatedOuterPre
open ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (hj0 : StepValid (true, j) false s)
  (hi0 : StepValid (true, i) false (nextSector (true, j) false s))
  (hs : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) =
    nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)))
  (Y : P.H (nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s))))

def probeReservoirCross := (P.step (true, i) true s trivial).map
  (P.postCrossNe i j (nextSector (true, i) true s) hi hj hj0 hi0 hs Y)

private lemma scale_slide {C : Type u} [Category C] [Preadditive C] [Linear k C]
    {A B : C} (x : End A) (y : End B) (f : A ⟶ B) (q ε : k)
    (h : x ≫ f = ε • (f ≫ y)) :
    (q • x) ≫ f = f ≫ ((q * ε) • y) := by
  rw [Linear.smul_comp, h, smul_smul, Linear.comp_smul]

lemma probe_pre_slide :
    RepeatedOuterPost.targetAlg P i j s hi hj (hs ▸ Y)
        (P.rpPreDot i s hi (rest P i j s hj (hs ▸ Y))) ≫
      probeReservoirCross P i j s hi hj hj0 hi0 hs Y =
    probeReservoirCross P i j s hi hj hj0 hi0 hs Y ≫
      RepeatedOuterPost.coefficientAlg P i j s hj0 hi0 Y
        (P.rpPreDot i (nextSector (true, j) false s) hi0 Y) := by
  rw [RepeatedOuterPost.targetAlg_pre, RepeatedOuterPost.coefficientAlg_pre]
  have h := TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i (P.muP_preE i s))
    ((P.postCrossNe_supernatural i j (nextSector (true, i) true s) hi hj hj0 hi0 hs).mem Y)
  rw [koszulSign_smul_eq_zsign (k := k)] at h
  have hp : D.parity i * (D.parity i * D.parity j) = D.parity i * D.parity j := by
    rw [← mul_assoc, SKM.zmod2_mul_self]
  rw [hp] at h
  exact scale_slide _ _ _ _ _ h

lemma probe_post_slide (hij : i ≠ j) :
    RepeatedOuterPost.targetAlg P i j s hi hj (hs ▸ Y)
        (P.rpPostDot i s hi (rest P i j s hj (hs ▸ Y))) ≫
      probeReservoirCross P i j s hi hj hj0 hi0 hs Y =
    probeReservoirCross P i j s hi hj hj0 hi0 hs Y ≫
      RepeatedOuterPost.coefficientAlg P i j s hj0 hi0 Y
        (P.rpPostDot i (nextSector (true, j) false s) hi0 Y) := by
  rw [RepeatedOuterPost.targetAlg_post, RepeatedOuterPost.coefficientAlg_post]
  have h := congrArg (P.step (true, i) true s trivial).map
    (P.postCrossNe_slideL i j hij (nextSector (true, i) true s) hi hj hj0 hi0 hs Y)
  simp only [Functor.map_comp, Functor.map_smul] at h
  exact scale_slide _ _ _ _ _ h

lemma probe_coeff_slide (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    RepeatedOuterPost.targetAlg P i j s hi hj (hs ▸ Y)
        (c.a i s hi (rest P i j s hj (hs ▸ Y))) ≫
      probeReservoirCross P i j s hi hj hj0 hi0 hs Y =
    probeReservoirCross P i j s hi hj hj0 hi0 hs Y ≫
      RepeatedOuterPost.coefficientAlg P i j s hj0 hi0 Y
        (c.a i (nextSector (true, j) false s) hi0 Y) := by
  let φ := RepeatedOuterPost.targetAlg P i j s hi hj (hs ▸ Y)
  let ψ := RepeatedOuterPost.coefficientAlg P i j s hj0 hi0 Y
  let W := rest P i j s hj (hs ▸ Y)
  have hφ (a b : End (P.rpObj i i s hi W)) : φ (a ≫ b) = φ a ≫ φ b := φ.map_mul b a
  have hψ (a b : End (P.rpObj i i (nextSector (true, j) false s) hi0 Y)) :
      ψ (a ≫ b) = ψ a ≫ ψ b := ψ.map_mul b a
  have hx := probe_pre_slide P i j s hi hj hj0 hi0 hs Y
  have hz := probe_post_slide P i j s hi hj hj0 hi0 hs Y hij
  by_cases hp : D.parity i = 0
  · have ha := congrArg φ (hc.even i hp s hi W).1
    have hb := congrArg ψ (hc.even i hp (nextSector (true, j) false s) hi0 Y).2
    simp only [hφ, map_sub] at ha
    simp only [hψ, map_sub] at hb
    simpa only [one_smul] using signed_inverse_difference_transport
      _ _ _ _ _ _ (probeReservoirCross P i j s hi hj hj0 hi0 hs Y) (1 : k) (one_mul _)
      (hx.trans (one_smul _ _).symm) (hz.trans (one_smul _ _).symm) (ha.trans φ.map_one) (hb.trans ψ.map_one)
  · have hp' := (Supercategory.parity_eq_zero_or_one (D.parity i)).resolve_left hp
    have ha := congrArg φ (hc.odd i hp' s hi W).1
    have hb := congrArg ψ (hc.odd i hp' (nextSector (true, j) false s) hi0 Y).1
    simp only [hφ, map_sub] at ha
    simp only [hψ, map_sub] at hb
    have hd : (P.crossDenom h i (nextSector (true, j) false s) hi0 Y :
        End (P.rpObj i i (nextSector (true, j) false s) hi0 Y)) =
        P.rpPreDot i (nextSector (true, j) false s) hi0 Y ≫
          P.rpPreDot i (nextSector (true, j) false s) hi0 Y -
        P.rpPostDot i (nextSector (true, j) false s) hi0 Y ≫
          P.rpPostDot i (nextSector (true, j) false s) hi0 Y := by
      simp [crossDenom, hp, sub_eq_add_neg, add_comm, pow_two, End.mul_def]
    have hd' := congrArg ψ hd
    simp only [hψ, map_sub] at hd'
    simpa only [one_smul] using signed_odd_coefficient_transport
      _ _ _ _ _ _ (probeReservoirCross P i j s hi hj hj0 hi0 hs Y) (1 : k) (one_mul _)
      (hx.trans (one_smul _ _).symm) (hz.trans (one_smul _ _).symm) ha hb
      (Units.map ψ.toMonoidHom (P.crossDenom h i (nextSector (true, j) false s) hi0 Y)) hd'

private lemma rectangle_slide {C : Type u} [Category C]
    {A M N B T : C} (J : A ≅ M) (K : M ≅ N) (L : B ≅ T)
    (F : A ⟶ B) (f : N ⟶ T) (a : End M) (b : End T)
    (hf : F ≫ L.hom = J.hom ≫ K.hom ≫ f)
    (hc : (J.hom ≫ a ≫ J.inv) ≫ F = F ≫ (L.hom ≫ b ≫ L.inv)) :
    (K.inv ≫ a ≫ K.hom) ≫ f = f ≫ b := by
  have he := congrArg (fun g => K.inv ≫ J.inv ≫ g ≫ L.hom) hc
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id, ← Category.assoc F L.hom, hf] using he

variable (hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
    nextSector (true, i) false (nextSector (true, j) false s))

def reservoirCross :=
  (P.step (true, i) false s hi).map
    ((P.step (true, j) false (nextSector (true, i) false s) hj).map
      (eqToHom (P.probe_obj_sector_transport i hs0 Y))) ≫
    P.postCrossNe i j s hi hj hj0 hi0 hs0
      ((P.step (true, i) true (nextSector (true, i) false
        (nextSector (true, j) false s)) trivial).obj Y)

lemma coeff_slide (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    coefficientAlg P i j s hi hj (hs ▸ Y) (c.a i s hi (rest P i j s hj (hs ▸ Y))) ≫
      reservoirCross P i j s hi hj hj0 hi0 Y hs0 =
    reservoirCross P i j s hi hj hj0 hi0 Y hs0 ≫
      (P.step (true, j) false s hj0).map (c.a i (nextSector (true, j) false s) hi0 Y) := by
  have hf := eq_of_heq (P.postCrossNe_mixedJ_pair_heq i i j s hi hj hj0 hi0 hs0 hs Y)
  have he := probe_coeff_slide P i j s hi hj hj0 hi0 hs Y c hc h hij
  exact rectangle_slide
    (P.mixedJ i i s hi (rest P i j s hj (hs ▸ Y)))
    (rightIso P i j s hi hj (hs ▸ Y))
    (RepeatedOuterPost.comparison P i j s hj0 hi0 Y)
    (probeReservoirCross P i j s hi hj hj0 hi0 hs Y)
    (reservoirCross P i j s hi hj hj0 hi0 Y hs0)
    (c.a i s hi (rest P i j s hj (hs ▸ Y)))
    ((P.step (true, j) false s hj0).map (c.a i (nextSector (true, j) false s) hi0 Y)) hf he
private lemma rectangle_slide_back {C : Type u} [Category C]
    {A M N B T : C} (J : A ≅ M) (K : M ≅ N) (L : B ≅ T)
    (F : B ⟶ A) (f : T ⟶ N) (a : End M) (b : End T)
    (hf : F ≫ J.hom ≫ K.hom = L.hom ≫ f)
    (hc : (L.hom ≫ b ≫ L.inv) ≫ F = F ≫ (J.hom ≫ a ≫ J.inv)) :
    b ≫ f = f ≫ (K.inv ≫ a ≫ K.hom) := by
  have hF : F = L.hom ≫ f ≫ K.inv ≫ J.inv := by
    have hh := congrArg (fun g => g ≫ K.inv ≫ J.inv) hf
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using hh
  rw [hF] at hc
  have he := congrArg (fun g => L.inv ≫ g ≫ J.hom ≫ K.hom) hc
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using he

variable (Z : P.H (nextSector (true, j) false
    (nextSector (true, i) false (nextSector (true, i) true s))))

def reservoirBack :=
  (P.step (true, j) false s hj0).map
    ((P.step (true, i) false (nextSector (true, j) false s) hi0).map
      (eqToHom (P.probe_obj_sector_transport i hs0.symm Z))) ≫
    P.postCrossNe j i s hj0 hi0 hi hj hs0.symm
      ((P.step (true, i) true (nextSector (true, j) false
        (nextSector (true, i) false s)) trivial).obj Z)

lemma coeff_slide_back (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    (P.step (true, j) false s hj0).map
        (c.a i (nextSector (true, j) false s) hi0 (hs.symm ▸ Z)) ≫
      reservoirBack P i j s hi hj hj0 hi0 hs0 Z =
    reservoirBack P i j s hi hj hj0 hi0 hs0 Z ≫
      coefficientAlg P i j s hi hj Z (c.a i s hi (rest P i j s hj Z)) := by
  have hf := eq_of_heq (P.postCrossNe_mixedJ_pair_heq i j i s hj0 hi0 hi hj hs0.symm hs.symm Z)
  have he := RepeatedOuterPost.coeff_slide P i j s hj0 hi0 hi hj hs.symm Z c hc h hij
  exact rectangle_slide_back
    (P.mixedJ i i s hi (rest P i j s hj Z))
    (rightIso P i j s hi hj Z)
    (RepeatedOuterPost.comparison P i j s hj0 hi0 (hs.symm ▸ Z))
    (RepeatedOuterPost.reservoirCross P i j s hj0 hi0 hi hj hs.symm Z)
    _ (c.a i s hi (rest P i j s hj Z)) _
    (by simpa only [RepeatedOuterPost.comparison, Iso.trans_hom, reservoirBack,
      RepeatedOuterPost.firstIso, distinctReservoirFirstIso, rightIso,
      Functor.mapIso_hom, RepeatedOuterPost.reservoirCross, Category.assoc] using hf) he

end RepeatedOuterPre
end OddMath.QuiverHecke.SwappedAssembly
