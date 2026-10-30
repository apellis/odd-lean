/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPreTransport

/-! The Ri Rj Pi diagonal correction in Brundan–Ellis (1.9). -/
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
  (hs0 : nextSector (true, j) false (nextSector (true, i) false s) =
    nextSector (true, i) false (nextSector (true, j) false s))

lemma left_first (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three false false true hi hj trivial hs)
      (SPath.three false false true hj0 hi0 trivial rfl) Y)
      (reservoirCross P i j s hi hj hj0 hi0 Y hs0) := by
  let pg : SPath (wd D (SKM.wt D ν [up i]) [up i, up j]) s
      (nextSector (true, i) false (nextSector (true, j) false s)) :=
    SPath.two false false hi hj hs0
  let qg : SPath (wd D (SKM.wt D ν [up i]) [up j, up i]) s
      (nextSector (true, i) false (nextSector (true, j) false s)) :=
    SPath.two false false hj0 hi0 rfl
  let pv : SPath (wd D ν [up i])
      (nextSector (true, i) false (nextSector (true, j) false s))
      (nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s))) :=
    .cons _ true _ trivial (.nil _)
  have hp : (SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false false true hi hj trivial hs) = pg.append pv := by
    rcases adjacentPost_iji_cases hij hi hj hj0 hi0 hs rfl (pg.append pv) with h | h
    · exact h.symm
    · cases h
  have hq : (SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false false true hj0 hi0 trivial rfl) = qg.append pv := rfl
  rw [hp, hq]
  erw [crossEntry_left]
  have hed : HEq
      (crossEntry (P.swappedGens c L) ν [] i j [up i] (pg.append pv) (qg.append pv) Y)
      (P.postCrossNe i j s hi hj hj0 hi0 hs0 ((P.step (true, i) true _ trivial).obj Y)) := by
    erw [crossEntry_left]
    refine (sandwich_heq _ _ _).trans ?_
    dsimp only [swappedGens]
    erw [P.crossImage_ne c hij]
    exact P.twoTwo_two_heq
      ⟨up i, SKM.wt D (SKM.wt D ν [up i]) [up j]⟩ ⟨up j, SKM.wt D ν [up i]⟩
      ⟨up j, SKM.wt D (SKM.wt D ν [up i]) [up i]⟩ ⟨up i, SKM.wt D ν [up i]⟩
      (P.crossNeEntry i j _ _ _ _) (t := s) false false false false
      hi hj hj0 hi0 hs0 rfl rfl _ _ HEq.rfl
  erw [crossEntry_left] at hed
  refine hed.trans ?_
  symm
  dsimp only [reservoirCross]
  rw [eqToHom_map, eqToHom_map]
  simpa only [eqToHom_refl, Category.comp_id] using sandwich_heq
    (congrArg (fun V => (P.step (true, i) false s hi).obj
      ((P.step (true, j) false (nextSector (true, i) false s) hj).obj V))
      (P.probe_obj_sector_transport i hs0 Y)) rfl
    (P.postCrossNe i j s hi hj hj0 hi0 hs0 ((P.step (true, i) true _ trivial).obj Y))

lemma left_mid (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three false false true hj0 hi0 trivial rfl)
      (SPath.three false false true hj0 hi0 trivial rfl) Y =
      (P.step (true, j) false s hj0).map (c.a i (nextSector (true, j) false s) hi0 Y) := by
  refine (crossEntry_right (P.swappedGens c L) ν j i i false hj0
    (SPath.two false true hi0 trivial rfl) (SPath.two false true hi0 trivial rfl) Y).trans ?_
  erw [swappedGens_cross_self]
  rfl

def literalCoeff (ν : X) {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (V : P.H t) (c : P.CrossCoeff Sc) :
    End ((P.pathFunctor (SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false false true hi hj trivial e)).obj V) :=
  (conjAlg (k := k) (eqToIso (P.pathFunctor_three_obj
    (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
    (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    false false true hi hj trivial e V)).symm)
    (coefficientAlg P i j s hi hj (e ▸ V) (c.a i s hi (rest P i j s hj (e ▸ V))))

lemma literalCoeff_heq (ν : X) {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (V : P.H t) (c : P.CrossCoeff Sc) :
    HEq (literalCoeff P i j s hi hj ν e V c)
      (coefficientAlg P i j s hi hj (e ▸ V) (c.a i s hi (rest P i j s hj (e ▸ V)))) := by
  subst e
  apply heq_of_eq
  change (𝟙 _ ≫ _ ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

include hs0 in
lemma left_literal_slide (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial hs
    let b : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false false true hj0 hi0 trivial rfl
    crossEntry (P.swappedGens c L) ν [] i j [up i] n b Y ≫
      crossEntry (P.swappedGens c L) ν [up j] i i [] b b Y =
    literalCoeff P i j s hi hj ν hs Y c ≫
      crossEntry (P.swappedGens c L) ν [] i j [up i] n b Y := by
  dsimp only
  rw [left_mid P i j s hj0 hi0 Y ν c L]
  have hn := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
    (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    false false true hi hj trivial hs Y
  have hf := left_first P i j s hi hj hj0 hi0 hs Y hs0 ν c L hij
  have hleft := comp_common_grid_heq hn rfl rfl hf (HEq.rfl (a :=
    (P.step (true, j) false s hj0).map (c.a i (nextSector (true, j) false s) hi0 Y)))
  have hright := comp_common_grid_heq hn hn rfl (literalCoeff_heq P i j s hi hj ν hs Y c) hf
  exact eq_of_heq (hleft.trans ((heq_of_eq (coeff_slide P i j s hi hj hj0 hi0 hs Y hs0 c hc h hij).symm).trans hright.symm))
section Canonical
variable (Z : P.H (nextSector (true, j) false
    (nextSector (true, i) false (nextSector (true, i) true s))))
  (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) =
    nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)))

lemma left_quad (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial rfl
    let b : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false false true hj0 hi0 trivial e
    crossEntry (P.swappedGens c L) ν [] i j [up i] n b Z ≫
      crossEntry (P.swappedGens c L) ν [] j i [up i] b n Z =
    qExpr Sc (outerDot P i j s hi hj Z) (middleDot P i j s hi hj Z) i j := by
  classical
  dsimp only
  have e0 : nextSector (true, i) false (nextSector (true, j) false s) =
      nextSector (true, j) false (nextSector (true, i) false s) := by
    have he2 := congrArg (fun t : Sector I => t.2) e
    exact Prod.ext rfl he2
  let pg : SPath (wd D (SKM.wt D ν [up i]) [up i, up j]) s
      (nextSector (true, j) false (nextSector (true, i) false s)) := SPath.two false false hi hj rfl
  let qg : SPath (wd D (SKM.wt D ν [up i]) [up j, up i]) s
      (nextSector (true, j) false (nextSector (true, i) false s)) := SPath.two false false hj0 hi0 e0
  let pv : SPath (wd D ν [up i])
      (nextSector (true, j) false (nextSector (true, i) false s))
      (nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s))) :=
    .cons _ true _ trivial (.nil _)
  have hb : (SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false false true hj0 hi0 trivial e) = qg.append pv := by
    rcases adjacentPost_jii_cases hij hj0 hi0 e e (qg.append pv) with h | h
    · exact h.symm
    · cases h
  have hn : (SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false false true hi hj trivial rfl) = pg.append pv := rfl
  let V := (P.pathFunctor pv).obj Z
  have hsum : crossCross (P.swappedGens c L) i j (SKM.wt D ν [up i]) pg pg V =
      (P.swappedGens c L).cross i j (SKM.wt D ν [up i]) pg qg V ≫
        (P.swappedGens c L).cross j i (SKM.wt D ν [up i]) qg pg V := by
    have : Subsingleton (SPath (wd D (SKM.wt D ν [up i]) [up j, up i]) s
        (nextSector (true, j) false (nextSector (true, i) false s))) := ⟨path_eq_of_ne hij.symm⟩
    let := Fintype.ofFinite (SPath (wd D (SKM.wt D ν [up i]) [up j, up i]) s
      (nextSector (true, j) false (nextSector (true, i) false s)))
    unfold crossCross
    exact Fintype.sum_subsingleton _ qg
  change crossEntry (P.swappedGens c L) ν [] i j [up i] (pg.append pv) _ Z ≫
    crossEntry (P.swappedGens c L) ν [] j i [up i] _ (pg.append pv) Z = _
  rw [hb, crossEntry_left, crossEntry_left]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [← hsum, P.swappedGens_crossCrossNe c L i j (SKM.wt D ν [up i]) hij pg V]
  have hx := eq_of_heq (P.leftDot_two_reservoir_heq c L i j (SKM.wt D ν [up i]) hi false hj rfl V V HEq.rfl)
  have hy := eq_of_heq (P.rightDot_two_reservoir_heq c L i j (SKM.wt D ν [up i]) false hi hj rfl V V HEq.rfl)
  rw [hx, hy]
  rfl
lemma left_mid_heq (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    HEq (crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three false false true hj0 hi0 trivial e)
      (SPath.three false false true hj0 hi0 trivial e) Z)
      ((P.step (true, j) false s hj0).map (c.a i (nextSector (true, j) false s) hi0 (e ▸ Z))) := by
  generalize ht : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t at Z e
  subst e
  exact heq_of_eq (left_mid P i j s hj0 hi0 Z ν c L)

lemma left_last_slide (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial rfl
    let b : SPath (wd D ν [up j, up i, up i]) s _ := SPath.three false false true hj0 hi0 trivial e
    crossEntry (P.swappedGens c L) ν [up j] i i [] b b Z ≫
      crossEntry (P.swappedGens c L) ν [] j i [up i] b n Z =
    crossEntry (P.swappedGens c L) ν [] j i [up i] b n Z ≫
      coefficientAlg P i j s hi hj Z (c.a i s hi (rest P i j s hj Z)) := by
  dsimp only
  have e0 : nextSector (true, i) false (nextSector (true, j) false s) =
      nextSector (true, j) false (nextSector (true, i) false s) := by
    have he2 := congrArg (fun t : Sector I => t.2) e
    exact Prod.ext rfl he2
  have hf := P.repeatedReservoir_left ν i j s hj0 hi0 hi hj e0 e c L Z hij
  have hb := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    false false true hj0 hi0 trivial e Z
  have hd := left_mid_heq P i j s hj0 hi0 Z e ν c L
  have hl := comp_common_grid_heq hb hb rfl hd hf
  have hr := comp_common_grid_heq hb rfl rfl hf
    (HEq.rfl (a := coefficientAlg P i j s hi hj Z (c.a i s hi (rest P i j s hj Z))))
  exact eq_of_heq (hl.trans ((heq_of_eq (coeff_slide_back P i j s hi hj hj0 hi0 e.symm e0.symm Z c hc h hij)).trans hr.symm))

include hj0 hi0 e in
lemma braidLeft_coefficient (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν
      (SPath.three false false true hi hj trivial rfl)
      (SPath.three false false true hi hj trivial rfl) Z =
    qExpr Sc (outerDot P i j s hi hj Z) (middleDot P i j s hi hj Z) i j ≫
      coefficientAlg P i j s hi hj Z (c.a i s hi (rest P i j s hj Z)) := by
  rw [braidLeft_route P i j s hi hj Z hj0 hi0 e ν _ hij, Category.assoc,
    left_last_slide P i j s hi hj hj0 hi0 Z e ν c L hc h hij,
    ← Category.assoc, left_quad P i j s hi hj hj0 hi0 Z e ν c L hij]

lemma right_conjQ :
    (rightIso P i j s hi hj Z).inv ≫
        (P.step (true, i) false s hi).map (P.mixedQ i j (nextSector (true, i) false s) hj Z) ≫
      (rightIso P i j s hi hj Z).hom =
    qExpr Sc (innerDot P i j s hi hj Z) (middleDot P i j s hi hj Z) i j := by
  have hQ := congrArg (P.step (true, i) false s hi).map
    (P.mixedJ_inv_mixedQ_hom i j (nextSector (true, i) false s) hj Z)
  simp only [Functor.map_comp] at hQ
  have he : (rightIso P i j s hi hj Z).inv ≫
        (P.step (true, i) false s hi).map (P.mixedQ i j (nextSector (true, i) false s) hj Z) ≫
      (rightIso P i j s hi hj Z).hom =
      qExpr Sc (middleDot P i j s hi hj Z) (innerDot P i j s hi hj Z) j i :=
        hQ.trans (qExpr_map Sc (functorAlg (k := k) (P.step (true, i) false s hi) _) _ _ j i)
  rw [he]
  symm
  exact qExpr_swap Sc _ _ i j (zsign k (D.parity i * D.parity j))
    (dots_zy P i j s hi hj Z) (fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn)

lemma braidRight_q (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    braidRight (P.swappedGens c L) i j i ν
      (SPath.three false false true hi hj trivial rfl)
      (SPath.three false false true hi hj trivial rfl) Z =
    qExpr Sc (innerDot P i j s hi hj Z) (middleDot P i j s hi hj Z) i j ≫
      coefficientAlg P i j s hi hj Z (c.a i s hi (rest P i j s hj Z)) := by
  rw [braidRight_coefficient P i j s hi hj Z ν c L hij, ← right_conjQ P i j s hi hj Z]
  change (_ ≫ _ ≫ _) ≫ _ = (_ ≫ _ ≫ _) ≫ (_ ≫ _ ≫ _)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

include hj0 hi0 e in
lemma correction (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν
      (SPath.three false false true hi hj trivial rfl)
      (SPath.three false false true hi hj trivial rfl) Z -
    braidRight (P.swappedGens c L) i j i ν
      (SPath.three false false true hi hj trivial rfl)
      (SPath.three false false true hi hj trivial rfl) Z =
    zsign k (D.parity i * D.parity j) •
      (normalizedCoeff P i j s hi hj Z c *
        (qExpr Sc (outerDot P i j s hi hj Z) (middleDot P i j s hi hj Z) i j -
          qExpr Sc (innerDot P i j s hi hj Z) (middleDot P i j s hi hj Z) i j)) := by
  rw [braidLeft_coefficient P i j s hi hj hj0 hi0 Z e ν c L hc h hij,
    braidRight_q P i j s hi hj Z ν c L hij]
  simp only [← End.mul_def]
  simp only [normalizedCoeff, smul_mul_assoc, smul_sub, smul_smul,
    ProbeReservoir.zsign_mul_self', one_smul, mul_sub]
include hj0 hi0 e in
/-- The complete literal 001 diagonal field, including both signed finite sums. -/
lemma full_diag (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial rfl
    braidLeft (P.swappedGens c L) i j i ν n n Z -
      braidRight (P.swappedGens c L) i j i ν n n Z =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n Z)
              (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] n Z) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n Z) (b - 1 - a)) := by
  dsimp only
  rw [correction P i j s hi hj hj0 hi0 Z e ν c L hc h hij]
  simp only [dotX P i j s hi hj Z ν c L, dotY P i j s hi hj Z ν c L,
    dotZ P i j s hi hj Z ν c L, compPow_eq_pow, ← End.mul_def]
  exact q_correction P i j s hi hj Z c hc

end Canonical

include hj0 hi0 in
lemma full_diag_transport (ν : X) {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ := SPath.three false false true hi hj trivial e
    braidLeft (P.swappedGens c L) i j i ν n n Z -
      braidRight (P.swappedGens c L) i j i ν n n Z =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n Z)
              (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] n Z) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n Z) (b - 1 - a)) := by
  subst e
  exact full_diag P i j s hi hj hj0 hi0 Z e' ν c L hc h hij

include hj0 hi0 in
lemma full_diag_path (ν : X) {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (p : SPath (wd D ν [up i, up j, up i]) s t)
    (hp : p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false false true hi hj trivial e)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν p p Z -
      braidRight (P.swappedGens c L) i j i ν p p Z =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z)
              (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] p Z) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z) (b - 1 - a)) := by
  subst p
  exact full_diag_transport P i j s hi hj hj0 hi0 ν e e' Z c L hc h hij


end RepeatedOuterPre
end OddMath.QuiverHecke.SwappedAssembly
