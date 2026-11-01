/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPostRoutes

/-! The full repeated-outer 100 diagonal CrossBraid field with both original dot-power sums. -/
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

lemma coeff_comm (c : P.CrossCoeff Sc) (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (f : End (obj P i j s hj0 hi0 Z))
    (hx : outerDot P i j s hj0 hi0 Z ≫ f = f ≫ outerDot P i j s hj0 hi0 Z)
    (hz : innerDot P i j s hj0 hi0 Z ≫ f = f ≫ innerDot P i j s hj0 hi0 Z) :
    coefficientAlg P i j s hj0 hi0 Z (c.a i (nextSector (true, j) false s) hi0 Z) ≫ f =
      f ≫ coefficientAlg P i j s hj0 hi0 Z (c.a i (nextSector (true, j) false s) hi0 Z) := by
  let φ := coefficientAlg P i j s hj0 hi0 Z
  have hφ (a b : End (P.rpObj i i (nextSector (true, j) false s) hi0 Z)) :
      φ (a ≫ b) = φ a ≫ φ b := φ.map_mul b a
  have hx' : φ (P.rpPreDot i (nextSector (true, j) false s) hi0 Z) ≫ f =
      (1 : k) • (f ≫ φ (P.rpPreDot i (nextSector (true, j) false s) hi0 Z)) := by
    rw [one_smul, show φ _ = _ from coefficientAlg_pre P i j s hj0 hi0 Z,
      Linear.smul_comp, Linear.comp_smul, hx]
  have hz' : φ (P.rpPostDot i (nextSector (true, j) false s) hi0 Z) ≫ f =
      (1 : k) • (f ≫ φ (P.rpPostDot i (nextSector (true, j) false s) hi0 Z)) := by
    rw [one_smul, show φ _ = _ from coefficientAlg_post P i j s hj0 hi0 Z,
      Linear.smul_comp, Linear.comp_smul, hz]
  by_cases hp : D.parity i = 0
  · have ha := congrArg φ (hc.even i hp (nextSector (true, j) false s) hi0 Z).1
    have hb := congrArg φ (hc.even i hp (nextSector (true, j) false s) hi0 Z).2
    simp only [hφ, map_sub] at ha hb
    simpa only [one_smul] using signed_inverse_difference_transport _ _ _ _ _ _ f (1 : k)
      (one_mul _) hx' hz' (ha.trans φ.map_one) (hb.trans φ.map_one)
  · have hp' := (Supercategory.parity_eq_zero_or_one (D.parity i)).resolve_left hp
    have ha := congrArg φ (hc.odd i hp' (nextSector (true, j) false s) hi0 Z).1
    simp only [hφ, map_sub] at ha
    have hd : (P.crossDenom h i (nextSector (true, j) false s) hi0 Z :
        End (P.rpObj i i (nextSector (true, j) false s) hi0 Z)) =
      P.rpPreDot i (nextSector (true, j) false s) hi0 Z ≫
        P.rpPreDot i (nextSector (true, j) false s) hi0 Z -
      P.rpPostDot i (nextSector (true, j) false s) hi0 Z ≫
        P.rpPostDot i (nextSector (true, j) false s) hi0 Z := by
      simp [crossDenom, hp, sub_eq_add_neg, add_comm, pow_two, End.mul_def]
    have hd' := congrArg φ hd
    simp only [hφ, map_sub] at hd'
    simpa only [one_smul] using signed_odd_coefficient_transport _ _ _ _ _ _ f (1 : k)
      (one_mul _) hx' hz' ha ha
      (Units.map φ.toMonoidHom (P.crossDenom h i (nextSector (true, j) false s) hi0 Z)) hd'

lemma q_comm (c : P.CrossCoeff Sc) (hc : c.IsInverse) (h : P.CrossCoeffInputs) :
    let C := coefficientAlg P i j s hj0 hi0 Z (c.a i (nextSector (true, j) false s) hi0 Z)
    let x := outerDot P i j s hj0 hi0 Z
    let y := middleDot P i j s hj0 hi0 Z
    let z := innerDot P i j s hj0 hi0 Z
    (C ≫ qExpr Sc x y i j = qExpr Sc x y i j ≫ C) ∧
      (C ≫ qExpr Sc z y i j = qExpr Sc z y i j ≫ C) := by
  dsimp only
  have hxy := (P.distinctReservoir_dots_probe i j i s hj0 hi0 Z).1
  have hxz := dots_xz P i j s hj0 hi0 Z
  have hzy := dots_zy P i j s hj0 hi0 Z
  have hxy' := congrArg (fun f => zsign k (D.parity i * D.parity j) • f) hxy
  have hzy' := congrArg (fun f => zsign k (D.parity i * D.parity j) • f) hzy
  simp only [smul_smul, ProbeReservoir.zsign_mul_self', one_smul] at hxy' hzy'
  have he (n : ℕ) (hn : (n : ZMod 2) * D.parity j = 0) :
      zsign k (D.parity i * D.parity j) ^ n = 1 := by
    rw [mul_comm (D.parity i)]
    exact zsign_pow_of_mul_eq_zero _ _ n hn
  have hq (n : ℕ) (hn : (n : ZMod 2) * D.parity i = 0) :
      zsign k (D.parity i) ^ n = 1 := by
    simpa only [mul_one] using zsign_pow_of_mul_eq_zero (k := k) (D.parity i) 1 n hn
  have hzx : innerDot P i j s hj0 hi0 Z ≫ outerDot P i j s hj0 hi0 Z =
      zsign k (D.parity i) •
        (outerDot P i j s hj0 hi0 Z ≫ innerDot P i j s hj0 hi0 Z) := hxz
  have hzx' := congrArg (fun f => zsign k (D.parity i) • f) hzx
  simp only [smul_smul, ProbeReservoir.zsign_mul_self', one_smul] at hzx'
  constructor
  · apply coeff_comm P i j s hj0 hi0 Z c hc h
    · exact comp_qExpr (Sc := Sc) _ _ _ _ _ i j 1 (zsign k (D.parity i * D.parity j))
        (one_smul _ _).symm hxy'.symm (fun _ _ => one_pow _) he
    · exact comp_qExpr (Sc := Sc) _ _ _ _ _ i j (zsign k (D.parity i))
        (zsign k (D.parity i * D.parity j)) hzx hzy'.symm hq he
  · apply coeff_comm P i j s hj0 hi0 Z c hc h
    · exact comp_qExpr (Sc := Sc) _ _ _ _ _ i j (zsign k (D.parity i))
        (zsign k (D.parity i * D.parity j)) hzx'.symm hxy'.symm hq he
    · exact comp_qExpr (Sc := Sc) _ _ _ _ _ i j 1 (zsign k (D.parity i * D.parity j))
        (one_smul _ _).symm hzy'.symm (fun _ _ => one_pow _) he

lemma dotY (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    dotEntry (P.swappedGens c L) ν [up i] j [up i]
      (SPath.three true false false trivial hj0 hi0 rfl) Z =
      middleDot P i j s hj0 hi0 Z := by
  unfold dotEntry
  refine eq_of_heq ((heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i] (SKM.Shape.dot j) [up i]) (.cons _ true s trivial (.nil _))
    (.cons _ false _ hj0 (.nil _)) (.cons _ false _ hj0 (.nil _))
    (.cons _ false _ hi0 (.nil _)) _ _ rfl rfl Z)).trans ?_)
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (P.step (true, i) true s trivial).map
    (P.dotImage_reservoir j (SKM.wt D ν [up i]) (nextSector (true, i) true s)
      hj0 hj0 (rest P i j s hi0 Z)))

lemma full_diag (ν : X)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hs : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) =
      nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)))
    (Y : P.H (nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s))))
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true false false trivial hj0 hi0 hs
    braidLeft (P.swappedGens c L) i j i ν n n Y -
      braidRight (P.swappedGens c L) i j i ν n n Y =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n Y) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n Y)
              (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n Y) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] n Y) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n Y) (b - 1 - a)) := by
  have hr := braidRight_coefficient P i j s hj0 hi0 hi hj hs Y ν c L hc h hij
  generalize ht : nextSector (true, j) false (nextSector (true, i) false
    (nextSector (true, i) true s)) = t at Y hs hr ⊢
  subst hs
  dsimp only
  rw [braidLeft_coefficient P i j s hj0 hi0 Y ν c L hij, eq_of_heq hr]
  simp only [dotX P i j s hj0 hi0 Y ν c L, dotY P i j s hj0 hi0 Y ν c L,
    dotZ P i j s hj0 hi0 Y ν c L, compPow_eq_pow, ← End.mul_def]
  have hswap := qExpr_swap Sc (innerDot P i j s hj0 hi0 Y)
    (middleDot P i j s hj0 hi0 Y) i j (zsign k (D.parity i * D.parity j))
    (dots_zy P i j s hj0 hi0 Y) (fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn)
  rw [← hswap]
  have hcomm := q_comm P i j s hj0 hi0 Y c hc h
  have hQ : P.mixedQ i j s hj0 (rest P i j s hi0 Y) =
      qExpr Sc (outerDot P i j s hj0 hi0 Y) (middleDot P i j s hj0 hi0 Y) i j := rfl
  rw [hQ]
  simp only [← End.mul_def] at hcomm
  rw [hcomm.1, hcomm.2]
  have hn :
      -(qExpr Sc (outerDot P i j s hj0 hi0 Y) (middleDot P i j s hj0 hi0 Y) i j ≫
        coefficientAlg P i j s hj0 hi0 Y (c.a i (nextSector (true, j) false s) hi0 Y)) -
      -(qExpr Sc (innerDot P i j s hj0 hi0 Y) (middleDot P i j s hj0 hi0 Y) i j ≫
        coefficientAlg P i j s hj0 hi0 Y (c.a i (nextSector (true, j) false s) hi0 Y)) =
      zsign k (D.parity i * D.parity j) •
        (normalizedCoeff P i j s hj0 hi0 Y c *
          (qExpr Sc (outerDot P i j s hj0 hi0 Y) (middleDot P i j s hj0 hi0 Y) i j -
            qExpr Sc (innerDot P i j s hj0 hi0 Y) (middleDot P i j s hj0 hi0 Y) i j)) := by
    simp only [← End.mul_def]
    simp only [normalizedCoeff, mul_sub, smul_sub, smul_mul_assoc, smul_smul, mul_neg,
      ProbeReservoir.zsign_mul_self', neg_one_smul]
  exact hn.trans (q_correction P i j s hj0 hi0 Y c hc)


lemma full_diag_transport (ν : X)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (Y : P.H t)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true false false trivial hj0 hi0 e
    braidLeft (P.swappedGens c L) i j i ν n n Y -
      braidRight (P.swappedGens c L) i j i ν n n Y =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n Y) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n Y)
              (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n Y) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] n Y) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n Y) (b - 1 - a)) := by
  subst e'
  exact full_diag P i j s hj0 hi0 ν hi hj e Y c L hc h hij

lemma full_diag_path (ν : X)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (Y : P.H t) (p : SPath (wd D ν [up i, up j, up i]) s t)
    (hp : p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
      (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      true false false trivial hj0 hi0 e)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν p p Y -
      braidRight (P.swappedGens c L) i j i ν p p Y =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Y) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Y)
              (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Y) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] p Y) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Y) (b - 1 - a)) := by
  subst p
  exact full_diag_transport P i j s hj0 hi0 ν hi hj e e' Y c L hc h hij

end RepeatedOuterPost
end OddMath.QuiverHecke.SwappedAssembly
