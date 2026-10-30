/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterSeparatedCoordinates

/-! # Separated repeated-outer diagonal routes

The full literal `Pᵢ Pⱼ Rᵢ` diagonal correction is proved for the supplied
coefficient-derived swapped generators. Both finite crossing sums are evaluated,
the terminal-cast probe quadratic is identified, and the separated coefficient
commutes with inner Q by mapped inverse identities and the denominator unit.
All three literal dotEntry powers and both signed coefficient sums are retained.
This supplies one diagonal component, not yet the full CrossBraid producer.
-/
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
namespace ProbeReservoir
private lemma route {C : Type u} [Category C] [Preadditive C]
    {A B V : C} (f : A ⟶ B) (f' : A ⟶ V) (g : B ⟶ B)
    (h : V ⟶ B) (j : B ⟶ V) (l : V ⟶ V) (r : B ⟶ A) (r' : V ⟶ A)
    (hf : f = 0) (hr : r = 0) :
    (f ≫ g + f' ≫ h) ≫ r + (f ≫ j + f' ≫ l) ≫ r' = (f' ≫ l) ≫ r' := by
  rw [hf, hr]
  simp only [Limits.zero_comp, Limits.comp_zero, zero_add]

variable (P : ProbeReservoir k B D Sc) (ν : X) (i j : I) (s : Sector I)
  (hR : StepValid (true, i) false s)
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

lemma separatedOuter_braidRight_route (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
    let b : SPath (wd D ν [up i, up i, up j]) s _ :=
      SPath.three true false true trivial hR trivial rfl
    braidRight G i j i ν n n Z =
      (crossEntry G ν [up i] j i [] n b Z ≫ crossEntry G ν [] i i [up j] b b Z) ≫
        crossEntry G ν [up i] i j [] b n Z := by
  classical
  dsimp only
  have hf := crossEntry_right_eq_zero G ν i j i true false (by decide)
    trivial hR (SPath.two true false trivial hR rfl)
    (SPath.two true true trivial trivial rfl) Z
  have hr := crossEntry_right_eq_zero G ν i i j false true Bool.false_ne_true
    hR trivial (SPath.two true true trivial trivial rfl)
    (SPath.two true false trivial hR rfl) Z
  unfold braidRight
  erw [adjacentMixed_iij_sum hij hR rfl rfl]
  erw [adjacentMixed_iij_sum hij hR rfl rfl, adjacentMixed_iij_sum hij hR rfl rfl]
  exact route _ _ _ _ _ _ _ _ hf hr

private lemma comparison_conj {C : Type u} [Category C] [Preadditive C]
    {A B V : C} (K : A ≅ B) (H : B ≅ V) (a : End V) (q : End A) :
    (K.hom ≫ (-(H.hom ≫ a ≫ H.inv))) ≫ (K.inv ≫ q) =
      -((K.hom ≫ H.hom ≫ a ≫ H.inv ≫ K.inv) ≫ q) := by
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]

/-- The complete finite right diagonal sum, with its coefficient and Q
identified from the supplied swapped generators. -/
lemma separatedOuter_braidRight (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) :
    braidRight (P.swappedGens c L) i j i ν
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true true false trivial trivial hR rfl) Z =
      -(P.repeatedOuterMixedSeparatedCoeff i j s hR Z c ≫
        (P.step (true, i) true s trivial).map
          (P.mixedQ j i (nextSector (true, i) true s) hR Z)) := by
  rw [P.separatedOuter_braidRight_route ν i j s hR Z (P.swappedGens c L) hij]
  have hmid := eq_of_heq (P.adjacentReverse_target_conj_heq ν i j s c L hR Z)
  have hfirst := P.adjacentReverse_inner ν i j s c L hR Z hij
  have hlast := (P.repeatedOuter_forward_inner i j s hR Z ν c L hij).trans
    ((P.step (true, i) true s trivial).map_comp _ _)
  exact (congrArg₂ (fun f g => f ≫ g)
    (congrArg₂ (fun f g => f ≫ g) hfirst hmid) hlast).trans
    (comparison_conj (P.distinctProbeFirstIso i j i s hR Z)
      (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)) _ _)
section Left
variable
  (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
    nextSector (true, j) true (nextSector (true, i) true s))
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))

lemma separatedOuter_braidLeft_route (G : P.Generators) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
    let b : SPath (wd D ν [up j, up i, up i]) s _ :=
      SPath.three true true false trivial trivial hR hs
    braidLeft G i j i ν n n Z =
      (crossEntry G ν [] i j [up i] n b Z ≫ crossEntry G ν [up j] i i [] b b Z) ≫
        crossEntry G ν [] j i [up i] b n Z := by
  classical
  dsimp only
  have hf := P.crossEntry_left_three_zero G ν i j i true true true false false true
    (by decide) trivial trivial trivial hR hR trivial rfl hs Z
  have hr := P.crossEntry_left_three_zero G ν j i i true false true true true false
    (by decide) trivial hR trivial trivial trivial hR hs rfl Z
  unfold braidLeft
  erw [adjacentMixed_jii_sum hij hR hs hs]
  erw [adjacentMixed_jii_sum hij hR hs hs, adjacentMixed_jii_sum hij hR hs hs]
  exact route _ _ _ _ _ _ _ _ hf hr

private lemma map_neg_triple {C C' : Type u} [Category C] [Preadditive C]
    [Category C'] [Preadditive C'] (F : C ⥤ C') [F.Additive]
    {A B V W : C} (f : A ⟶ B) (g : B ⟶ V) (h : V ⟶ W) :
    F.map (-(f ≫ g ≫ h)) = -(F.map f ≫ F.map g ≫ F.map h) := by
  simp only [Functor.map_neg, Functor.map_comp]

private lemma neg_assoc {C : Type u} [Category C] [Preadditive C]
    {A B V W : C} (f : A ⟶ B) (g : B ⟶ V) (h : V ⟶ W) :
    f ≫ g ≫ (-h) = -((f ≫ g) ≫ h) := by
  simp only [Preadditive.comp_neg, Category.assoc]

private lemma neg_slide {C : Type u} [Category C] [Preadditive C]
    {A B : C} (a : End A) (b : End B) (f : A ⟶ B)
    (h : a ≫ f = f ≫ b) : (-a) ≫ f = f ≫ (-b) := by
  rw [Preadditive.neg_comp, Preadditive.comp_neg, h]

include hs₀ in
lemma separatedOuter_literal_coeff_slide (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
    let b : SPath (wd D ν [up j, up i, up i]) s _ :=
      SPath.three true true false trivial trivial hR hs
    crossEntry (P.swappedGens c L) ν [up j] i i [] b b Z ≫
        crossEntry (P.swappedGens c L) ν [] j i [up i] b n Z =
      crossEntry (P.swappedGens c L) ν [] j i [up i] b n Z ≫
        (-P.repeatedOuterMixedSeparatedCoeff i j s hR Z c) := by
  dsimp only
  have hB := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true true false trivial trivial hR hs Z
  have hf := P.adjacentReverse_probe_heq ν i j s c L hR hs₀ hs Z hij
  have ha := P.adjacentReverse_source_conj_heq ν i j s c L hR hs Z
  have ha' : HEq (crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true true false trivial trivial hR hs)
      (SPath.three true true false trivial trivial hR hs) Z)
      (-P.repeatedOuterMixedAdjacentCoeff i j s hR hs Z c) := by
    refine ha.trans (heq_of_eq ?_)
    have : (P.step (true, j) true s trivial).Additive := P.step_additive _ _ _ _
    exact map_neg_triple (P.step (true, j) true s trivial) _ _ _
  have hleft := comp_common_grid_heq hB hB rfl ha' hf
  have hright := comp_common_grid_heq hB rfl rfl hf
    (HEq.rfl : HEq (-P.repeatedOuterMixedSeparatedCoeff i j s hR Z c)
      (-P.repeatedOuterMixedSeparatedCoeff i j s hR Z c))
  exact eq_of_heq (hleft.trans ((heq_of_eq (neg_slide _ _ _
    (P.repeatedOuterMixed_probe_coeff i j s hR hs₀ hs Z c hc h hij))).trans hright.symm))

include hs₀ in
/-- The full left diagonal sum with the coefficient moved through the
literal terminal-cast probe edge. No probe crossing is cancelled. -/
lemma separatedOuter_braidLeft (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
    let b : SPath (wd D ν [up j, up i, up i]) s _ :=
      SPath.three true true false trivial trivial hR hs
    braidLeft (P.swappedGens c L) i j i ν n n Z =
      -((crossEntry (P.swappedGens c L) ν [] i j [up i] n b Z ≫
        crossEntry (P.swappedGens c L) ν [] j i [up i] b n Z) ≫
        P.repeatedOuterMixedSeparatedCoeff i j s hR Z c) := by
  dsimp only
  rw [P.separatedOuter_braidLeft_route ν i j s hR Z hs (P.swappedGens c L) hij]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true true false trivial trivial hR hs) Z ≫ f)
      (P.separatedOuter_literal_coeff_slide ν i j s hR Z hs₀ hs c L hc h hij)).trans
        (neg_assoc _ _ _))
include hs₀ in
/-- The literal terminal-cast probe pair is exactly the native outer Q. -/
lemma separatedOuter_literal_probe_quad (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
    let b : SPath (wd D ν [up j, up i, up i]) s _ :=
      SPath.three true true false trivial trivial hR hs
    crossEntry (P.swappedGens c L) ν [] i j [up i] n b Z ≫
      crossEntry (P.swappedGens c L) ν [] j i [up i] b n Z =
      qExpr Sc (P.distinctProbeOuterDot i j i s hR Z)
        (P.distinctProbeInnerDot i j i s hR Z) i j := by
  classical
  dsimp only
  let pg : SPath (wd D (SKM.wt D ν [up i]) [up i, up j]) s
      (nextSector (true, j) true (nextSector (true, i) true s)) :=
    SPath.two true true trivial trivial rfl
  let qg : SPath (wd D (SKM.wt D ν [up i]) [up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true s)) :=
    SPath.two true true trivial trivial hs₀
  let pv : SPath (wd D ν [up i])
      (nextSector (true, j) true (nextSector (true, i) true s))
      (nextSector (true, i) false (nextSector (true, j) true (nextSector (true, i) true s))) :=
    .cons _ false _ hR (.nil _)
  have hb : SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      true true false trivial trivial hR hs = qg.append pv := by
    rcases adjacentMixed_jii_cases hij hR hs hs (qg.append pv) with h | h
    · cases h
    · exact h.symm
  have hM : (P.pathFunctor (qg.append pv)).obj Z =
      (P.pathFunctor qg).obj ((P.pathFunctor pv).obj Z) := by
    rw [P.pathFunctor_append]; rfl
  have hf := (heq_of_eq (crossEntry_left (P.swappedGens c L) ν i j i pg qg pv Z)).trans
    (sandwich_heq _ _ _)
  have hg := (heq_of_eq (crossEntry_left (P.swappedGens c L) ν j i i qg pg pv Z)).trans
    (sandwich_heq _ _ _)
  have hp := eq_of_heq (comp_common_grid_heq rfl hM rfl hf hg)
  have hquad := P.swappedGens_crossCrossNe c L i j (SKM.wt D ν [up i]) hij pg
    ((P.pathFunctor pv).obj Z)
  have : Subsingleton (SPath (wd D (SKM.wt D ν [up i]) [up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true s))) := ⟨path_eq_of_ne hij.symm⟩
  let : Fintype (SPath (wd D (SKM.wt D ν [up i]) [up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true s))) := Fintype.ofFinite _
  unfold crossCross at hquad
  have hsum := Fintype.sum_subsingleton (fun m : SPath
    (wd D (SKM.wt D ν [up i]) [up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true s)) =>
    (P.swappedGens c L).cross i j (SKM.wt D ν [up i]) pg m ((P.pathFunctor pv).obj Z) ≫
      (P.swappedGens c L).cross j i (SKM.wt D ν [up i]) m pg ((P.pathFunctor pv).obj Z)) qg
  have hquad := hsum.symm.trans hquad
  have hx := eq_of_heq (P.leftDot_two_probe_heq c L i j (SKM.wt D ν [up i])
    true trivial rfl ((P.pathFunctor pv).obj Z) _ HEq.rfl)
  have hy := eq_of_heq (P.rightDot_two_probe_heq c L i j (SKM.wt D ν [up i])
    true trivial rfl ((P.pathFunctor pv).obj Z) _ HEq.rfl)
  have hfinal := hp.trans (hquad.trans (congrArg₂ (fun x y => qExpr Sc x y i j) hx hy))
  erw [hb]
  exact hfinal
include hs₀ hs in
/-- The full left diagonal matrix entry in the native separated dots. -/
lemma separatedOuter_braidLeft_qExpr (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true true false trivial trivial hR rfl) Z =
      -(qExpr Sc (P.distinctProbeOuterDot i j i s hR Z)
        (P.distinctProbeInnerDot i j i s hR Z) i j ≫
        P.repeatedOuterMixedSeparatedCoeff i j s hR Z c) := by
  exact (P.separatedOuter_braidLeft ν i j s hR Z hs₀ hs c L hc h hij).trans
    (congrArg (fun q => -(q ≫ P.repeatedOuterMixedSeparatedCoeff i j s hR Z c))
      (P.separatedOuter_literal_probe_quad ν i j s hR Z hs₀ hs c L hij))
end Left

lemma separatedOuter_innerQ :
    (P.step (true, i) true s trivial).map
      (P.mixedQ j i (nextSector (true, i) true s) hR Z) =
      qExpr Sc (P.distinctProbeSpectatorDot i j i s hR Z)
        (P.distinctProbeInnerDot i j i s hR Z) i j := by
  exact (P.distinctProbe_map_mixedQ i j i s hR Z).trans
    (qExpr_swap Sc _ _ i j (zsign k (D.parity i * D.parity j))
      (P.separatedOuterDots_zy i j s hR Z)
      (zsign_pow_of_mul_eq_zero (k := k) (D.parity i) (D.parity j))).symm

/-- The full right diagonal matrix entry, with Q written in the native
spectator and inner probe dots in the order required by the correction. -/
lemma separatedOuter_braidRight_qExpr (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) :
    braidRight (P.swappedGens c L) i j i ν
      (SPath.three true true false trivial trivial hR rfl)
      (SPath.three true true false trivial trivial hR rfl) Z =
      -(P.repeatedOuterMixedSeparatedCoeff i j s hR Z c ≫
        qExpr Sc (P.distinctProbeSpectatorDot i j i s hR Z)
          (P.distinctProbeInnerDot i j i s hR Z) i j) := by
  exact (P.separatedOuter_braidRight ν i j s hR Z c L hij).trans
    (congrArg (fun q => -(P.repeatedOuterMixedSeparatedCoeff i j s hR Z c ≫ q))
      (P.separatedOuter_innerQ i j s hR Z))
private lemma signed_reverse {C : Type u} [Category C] [Preadditive C] [Linear k C]
    {V : C} (x y : End V) (ε : k) (hε : ε * ε = 1)
    (h : x ≫ y = ε • (y ≫ x)) : y ≫ x = ε • (x ≫ y) := by
  rw [h, smul_smul, hε, one_smul]

lemma separatedOuterDots_xy :
    P.distinctProbeOuterDot i j i s hR Z ≫ P.distinctProbeInnerDot i j i s hR Z =
      zsign k (D.parity i * D.parity j) •
        (P.distinctProbeInnerDot i j i s hR Z ≫ P.distinctProbeOuterDot i j i s hR Z) := by
  have he := TwoSupercategory.super_interchange (R := k)
    (P.T.dot_mem i (P.muP_preE i s))
    ((P.prPreDot_supernatural j i (nextSector (true, i) true s) hR).mem Z)
  rw [koszulSign_smul_eq_zsign (k := k)] at he
  exact he

lemma separatedOuter_x_innerQ :
    P.distinctProbeOuterDot i j i s hR Z ≫
        qExpr Sc (P.distinctProbeSpectatorDot i j i s hR Z)
          (P.distinctProbeInnerDot i j i s hR Z) i j =
      qExpr Sc (P.distinctProbeSpectatorDot i j i s hR Z)
          (P.distinctProbeInnerDot i j i s hR Z) i j ≫
        P.distinctProbeOuterDot i j i s hR Z := by
  have hxz := signed_reverse _ _ _ (zsign_mul_self' _)
    (P.separatedOuterDots_xz i j s hR Z)
  exact comp_qExpr (Sc := Sc) _ _ _ _ _ i j
    (zsign k (D.parity i)) (zsign k (D.parity i * D.parity j)) hxz
    (P.separatedOuterDots_xy i j s hR Z)
    (fun n hn => by
      simpa only [mul_one] using
        (zsign_pow_of_mul_eq_zero (k := k) (D.parity i) 1 n hn))
    (fun n hn => by
      simpa only [mul_comm (D.parity i)] using
        (zsign_pow_of_mul_eq_zero (k := k) (D.parity j) (D.parity i) n hn))

lemma separatedOuter_z_innerQ :
    P.distinctProbeSpectatorDot i j i s hR Z ≫
        qExpr Sc (P.distinctProbeSpectatorDot i j i s hR Z)
          (P.distinctProbeInnerDot i j i s hR Z) i j =
      qExpr Sc (P.distinctProbeSpectatorDot i j i s hR Z)
          (P.distinctProbeInnerDot i j i s hR Z) i j ≫
        P.distinctProbeSpectatorDot i j i s hR Z := by
  have hzy := signed_reverse _ _ _ (zsign_mul_self' _)
    (P.separatedOuterDots_zy i j s hR Z)
  exact comp_qExpr (Sc := Sc) _ _ _ _ _ i j
    (1 : k) (zsign k (D.parity i * D.parity j)) (one_smul _ _).symm hzy
    (fun n _ => one_pow n)
    (fun n hn => by
      simpa only [mul_comm (D.parity i)] using
        (zsign_pow_of_mul_eq_zero (k := k) (D.parity j) (D.parity i) n hn))
private lemma smul_commuting {C : Type u} [Category C] [Preadditive C] [Linear k C]
    {V : C} (x q : End V) (scalar : k) (h : x ≫ q = q ≫ x) :
    (scalar • x) ≫ q = q ≫ (scalar • x) := by
  rw [Linear.smul_comp, Linear.comp_smul, h]

private lemma mapped_coefficient_commuting (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs)
    (V : P.H (nextSector (true, i) true (nextSector (true, i) false s)))
    {C : Type u} [Category C] [Preadditive C] [Linear k C] {Y : C}
    (φ : End (P.rpObj i i s hR V) →ₐ[k] End Y) (Q : End Y)
    (hx : φ (P.rpPreDot i s hR V) ≫ Q = Q ≫ φ (P.rpPreDot i s hR V))
    (hz : φ (P.rpPostDot i s hR V) ≫ Q = Q ≫ φ (P.rpPostDot i s hR V)) :
    φ (c.a i s hR V) ≫ Q = Q ≫ φ (c.a i s hR V) := by
  have hmap (a b : End (P.rpObj i i s hR V)) : φ (a ≫ b) = φ a ≫ φ b :=
    φ.map_mul b a
  by_cases hi : D.parity i = 0
  · have ha := congrArg φ (hc.even i hi s hR V).1
    have hb := congrArg φ (hc.even i hi s hR V).2
    simp only [hmap, map_sub, show φ (𝟙 _) = 𝟙 _ from φ.map_one] at ha hb
    simpa only [one_smul] using signed_inverse_difference_transport
      _ _ _ _ _ _ Q (1 : k) (one_mul _) (hx.trans (one_smul _ _).symm)
      (hz.trans (one_smul _ _).symm) ha hb
  · have hi' := (Supercategory.parity_eq_zero_or_one (D.parity i)).resolve_left hi
    have ha := congrArg φ (hc.odd i hi' s hR V).1
    simp only [hmap, map_sub] at ha
    have hd : (P.crossDenom h i s hR V : End (P.rpObj i i s hR V)) =
        P.rpPreDot i s hR V ≫ P.rpPreDot i s hR V -
          P.rpPostDot i s hR V ≫ P.rpPostDot i s hR V := by
      simp [crossDenom, hi, sub_eq_add_neg, add_comm, pow_two, End.mul_def]
    have hd' := congrArg φ hd
    simp only [hmap, map_sub] at hd'
    simpa only [one_smul] using signed_odd_coefficient_transport
      _ _ _ _ _ _ Q (1 : k) (one_mul _) (hx.trans (one_smul _ _).symm)
      (hz.trans (one_smul _ _).symm) ha ha
      (Units.map φ.toMonoidHom (P.crossDenom h i s hR V)) hd'

/-- The separated coefficient commutes with the inner Q by the mapped
inverse identities and the actual denominator unit, not by a new hypothesis. -/
lemma separatedOuter_coeff_innerQ (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) :
    P.repeatedOuterMixedSeparatedCoeff i j s hR Z c ≫
        qExpr Sc (P.distinctProbeSpectatorDot i j i s hR Z)
          (P.distinctProbeInnerDot i j i s hR Z) i j =
      qExpr Sc (P.distinctProbeSpectatorDot i j i s hR Z)
          (P.distinctProbeInnerDot i j i s hR Z) i j ≫
        P.repeatedOuterMixedSeparatedCoeff i j s hR Z c := by
  let V := (P.step (true, j) true _ trivial).obj Z
  let φ := P.separatedOuterAlg i j s hR Z
  let Q := qExpr Sc (P.distinctProbeSpectatorDot i j i s hR Z)
    (P.distinctProbeInnerDot i j i s hR Z) i j
  have hx : φ (P.rpPreDot i s hR V) ≫ Q = Q ≫ φ (P.rpPreDot i s hR V) := by
    rw [P.separatedOuterAlg_pre i j s hR Z]
    exact smul_commuting _ _ _ (P.separatedOuter_x_innerQ i j s hR Z)
  have hz : φ (P.rpPostDot i s hR V) ≫ Q = Q ≫ φ (P.rpPostDot i s hR V) := by
    rw [P.separatedOuterAlg_post i j s hR Z]
    exact smul_commuting _ _ _ (P.separatedOuter_z_innerQ i j s hR Z)
  have hresult := mapped_coefficient_commuting P i s hR c hc h V φ Q hx hz
  have he := P.separatedOuterAlg_coeff i j s hR Z c
  exact (congrArg₂ (fun a b => a ≫ Q = Q ≫ b) he he) ▸ hresult
private lemma difference_normalization {R : Type u} [Ring R] [Algebra k R]
    (a q r : R) (ε : k) (hε : ε * ε = 1) (hr : r * a = a * r) :
    -(a * q) - (-(r * a)) = ε • (((-ε) • a) * (q - r)) := by
  rw [hr, smul_mul_assoc, smul_smul, mul_neg, hε, neg_one_smul]
  noncomm_ring

/-- The actual diagonal matrix difference equals the checked separated
coordinate correction, with the original two finite sums and all signs. -/
lemma separatedOuter_braid_difference (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j)
    (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
      nextSector (true, j) true (nextSector (true, i) true s))
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
      nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
    let x := P.distinctProbeOuterDot i j i s hR Z
    let y := P.distinctProbeInnerDot i j i s hR Z
    let z := P.distinctProbeSpectatorDot i j i s hR Z
    braidLeft (P.swappedGens c L) i j i ν n n Z -
      braidRight (P.swappedGens c L) i j i ν n n Z =
      (∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (x ^ (D.dn i j - 1 - a) * z ^ a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i),
        ∑ a ∈ Finset.range b,
          (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
            (x ^ (b - 1 - a) * y ^ d * z ^ a) := by
  dsimp only
  have hl := P.separatedOuter_braidLeft_qExpr ν i j s hR Z hs₀ hs c L hc h hij
  have hr := P.separatedOuter_braidRight_qExpr ν i j s hR Z c L hij
  refine (congrArg₂ (· - ·) hl hr).trans ?_
  have hn := difference_normalization (End.of (P.repeatedOuterMixedSeparatedCoeff i j s hR Z c))
    (qExpr Sc (P.distinctProbeOuterDot i j i s hR Z) (P.distinctProbeInnerDot i j i s hR Z) i j)
    (qExpr Sc (P.distinctProbeSpectatorDot i j i s hR Z) (P.distinctProbeInnerDot i j i s hR Z) i j)
    (zsign k (D.parity i * D.parity j)) (zsign_mul_self' _)
    (P.separatedOuter_coeff_innerQ i j s hR Z c hc h)
  have ha : (-zsign k (D.parity i * D.parity j)) •
      P.repeatedOuterMixedSeparatedCoeff i j s hR Z c =
      P.separatedOuterCoeff i j s hR Z c :=
    congrArg (fun a => (-zsign k (D.parity i * D.parity j)) • a)
      (P.separatedOuterAlg_coeff i j s hR Z c).symm
  rw [ha] at hn
  exact hn.trans (P.separatedOuter_qExpr_correction i j s hR Z c hc)
/-- The literal outer dot is the native separated x. -/
lemma separatedOuter_dotX (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    dotEntry (P.swappedGens c L) ν [] i [up j, up i]
      (SPath.three true true false trivial trivial hR rfl) Z =
      P.distinctProbeOuterDot i j i s hR Z := by
  unfold dotEntry
  refine eq_of_heq ((heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [] (SKM.Shape.dot i) [up j, up i]) (.nil s)
    (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _))
    (SPath.two true false trivial hR rfl) _ _ rfl rfl Z)).trans ?_)
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (P.dotImage_probe i (SKM.wt D ν [up j, up i]) s trivial trivial _)

/-- The literal middle dot is the native separated y. -/
lemma separatedOuter_dotY (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    dotEntry (P.swappedGens c L) ν [up i] j [up i]
      (SPath.three true true false trivial trivial hR rfl) Z =
      P.distinctProbeInnerDot i j i s hR Z := by
  unfold dotEntry
  refine eq_of_heq ((heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i] (SKM.Shape.dot j) [up i]) (.cons _ true s trivial (.nil _))
    (.cons _ true _ trivial (.nil _)) (.cons _ true _ trivial (.nil _))
    (.cons _ false _ hR (.nil _)) _ _ rfl rfl Z)).trans ?_)
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (P.step (true, i) true s trivial).map
    (P.dotImage_probe j (SKM.wt D ν [up i]) (nextSector (true, i) true s) trivial trivial
      ((P.step (true, i) false
        (nextSector (true, j) true (nextSector (true, i) true s)) hR).obj Z)))

/-- The literal reservoir dot is the native separated z. -/
lemma separatedOuter_dotZ (c : P.CrossCoeff Sc) (L : P.LeftwardData) :
    dotEntry (P.swappedGens c L) ν [up i, up j] i []
      (SPath.three true true false trivial trivial hR rfl) Z =
      P.distinctProbeSpectatorDot i j i s hR Z := by
  unfold dotEntry
  refine eq_of_heq ((heq_of_eq (compLayer_eq_of_path (P.swappedGens c L)
    (SKM.lay D ν [up i, up j] (SKM.Shape.dot i) []) (SPath.two true true trivial trivial rfl)
    (.cons _ false _ hR (.nil _)) (.cons _ false _ hR (.nil _))
    (.nil _) _ _ rfl rfl Z)).trans ?_)
  refine (sandwich_heq _ _ _).trans ?_
  exact heq_of_eq (congrArg (fun f => (P.step (true, i) true s trivial).map
    ((P.step (true, j) true _ trivial).map f))
    (P.dotImage_reservoir i ν (nextSector (true, j) true (nextSector (true, i) true s))
      hR hR Z))
private lemma correction_coordinates {C : Type u} [Category C] [Preadditive C] [Linear k C]
    {V : C} (x y z x' y' z' : End V) (hx : x = x') (hy : y = y') (hz : z = z') :
    ((∑ a ∈ Finset.range (D.dn i j),
      (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        (x ^ (D.dn i j - 1 - a) * z ^ a)) +
    ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
      (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
        (x ^ (b - 1 - a) * y ^ d * z ^ a)) =
    (∑ a ∈ Finset.range (D.dn i j),
      (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
        (compPow z' a ≫ compPow x' (D.dn i j - 1 - a))) +
    ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
      (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
        (compPow z' a ≫ compPow y' d ≫ compPow x' (b - 1 - a)) := by
  subst x'; subst y'; subst z'
  simp only [compPow_eq_pow, ← End.mul_def]

/-- The full literal `Pᵢ Pⱼ Rᵢ` diagonal field of CrossBraid, with every
literal dotEntry power and both original coefficient sums. -/
lemma separatedOuter_braidEq_diag (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j)
    (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
      nextSector (true, j) true (nextSector (true, i) true s))
    (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
      nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR rfl
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
  exact (P.separatedOuter_braid_difference ν i j s hR Z c L hc h hij hs₀ hs).trans
    (correction_coordinates i j _ _ _ _ _ _
      (P.separatedOuter_dotX ν i j s hR Z c L).symm
      (P.separatedOuter_dotY ν i j s hR Z c L).symm
      (P.separatedOuter_dotZ ν i j s hR Z c L).symm)
include hR in
/-- Both off-diagonal directions in the one-reservoir repeated-outer
sector, for arbitrary source and target paths and terminal sector. -/
lemma repeatedOuter_oneReservoir_offDiag (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) {t : Sector I}
    (e₀ : nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) false s)) = t)
    (e₁ : nextSector (true, i) false (nextSector (true, j) true
      (nextSector (true, i) true s)) = t)
    (p q : SPath (wd D ν [up i, up j, up i]) s t) (W : P.H t) (hpq : p ≠ q) :
    braidLeft (P.swappedGens c L) i j i ν p q W =
      braidRight (P.swappedGens c L) i j i ν p q W := by
  rcases adjacentMixed_iji_cases hij hR e₀ e₁ p with rfl | rfl <;>
    rcases adjacentMixed_iji_cases hij hR e₀ e₁ q with rfl | rfl
  · exact (hpq rfl).elim
  · subst e₁
    exact P.repeatedOuter_forward_braid i j s hR
      (by simp only [nextSector, add_right_comm]) e₀ W ν c L hc h hij
  · subst e₀
    exact P.repeatedOuter_other_offDiag ν i j s hR c L hij e₁ W
  · exact (hpq rfl).elim
/-- The literal correction at every terminal transport of Pi Pj Ri. -/
lemma separatedOuter_braidEq_diag_transport {t : Sector I}
    (e : nextSector (true, i) false (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (W : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let n : SPath (wd D ν [up i, up j, up i]) s _ :=
      SPath.three true true false trivial trivial hR e
    braidLeft (P.swappedGens c L) i j i ν n n W -
      braidRight (P.swappedGens c L) i j i ν n n W =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n W) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n W)
              (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] n W) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] n W) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] n W) (b - 1 - a)) := by
  subst e
  exact P.separatedOuter_braidEq_diag ν i j s hR W c L hc h hij
    (by simp only [nextSector, add_right_comm])
    (by simp only [nextSector, add_right_comm])
end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
