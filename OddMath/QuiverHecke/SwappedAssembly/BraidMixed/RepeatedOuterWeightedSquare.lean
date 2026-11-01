/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterMixedForward
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.CrossCoeff

/-! # Weighted repeated-outer forward braid

The full finite-sum entry from `Rᵢ Pⱼ Pᵢ` to `Pᵢ Pⱼ Rᵢ` agrees on both sides
for the generators constructed from `c`. This is the forward off-diagonal
component needed by `CrossBraid`. The Q weight commutes with the actual local
coefficient by its inverse identities, and slides through the unequal probe
crossing by supported dot powers. Only comparison isomorphisms are cancelled.
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
variable (P : ProbeReservoir k B D Sc)
variable (i : I)
private lemma coefficient_alg_commute (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (t : Sector I) (hv : StepValid (true, i) false t)
    (V : P.H (nextSector (true, i) true (nextSector (true, i) false t)))
    {C : Type u} [Category C] [Preadditive C] [Linear k C] {Y : C}
    (φ : End (P.rpObj i i t hv V) →ₐ[k] End Y) (f : End Y)
    (hx : φ (P.rpPreDot i t hv V) ≫ f = f ≫ φ (P.rpPreDot i t hv V))
    (hy : φ (P.rpPostDot i t hv V) ≫ f = f ≫ φ (P.rpPostDot i t hv V)) :
    φ (c.a i t hv V) ≫ f = f ≫ φ (c.a i t hv V) := by
  have hmap (a b : End (P.rpObj i i t hv V)) : φ (a ≫ b) = φ a ≫ φ b :=
    φ.map_mul b a
  by_cases hi : D.parity i = 0
  · have ha := congrArg φ (hc.even i hi t hv V).1
    have hb := congrArg φ (hc.even i hi t hv V).2
    simp only [hmap, map_sub, show φ (𝟙 _) = 𝟙 _ from φ.map_one] at ha hb
    simpa only [one_smul] using signed_inverse_difference_transport
      _ _ _ _ _ _ f (1 : k) (one_mul _) (hx.trans (one_smul _ _).symm)
      (hy.trans (one_smul _ _).symm) ha hb
  · have hi' := (Supercategory.parity_eq_zero_or_one (D.parity i)).resolve_left hi
    have ha := congrArg φ (hc.odd i hi' t hv V).1
    simp only [hmap, map_sub] at ha
    have hd : (P.crossDenom h i t hv V : End (P.rpObj i i t hv V)) =
        P.rpPreDot i t hv V ≫ P.rpPreDot i t hv V -
          P.rpPostDot i t hv V ≫ P.rpPostDot i t hv V := by
      simp [crossDenom, hi, sub_eq_add_neg, add_comm, pow_two, End.mul_def]
    have hd' := congrArg φ hd
    simp only [hmap, map_sub] at hd'
    simpa only [one_smul] using signed_odd_coefficient_transport
      _ _ _ _ _ _ f (1 : k) (one_mul _) (hx.trans (one_smul _ _).symm)
      (hy.trans (one_smul _ _).symm) ha ha
      (Units.map φ.toMonoidHom (P.crossDenom h i t hv V)) hd'

lemma mixedQ_comp_repeatedOuterCoeff
    (j : I) (s : Sector I)
    (hR : StepValid (true, i) false s)
    (V : P.H (nextSector (true, i) true
      (nextSector (true, i) false (nextSector (true, j) true s))))
    (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) :
    P.mixedQ j i s hR
        ((P.step (true, i) true
          (nextSector (true, i) false (nextSector (true, j) true s))
          trivial).obj V) ≫
      (P.step (true, j) true s trivial).map
        (c.a i (nextSector (true, j) true s) hR V) =
    (P.step (true, j) true s trivial).map
        (c.a i (nextSector (true, j) true s) hR V) ≫
      P.mixedQ j i s hR
        ((P.step (true, i) true
          (nextSector (true, i) false (nextSector (true, j) true s))
          trivial).obj V) := by
  let t := nextSector (true, j) true s
  let F := P.step (true, j) true s trivial
  have : F.Additive := P.step_additive (true, j) true s trivial
  have : F.Linear k := P.step_linear (true, j) true s trivial
  let U := (P.step (true, i) true
    (nextSector (true, i) false t) trivial).obj V
  let φ := functorAlg (k := k) F (P.rpObj i i t hR V)
  let x := φ (P.rpPreDot i t hR V)
  let a := P.prPreDot j i s hR U
  let b := P.prPostDot j i s hR U
  have hax :
      a ≫ x = zsign k (D.parity j * D.parity i) • (x ≫ a) := by
    have he := TwoSupercategory.super_interchange (R := k)
      (P.T.dot_mem j (P.muP_preE j s))
      ((P.rpPreDot_supernatural i t hR).mem V)
    rw [koszulSign_smul_eq_zsign (k := k)] at he
    exact he
  have hxa :
      x ≫ a = zsign k (D.parity j * D.parity i) • (a ≫ x) := by
    rw [hax, smul_smul, zsign_mul_self', one_smul]
  have hxb :
      x ≫ b = zsign k (D.parity i * D.parity i) • (b ≫ x) := by
    have he := congrArg F.map (P.rpPreDot_comp_rpPostDot i t hR V)
    simp only [Functor.map_comp] at he
    rw [koszulSign_smul_eq_zsign (k := k), Functor.map_smul, Functor.map_comp] at he
    exact he
  have hx :
      φ (P.rpPreDot i t hR V) ≫ P.mixedQ j i s hR U =
        P.mixedQ j i s hR U ≫ φ (P.rpPreDot i t hR V) := by
    change x ≫ qExpr Sc a b j i = qExpr Sc a b j i ≫ x
    exact comp_qExpr (Sc := Sc) x a b a b j i
      (zsign k (D.parity j * D.parity i))
      (zsign k (D.parity i * D.parity i))
      hxa hxb
      (fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn)
      (fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn)
  have hy :
      φ (P.rpPostDot i t hR V) ≫ P.mixedQ j i s hR U =
        P.mixedQ j i s hR U ≫ φ (P.rpPostDot i t hR V) := by
    exact (P.mixedQ_comm j i s hR U).1
  exact (coefficient_alg_commute P i c hc h t hR V φ
    (P.mixedQ j i s hR U) hx hy).symm
private def outerQ (j i r : I) (s : Sector I)
    (Y : P.H (nextSector (true, i) true (nextSector (true, j) true s))) (θ : End Y) :=
  qExpr Sc (P.T.dot j (P.muP_preE j s) ▷ (P.step (true, i) true _ trivial).obj Y)
    ((P.step (true, j) true s trivial).map ((P.step (true, i) true _ trivial).map θ)) j r

private lemma outerQ_heq (j i r : I) (s : Sector I)
    {Y Y' : P.H (nextSector (true, i) true (nextSector (true, j) true s))}
    (hY : Y = Y') {θ : End Y} {θ' : End Y'} (hθ : HEq θ θ') :
    HEq (outerQ P j i r s Y θ) (outerQ P j i r s Y' θ') := by
  subst hY
  cases hθ
  rfl

variable (j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
    nextSector (true, j) true (nextSector (true, i) true s))
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

lemma adjacentReverseProbeCross_Q_outer (hij : i ≠ j) :
    ((P.distinctProbeFirstIso j i i s hR ((P.castH hs).obj Z)).hom ≫
      P.mixedQ j i s hR
        ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z)) ≫
      (P.distinctProbeFirstIso j i i s hR ((P.castH hs).obj Z)).inv) ≫
      P.adjacentReverseProbeCross i j s hR hs₀ Z =
    P.adjacentReverseProbeCross i j s hR hs₀ Z ≫
      (P.step (true, i) true s trivial).map
        (P.mixedQ j i (nextSector (true, i) true s) hR Z) := by
  let Y := (P.step (true, i) false (nextSector (true, j) true (nextSector (true, i) true s)) hR).obj Z
  let θ := P.dotDiag i false (nextSector (true, j) true (nextSector (true, i) true s)) hR Z
  have hθ : θ ∈ parity (R := k) _ _ (D.parity i) := by
    have h := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W i
      (nextSector (true, j) true (nextSector (true, i) true s)).1
      (P.muP (nextSector (true, j) true (nextSector (true, i) true s)))
      (P.muM_postE i hR) 1).mem Z
    simp only [Nat.cast_one, one_mul, pow_one] at h
    exact h
  have hQ := P.preCrossNe_qExpr_outer j i i hij.symm s hs₀ Y θ hθ
  obtain ⟨hY, hd⟩ := P.reservoirDot_cast i hs₀ hR hR Z
  have hw := outerQ_heq P j i i s hY hd
  have hw' : HEq
      ((P.distinctProbeFirstIso j i i s hR ((P.castH hs).obj Z)).hom ≫
        P.mixedQ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z)) ≫
        (P.distinctProbeFirstIso j i i s hR ((P.castH hs).obj Z)).inv)
      (outerQ P j i i s ((P.castH hs₀).obj Y) ((P.castH hs₀).map θ)) :=
    (heq_of_eq (P.distinctProbeFirstIso_conj_mixedQ j i i s hR ((P.castH hs).obj Z))).trans hw.symm
  have hA := congrArg (fun Y => (P.step (true, j) true s trivial).obj
    ((P.step (true, i) true _ trivial).obj Y)) hY
  have hf : HEq (P.adjacentReverseProbeCross i j s hR hs₀ Z)
      (P.preCrossNe j i s hs₀ Y) := by
    exact eqToHom_comp_heq _ _
  apply rectangle_of_heq hA.symm hA.symm hA.symm rfl rfl hw' hf hf
    (heq_of_eq (P.distinctProbe_map_mixedQ i j i s hR Z))
  apply heq_of_eq
  exact hQ
private lemma weighted_square {C : Type u} [Category C] [Preadditive C]
    {V₀ V₁ V₂ V₃ V₄ V₅ : C}
    (E : V₁ ≅ V₀) (J : V₂ ≅ V₁) (K : V₅ ≅ V₄)
    (A Q : End V₁) (Qn : End V₅)
    (f : V₂ ⟶ V₅) (g : V₀ ⟶ V₃) (T : V₃ ⟶ V₄)
    (hcomm : Q ≫ A = A ≫ Q)
    (hq : (J.hom ≫ Q ≫ J.inv) ≫ f = f ≫ Qn)
    (hsq : (-(A ≫ A ≫ J.inv)) ≫ (f ≫ K.hom) = (E.hom ≫ g) ≫ T) :
    (E.inv ≫ Q ≫ (-(A ≫ A ≫ J.inv))) ≫ f =
      (g ≫ T) ≫ K.inv ≫ Qn := by
  have hs : (-(A ≫ A ≫ J.inv)) ≫ f = (E.hom ≫ g) ≫ T ≫ K.inv := by
    have he := congrArg (fun z => z ≫ K.inv) hsq
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he
  have hslide : Q ≫ (-(A ≫ A ≫ J.inv)) =
      (-(A ≫ A ≫ J.inv)) ≫ (J.hom ≫ Q ≫ J.inv) := by
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← Category.assoc Q A, hcomm, Category.assoc, ← Category.assoc Q A, hcomm]
    simp only [Category.assoc]
  calc
    (E.inv ≫ Q ≫ (-(A ≫ A ≫ J.inv))) ≫ f =
        E.inv ≫ (-(A ≫ A ≫ J.inv)) ≫ f ≫ Qn := by
      rw [hslide]
      simp only [Category.assoc] at hq ⊢
      rw [hq]
    _ = (g ≫ T) ≫ K.inv ≫ Qn := by
      rw [← Category.assoc (-(A ≫ A ≫ J.inv)), hs]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

private lemma map_square {C C' : Type u} [Category C] [Preadditive C]
    [Category C'] [Preadditive C'] (F : C ⥤ C') [F.Additive]
    {X Y : C} (a : End X) (v : X ⟶ Y) :
    F.map (-(a ≫ a ≫ v)) = -(F.map a ≫ F.map a ≫ F.map v) := by
  simp only [Functor.map_neg, Functor.map_comp]

lemma repeatedOuter_weighted_square (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let E := P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))
    let J := (P.step (true, j) true s trivial).mapIso
      (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))
    let K := (P.step (true, i) true s trivial).mapIso
      (P.mixedJ j i (nextSector (true, i) true s) hR Z)
    let H := P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)
    let A := (P.step (true, j) true s trivial).map
      (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))
    let B := c.a i s hR ((P.step (true, j) true _ trivial).obj Z)
    let Q := P.mixedQ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))
    let Qn := (P.step (true, i) true s trivial).map
      (P.mixedQ j i (nextSector (true, i) true s) hR Z)
    let f := P.adjacentReverseProbeCross i j s hR hs₀ Z
    let g := (P.step (true, i) false s hR).map
      (P.preCrossNe j i (nextSector (true, i) false s) hs Z)
    (E.inv ≫ Q ≫ (-(A ≫ A ≫ J.inv))) ≫ f =
      (g ≫ (-(B ≫ B ≫ H.inv))) ≫ K.inv ≫ Qn := by
  dsimp only
  apply weighted_square
  · exact P.mixedQ_comp_repeatedOuterCoeff i j s hR ((P.castH hs).obj Z) c hc h
  · exact P.adjacentReverseProbeCross_Q_outer i j s hR hs₀ hs Z hij
  · have he := P.adjacentReverse_square_rectangle i j s hR hs₀ hs Z c hc h hij
    have : (P.step (true, j) true s trivial).Additive := P.step_additive _ _ _ _
    have hm := map_square (P.step (true, j) true s trivial)
      (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))
      (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).inv
    exact (congrArg (fun q => q ≫ (P.adjacentReverseProbeCross i j s hR hs₀ Z ≫
      (P.step (true, i) true s trivial).map
        (P.mixedJ j i (nextSector (true, i) true s) hR Z).hom)) hm.symm).trans he
lemma repeatedOuter_forward_outer_heq (ν : X) (c : P.CrossCoeff Sc)
    (L : P.LeftwardData) (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true false true trivial hR trivial hs) Z)
      ((P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫
        P.mixedQ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))) := by
  generalize ht : nextSector (true, j) true (nextSector (true, i) true
    (nextSector (true, i) false s)) = t at Z hs
  subst hs
  exact heq_of_eq (P.adjacentMixed_mixed ν i j s hR c L Z hij)

lemma repeatedOuter_forward_inner (ν : X) (c : P.CrossCoeff Sc)
    (L : P.LeftwardData) (hij : i ≠ j) :
    crossEntry (P.swappedGens c L) ν [up i] i j []
      (SPath.three true false true trivial hR trivial rfl)
      (SPath.three true true false trivial trivial hR rfl) Z =
    (P.step (true, i) true s trivial).map
      ((P.mixedJ j i (nextSector (true, i) true s) hR Z).inv ≫
        P.mixedQ j i (nextSector (true, i) true s) hR Z) := by
  refine (crossEntry_right (P.swappedGens c L) ν i i j true trivial
    (SPath.two false true hR trivial rfl) (SPath.two true false trivial hR rfl) Z).trans ?_
  dsimp only [swappedGens]
  exact congrArg (P.step (true, i) true s trivial).map
    (P.crossImage_ne c hij ν (t := nextSector (true, i) true s)
      (SPath.two false true hR trivial rfl)
      (SPath.two true false trivial hR rfl) Z)

private theorem forward_left_pair (ν : X) (c : P.CrossCoeff Sc)
    (L : P.LeftwardData) (hij : i ≠ j) :
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true false true trivial hR trivial hs) Z ≫
      crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true false true trivial hR trivial hs)
      (SPath.three true true false trivial trivial hR hs) Z)
      (((P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫
        P.mixedQ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))) ≫
        (P.step (true, j) true s trivial).map
          (-(c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z) ≫
            c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z) ≫
            (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).inv))) := by
  have h2 := P.adjacentReverse_source_square_heq ν i j s c L hR hs Z
  generalize ht : nextSector (true, j) true (nextSector (true, i) true
    (nextSector (true, i) false s)) = t at Z hs h2
  subst hs
  have h1 := P.adjacentMixed_mixed ν i j s hR c L Z hij
  exact heq_of_eq (congrArg₂ (fun f g => f ≫ g) h1 (eq_of_heq h2))

private theorem forward_left_grid (ν : X) (c : P.CrossCoeff Sc)
    (L : P.LeftwardData) (hij : i ≠ j) :
    HEq ((crossEntry (P.swappedGens c L) ν [] i j [up i]
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true false true trivial hR trivial hs) Z ≫
      crossEntry (P.swappedGens c L) ν [up j] i i []
      (SPath.three true false true trivial hR trivial hs)
      (SPath.three true true false trivial trivial hR hs) Z) ≫
      crossEntry (P.swappedGens c L) ν [] j i [up i]
      (SPath.three true true false trivial trivial hR hs)
      (SPath.three true true false trivial trivial hR rfl) Z)
      ((((P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫
        P.mixedQ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))) ≫
        (P.step (true, j) true s trivial).map
          (-(c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z) ≫
            c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z) ≫
            (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).inv))) ≫
        P.adjacentReverseProbeCross i j s hR hs₀ Z) := by
  have hM := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
    (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    false true true hR trivial trivial hs Z
  have hB := P.pathFunctor_three_obj (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
    (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    true true false trivial trivial hR hs Z
  exact comp_common_grid_heq hM hB rfl
    (forward_left_pair P i j s hR hs Z ν c L hij)
    (P.adjacentReverse_probe_heq ν i j s c L hR hs₀ hs Z hij)

private theorem forward_right_grid (ν : X) (c : P.CrossCoeff Sc)
    (L : P.LeftwardData) (hij : i ≠ j) :
    HEq ((crossEntry (P.swappedGens c L) ν [up i] j i []
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three false true true hR trivial trivial rfl) Z ≫
      crossEntry (P.swappedGens c L) ν [] i i [up j]
      (SPath.three false true true hR trivial trivial rfl)
      (SPath.three true false true trivial hR trivial rfl) Z) ≫
      crossEntry (P.swappedGens c L) ν [up i] i j []
      (SPath.three true false true trivial hR trivial rfl)
      (SPath.three true true false trivial trivial hR rfl) Z)
      (((P.step (true, i) false s hR).map
        (P.preCrossNe j i (nextSector (true, i) false s) hs Z) ≫
        (-(c.a i s hR ((P.step (true, j) true _ trivial).obj Z) ≫
          c.a i s hR ((P.step (true, j) true _ trivial).obj Z) ≫
          (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)).inv))) ≫
        (P.step (true, i) true s trivial).map
          ((P.mixedJ j i (nextSector (true, i) true s) hR Z).inv ≫
            P.mixedQ j i (nextSector (true, i) true s) hR Z)) :=
  let hM := P.pathFunctor_three_obj (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩)
    (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
    false true true hR trivial trivial hs Z
  comp_common_grid_heq hM rfl rfl
    (comp_common_grid_heq hM rfl rfl
      (P.adjacentReverse_rightProbe_heq ν i j s c L hR hs Z hij)
      (P.adjacentReverse_target_square_heq ν i j s c L hR Z))
    (heq_of_eq (P.repeatedOuter_forward_inner i j s hR Z ν c L hij))

include hs₀ in
lemma repeatedOuter_forward_braid (ν : X) (c : P.CrossCoeff Sc)
    (L : P.LeftwardData) (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true true false trivial trivial hR rfl) Z =
    braidRight (P.swappedGens c L) i j i ν
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true true false trivial trivial hR rfl) Z := by
  have hl := forward_left_grid P i j s hR hs₀ hs Z ν c L hij
  have hr := forward_right_grid P i j s hR hs Z ν c L hij
  have raw := P.repeatedOuter_weighted_square i j s hR hs₀ hs Z c hc h hij
  have : (P.step (true, j) true s trivial).Additive := P.step_additive _ _ _ _
  have hm := map_square (P.step (true, j) true s trivial)
    (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))
    (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).inv
  have hn := (P.step (true, i) true s trivial).map_comp
    (P.mixedJ j i (nextSector (true, i) true s) hR Z).inv
    (P.mixedQ j i (nextSector (true, i) true s) hR Z)
  apply (P.repeatedOuter_forward_left_route (P.swappedGens c L) ν i j s hR hs Z hij).trans
  apply Eq.trans _ (P.repeatedOuter_forward_right_route (P.swappedGens c L) ν i j s hR hs Z hij).symm
  apply eq_of_heq (hl.trans ((heq_of_eq ?_).trans hr.symm))
  rw [hm, hn]
  exact (congrArg (fun z => z ≫ _) (Category.assoc _ _ _)).trans raw
end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
