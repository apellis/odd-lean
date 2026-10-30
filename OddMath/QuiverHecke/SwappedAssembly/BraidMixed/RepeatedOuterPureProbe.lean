/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentPureProbe
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPureReservoir

/-! # Repeated-outer probe factor braid

The correction polynomial of the probe relation is right-whiskered and
reassociated. The crossing order is reversed, and the equal crossing has
its prescribed negative Koszul normalization.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

/-- The dotted correction of the probe factor on the repeated-outer triple. -/
def repeatedOuterProbeCorrection (P : ProbeReservoir k B D Sc)
    (i j : I) {a b c d : X}
    (hab : a + D.α i = b) (hbc : b + D.α j = c) (hcd : c + D.α i = d) :
    End (P.T.E i hab ≫ P.T.E j hbc ≫ P.T.E i hcd) :=
      ∑ s ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
          (rouquierPower (P.T.dot i hab) s ▷ (P.T.E j hbc ≫ P.T.E i hcd) ≫
            P.T.E i hab ◁ P.T.E j hbc ◁ rouquierPower (P.T.dot i hcd) (D.dn i j - 1 - s)) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
        (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          (rouquierPower (P.T.dot i hab) s ▷ (P.T.E j hbc ≫ P.T.E i hcd) ≫
            P.T.E i hab ◁ (rouquierPower (P.T.dot j hbc) q ▷ P.T.E i hcd) ≫
            P.T.E i hab ◁ P.T.E j hbc ◁ rouquierPower (P.T.dot i hcd) (p - 1 - s))

/-- The reversed probe factor braid before the equal-crossing scalar. -/
theorem repeatedOuterPureProbe_factor_braid (P : ProbeReservoir k B D Sc)
    (i j : I) (hne : i ≠ j) {a bi bj cij cii d : X}
    (hi : a + D.α i = bi) (hj : a + D.α j = bj)
    (hij : bi + D.α j = cij) (hji : bj + D.α i = cij)
    (hii : bi + D.α i = cii)
    (hd12 : cij + D.α i = d) (hd13 : cii + D.α j = d) {e : B} (Z : P.T.obj d ⟶ e) :
    ((associator (P.T.E i hi) (P.T.E j hij) ((P.T.E i hd12) ≫ Z)).inv ≫ (P.T.cross j i hi hij hj
        hji) ▷ ((P.T.E i hd12) ≫ Z) ≫ (associator (P.T.E j hj) (P.T.E i hji) ((P.T.E i hd12) ≫
        Z)).hom) ≫
      (P.T.E j hj) ◁ ((associator (P.T.E i hji) (P.T.E i hd12) Z).inv ≫ (P.T.cross i i hji hd12
          hji hd12) ▷ Z ≫ (associator (P.T.E i hji) (P.T.E i hd12) Z).hom) ≫
      ((associator (P.T.E j hj) (P.T.E i hji) ((P.T.E i hd12) ≫ Z)).inv ≫ (P.T.cross i j hj hji hi
          hij) ▷ ((P.T.E i hd12) ≫ Z) ≫ (associator (P.T.E i hi) (P.T.E j hij) ((P.T.E i hd12) ≫
          Z)).hom) - (
      (P.T.E i hi) ◁ ((associator (P.T.E j hij) (P.T.E i hd12) Z).inv ≫ (P.T.cross i j hij hd12
          hii hd13) ▷ Z ≫ (associator (P.T.E i hii) (P.T.E j hd13) Z).hom) ≫
      ((associator (P.T.E i hi) (P.T.E i hii) ((P.T.E j hd13) ≫ Z)).inv ≫ (P.T.cross i i hi hii hi
          hii) ▷ ((P.T.E j hd13) ≫ Z) ≫ (associator (P.T.E i hi) (P.T.E i hii) ((P.T.E j hd13) ≫
          Z)).hom) ≫
      (P.T.E i hi) ◁ ((associator (P.T.E i hii) (P.T.E j hd13) Z).inv ≫ (P.T.cross j i hii hd13
          hij hd12) ▷ Z ≫ (associator (P.T.E j hij) (P.T.E i hd12) Z).hom) ) =
      -((tripleRightIso (k := k) (P.T.E i hi) (P.T.E j hij) (P.T.E i hd12) Z).inv ≫
        P.repeatedOuterProbeCorrection i j hi hij hd12 ▷ Z ≫
        (tripleRightIso (k := k) (P.T.E i hi) (P.T.E j hij) (P.T.E i hd12) Z).hom) := by
  rw [tripleRightIso_left (k := k), tripleRightIso_left (k := k), tripleRightIso_left (k := k),
    tripleRightIso_right (k := k), tripleRightIso_right (k := k), tripleRightIso_right (k := k)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hb := P.probeRel.braidEq i j hne hi hj hij hii hji hd12 hd13
  have hb' : _ = -P.repeatedOuterProbeCorrection i j hi hij hd12 :=
    (neg_sub _ _).symm.trans (congrArg Neg.neg hb)
  have hw := congrArg (fun f =>
    (tripleRightIso (k := k) (P.T.E i hi) (P.T.E j hij) (P.T.E i hd12) Z).inv ≫ f ▷ Z ≫
      (tripleRightIso (k := k) (P.T.E i hi) (P.T.E j hij) (P.T.E i hd12) Z).hom) hb'
  simpa only [sub_eq_add_neg, TwoSupercategory.add_whiskerRight (R := k),
    TwoSupercategory.neg_whiskerRight (R := k), TwoSupercategory.comp_whiskerRight (R := k),
    Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_neg,
    Preadditive.neg_comp, Category.assoc] using hw

/-- The normalized probe cores include the negative Koszul scalar on the
middle equal crossing. Reversal of the factor braid cancels its minus sign. -/
theorem repeatedOuterPureProbe_scaled_factor_braid (P : ProbeReservoir k B D Sc)
    (i j : I) (hne : i ≠ j) {a bi bj cij cii d : X}
    (hi : a + D.α i = bi) (hj : a + D.α j = bj)
    (hij : bi + D.α j = cij) (hji : bj + D.α i = cij)
    (hii : bi + D.α i = cii) (hd12 : cij + D.α i = d)
    (hd13 : cii + D.α j = d) {e : B} (Z : P.T.obj d ⟶ e) :
    probeCore P.T i j hi hij hj hji (P.T.E i hd12 ≫ Z) ≫
      P.T.E j hj ◁ (pureProbeScale (D := D) i i •
        probeCore P.T i i hji hd12 hji hd12 Z) ≫
      probeCore P.T j i hj hji hi hij (P.T.E i hd12 ≫ Z) -
    (P.T.E i hi ◁ probeCore P.T j i hij hd12 hii hd13 Z ≫
      (pureProbeScale (D := D) i i •
        probeCore P.T i i hi hii hi hii (P.T.E j hd13 ≫ Z)) ≫
      P.T.E i hi ◁ probeCore P.T i j hii hd13 hij hd12 Z) =
    koszulSign (D.parity i) (D.parity i) •
      ((tripleRightIso (k := k) (P.T.E i hi) (P.T.E j hij) (P.T.E i hd12) Z).inv ≫
        P.repeatedOuterProbeCorrection i j hi hij hd12 ▷ Z ≫
        (tripleRightIso (k := k) (P.T.E i hi) (P.T.E j hij) (P.T.E i hd12) Z).hom) := by
  classical
  simp only [TwoSupercategory.whiskerLeft_zsmul (R := k),
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, ← smul_sub]
  rw [show pureProbeScale (D := D) i i = -koszulSign (D.parity i) (D.parity i) by
    simp only [pureProbeScale, ite_true]]
  dsimp only [probeCore]
  rw [P.repeatedOuterPureProbe_factor_braid i j hne hi hj hij hji hii hd12 hd13 Z]
  simp only [neg_smul, smul_neg, neg_neg]

/-- The repeated-outer pure-probe path braid in normalized factor coordinates,
including the equal-colour negative Koszul normalization. -/
theorem repeatedOuterPureProbe_canonical_heq
    [∀ a b : B, PiSupercategory k (a ⟶ b)]
    (P : ProbeReservoir k B D Sc) (ν : X) (i j : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hne : i ≠ j)
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) true s)))) :
    let p := distinctPureProbePath (D := D) ν i j i s rfl
    let Θ := tripleRightIso (k := k) (P.T.E i (P.muP_preE i s))
      (P.T.E j (P.muP_preE j _)) (P.T.E i (P.muP_preE i _)) Z
    HEq (braidLeft (P.swappedGens c L) i j i ν p p Z -
      braidRight (P.swappedGens c L) i j i ν p p Z)
      (koszulSign (D.parity i) (D.parity i) •
        (Θ.inv ≫ P.repeatedOuterProbeCorrection i j
          (P.muP_preE i s) (P.muP_preE j _) (P.muP_preE i _) ▷ Z ≫ Θ.hom)) := by
  classical
  dsimp only
  have e : nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) true s)) =
      nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) true s)) := rfl
  let t := nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) true s))
  have e213 : nextSector (true, i) true (nextSector (true, i) true (nextSector (true, j) true s)) =
      t := by
    simp only [t, nextSector, add_comm, add_left_comm]
  have e231 : nextSector (true, i) true (nextSector (true, i) true (nextSector (true, j) true s)) =
      t := by
    simp only [t, nextSector, add_comm, add_left_comm]
  have e132 : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) true s)) =
      t := by
    simp only [t, nextSector, add_comm, add_left_comm]
  have e312 : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) true s)) =
      t := by
    simp only [t, nextSector, add_comm, add_left_comm]
  let : Subsingleton (SPath (wd D ν [up j, up i, up i]) s t) :=
    ⟨fun p q => (pureProbePath_unique e213 p).trans (pureProbePath_unique e213 q).symm⟩
  let : Subsingleton (SPath (wd D ν [up j, up i, up i]) s t) :=
    ⟨fun p q => (pureProbePath_unique e231 p).trans (pureProbePath_unique e231 q).symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up i, up j]) s t) :=
    ⟨fun p q => (pureProbePath_unique e132 p).trans (pureProbePath_unique e132 q).symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up i, up j]) s t) :=
    ⟨fun p q => (pureProbePath_unique e312 p).trans (pureProbePath_unique e312 q).symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up i]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up i]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up i, up i, up j]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up i, up i, up j]) s t)
  unfold braidLeft braidRight
  rw [Fintype.sum_subsingleton _ (distinctPureProbePath (D := D) ν j i i s e231),
    Fintype.sum_subsingleton _ (distinctPureProbePath (D := D) ν j i i s e213),
    Fintype.sum_subsingleton _ (distinctPureProbePath (D := D) ν i i j s e312),
    Fintype.sum_subsingleton _ (distinctPureProbePath (D := D) ν i i j s e132)]
  have hji := (P.muP_preE i (nextSector (true, j) true s)).trans
    (congrArg (fun x => -P.muP x) (pureProbe_swap j i s))
  have hri := (P.muP_preE i (nextSector (true, i) true s)).trans
    (congrArg (fun x => -P.muP x) (pureProbe_swap i i s))
  have hrj := (P.muP_preE j (nextSector (true, i) true s)).trans
    (congrArg (fun x => -P.muP x) (pureProbe_swap i j s))
  have hd12 := (P.muP_preE i (nextSector (true, j) true (nextSector (true, i) true s))).trans
    (congrArg (fun x => -P.muP x) e)
  have hd13 := (P.muP_preE j (nextSector (true, i) true (nextSector (true, i) true s))).trans
    (congrArg (fun x => -P.muP x) e132)
  have hd23 := (P.muP_preE i (nextSector (true, i) true (nextSector (true, j) true s))).trans
    (congrArg (fun x => -P.muP x) e231)
  have wji := congrArg (fun x => -P.muP x) (pureProbe_swap i j s)
  have wri := congrArg (fun x => -P.muP x) (pureProbe_swap i i s)
  have wrj := congrArg (fun x => -P.muP x) (pureProbe_swap j i s)
  exact repeatedOuterHexagon_difference_heq
    (eq_of_heq (P.distinctPureProbe_obj ν i j i s e Z rfl rfl rfl rfl
      (P.muP_preE i s) (P.muP_preE j _) hd12 Z HEq.rfl))
    (eq_of_heq (P.distinctPureProbe_obj ν j i i s e213 Z rfl wji rfl rfl
      (P.muP_preE j s) hji hd12 Z HEq.rfl))
    (eq_of_heq (P.distinctPureProbe_obj ν j i i s e231 Z rfl wji rfl rfl
      (P.muP_preE j s) hji hd12 Z HEq.rfl))
    (eq_of_heq (P.distinctPureProbe_obj ν i j i s rfl Z rfl rfl rfl rfl
      (P.muP_preE i s) (P.muP_preE j _) hd12 Z HEq.rfl))
    (eq_of_heq (P.distinctPureProbe_obj ν i i j s e132 Z rfl rfl rfl rfl
      (P.muP_preE i s) (P.muP_preE i _) hd13 Z HEq.rfl))
    (eq_of_heq (P.distinctPureProbe_obj ν i i j s e312 Z rfl wri rfl rfl
      (P.muP_preE i s) hri hd13 Z HEq.rfl))
    (P.pureProbe_left_core ν i j i s c L (pureProbe_swap i j s) e e213 Z
      rfl rfl rfl rfl (P.muP_preE i s) (P.muP_preE j _) (P.muP_preE j s) hji hd12 Z HEq.rfl)
    (P.pureProbe_right_core ν j i i s c L e213 e231 Z
      rfl wji wji rfl (P.muP_preE j s) hji hji hd12 hd12 Z HEq.rfl)
    (P.pureProbe_left_core ν j i i s c L
      (pureProbe_swap j i s) e231 rfl Z
      rfl rfl wji rfl (P.muP_preE j s) hji (P.muP_preE i s) (P.muP_preE j _) hd12 Z HEq.rfl)
    (P.pureProbe_right_core ν i j i s c L e e132 Z
      rfl rfl rfl rfl (P.muP_preE i s) (P.muP_preE j _) (P.muP_preE i _) hd12 hd13 Z HEq.rfl)
    (P.pureProbe_left_core ν i i j s c L (pureProbe_swap i i s) e132 e312 Z
      rfl rfl rfl rfl (P.muP_preE i s) (P.muP_preE i _) (P.muP_preE i s) hri hd13 Z HEq.rfl)
    (P.pureProbe_right_core ν i i j s c L e312 rfl Z
      rfl wri rfl rfl (P.muP_preE i s) hri (P.muP_preE j _) hd13 hd12 Z HEq.rfl)
    (by
      simpa only [pureProbeScale, ite_true, ite_eq_right hne,
        ite_eq_right hne.symm, one_smul] using
        P.repeatedOuterPureProbe_scaled_factor_braid i j hne
          (P.muP_preE i s) (P.muP_preE j s) (P.muP_preE j _) hji
          (P.muP_preE i _) hd12 hd13 Z)

/-- At a pure-probe endpoint the repeated-outer word has only one path. -/
theorem repeatedOuterPureProbe_path_eq (ν : X) (i j : I) {s t : Sector I}
    (ht : nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) true s)) = t)
    (p q : SPath (wd D ν [up i, up j, up i]) s t) : p = q := by
  exact (pureProbePath_unique ht p).trans (pureProbePath_unique ht q).symm

/-- Off-diagonal entries in a pure-probe sector vanish by path uniqueness. -/
theorem repeatedOuterPureProbe_offdiag [∀ a b : B, PiSupercategory k (a ⟶ b)]
    (P : ProbeReservoir k B D Sc)
    (ν : X) (i j : I) {s t : Sector I} (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (ht : nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) true s)) = t) (p q : SPath (wd D ν [up i, up j, up i]) s t)
    (hpq : p ≠ q) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j i ν p q Z = 0 ∧
      braidRight (P.swappedGens c L) i j i ν p q Z = 0 := by
  exact (hpq (repeatedOuterPureProbe_path_eq ν i j ht p q)).elim

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
