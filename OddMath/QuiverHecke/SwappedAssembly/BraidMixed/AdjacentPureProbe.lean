/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctPureProbeSector
/-! # Pure-probe non-correction braids with adjacent equal colours

The pure-probe endpoint of the swapped non-correction braid, including repeated
adjacent colours. Equal-colour entries retain their prescribed negative Koszul sign.
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
/-- The maximal probe-content endpoint forces all three choices to be probe,
without any inequality between the colours. -/
theorem pureProbePath_unique {ν : X} {i j r : I} {s t : Sector I}
    (e : nextSector (true, r) true (nextSector (true, j) true
      (nextSector (true, i) true s)) = t)
    (p : SPath (wd D ν [up i, up j, up r]) s t) :
    p = distinctPureProbePath ν i j r s e := by
  obtain ⟨a, b, c, ha, hb, hc, e', rfl⟩ := SPath.exists_eq_three p
  have h := congrArg (fun x : Sector I => x.1.sum (fun _ n => n)) (e'.trans e.symm)
  cases a <;> cases b <;> cases c <;>
    first | rfl | (exfalso; simp [nextSector,
      Finsupp.sum_add_index' (h := fun (_ : I) (n : ℕ) => n)
        (fun _ => rfl) (fun _ _ _ => rfl)] at h <;> omega)

variable [∀ a b : B, PiSupercategory k (a ⟶ b)]
variable (P : ProbeReservoir k B D Sc)

/-- The normalization of a pure probe crossing. -/
def pureProbeScale (i j : I) : ℤ := by
  classical
  exact if i = j then -koszulSign (D.parity i) (D.parity i) else 1

/-- The equal-colour entry is the normalized unscaled probe crossing. -/
theorem preCrossSame_eq_scaled (i : I) (s : Sector I)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) true s))) :
    P.preCrossSame i s Z = pureProbeScale (D := D) i i • P.preCrossNe i i s rfl Z := by
  have h := eq_of_heq (P.preCrossNe_heq i i s rfl Z (P.muP_preE i _))
  rw [h]
  simp only [pureProbeScale, ite_true]
  rfl

theorem pureProbe_left_raw (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s))
    {t : Sector I}
    (e : nextSector (true, r) true (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, r) true (nextSector (true, i) true (nextSector (true, j) true s)) = t)
    (Z : P.H t) :
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up r]
      (distinctPureProbePath ν i j r s e) (distinctPureProbePath ν j i r s e') Z)
      (pureProbeScale (D := D) i j •
        P.preCrossNe i j s hs ((P.step (true, r) true _ trivial).obj (e' ▸ Z))) := by
  subst e'
  let pg : SPath (wd D (SKM.wt D ν [up r]) [up i, up j]) s
      (nextSector (true, i) true (nextSector (true, j) true s)) :=
    SPath.two true true trivial trivial hs
  let qg : SPath (wd D (SKM.wt D ν [up r]) [up j, up i]) s
      (nextSector (true, i) true (nextSector (true, j) true s)) :=
    SPath.two true true trivial trivial rfl
  let pv : SPath (wd D ν [up r])
      (nextSector (true, i) true (nextSector (true, j) true s))
      (nextSector (true, r) true (nextSector (true, i) true (nextSector (true, j) true s))) :=
    .cons _ true _ trivial (.nil _)
  have hp : distinctPureProbePath (D := D) ν i j r s e = pg.append pv :=
    (pureProbePath_unique e (pg.append pv)).symm
  have hq : distinctPureProbePath (D := D) ν j i r s rfl = qg.append pv := rfl
  rw [hp, hq]
  refine (heq_of_eq (crossEntry_left (P.swappedGens c L) ν i j r pg qg pv Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  classical
  by_cases hij : i = j
  · subst j
    rw [swappedGens_cross_self]
    change HEq (P.preCrossSame i s ((P.step (true, r) true _ trivial).obj Z)) _
    exact heq_of_eq (P.preCrossSame_eq_scaled i s _)
  simp only [pureProbeScale, ite_eq_right hij, one_smul]
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hij]
  exact P.twoTwo_two_heq
    ⟨up i, SKM.wt D (SKM.wt D ν [up r]) [up j]⟩ ⟨up j, SKM.wt D ν [up r]⟩
    ⟨up j, SKM.wt D (SKM.wt D ν [up r]) [up i]⟩ ⟨up i, SKM.wt D ν [up r]⟩
    (P.crossNeEntry i j _ _ _ _) (t := s) true true true true
    trivial trivial trivial trivial hs rfl rfl _ _ HEq.rfl

theorem pureProbe_right_raw (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    {t : Sector I}
    (e : nextSector (true, r) true (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, j) true (nextSector (true, r) true (nextSector (true, i) true s)) = t)
    (Z : P.H t) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] j r []
      (distinctPureProbePath ν i j r s e) (distinctPureProbePath ν i r j s e') Z)
      ((P.step (true, i) true s trivial).map
        (pureProbeScale (D := D) j r •
          P.preCrossNe j r (nextSector (true, i) true s) (e.trans e'.symm) (e' ▸ Z))) := by
  subst e'
  refine (heq_of_eq (crossEntry_right (P.swappedGens c L) ν i j r true trivial
    (SPath.two true true trivial trivial e)
    (SPath.two true true trivial trivial rfl) Z)).trans ?_
  apply map_of_heq _ (P.pathFunctor_two_obj
    (c₁ := ⟨up j, SKM.wt D ν [up r]⟩) (c₂ := ⟨up r, SKM.wt D ν []⟩)
    (t := nextSector (true, i) true s)
    true true trivial trivial e Z _ (P.sector_heq e Z)) rfl
  classical
  by_cases hjr : j = r
  · subst r
    change HEq ((P.swappedGens c L).cross j j ν
      (SPath.two (c₁ := ⟨up j, SKM.wt D ν [up j]⟩) (c₂ := ⟨up j, ν⟩)
        true true trivial trivial rfl)
      (SPath.two true true trivial trivial rfl) Z) _
    refine (heq_of_eq (P.swappedGens_cross_self c L j ν _ _ Z)).trans ?_
    exact heq_of_eq (P.preCrossSame_eq_scaled j _ Z)
  simp only [pureProbeScale, ite_eq_right hjr, one_smul]
  dsimp only [swappedGens]
  refine (heq_of_eq (P.crossImage_ne c hjr ν
    (SPath.two true true trivial trivial e)
    (SPath.two true true trivial trivial rfl) Z)).trans ?_
  exact P.twoTwo_two_heq
    ⟨up j, SKM.wt D ν [up r]⟩ ⟨up r, ν⟩
    ⟨up r, SKM.wt D ν [up j]⟩ ⟨up j, ν⟩
    (P.crossNeEntry j r _ _ _ _) (t := nextSector (true, i) true s)
    true true true true trivial trivial trivial trivial e rfl rfl Z Z HEq.rfl

/-- Integer scaling respects equality of the source and target objects. -/
theorem pureProbe_zsmul_heq {C : Type*} [Category C] [Preadditive C]
    {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) (z : ℤ) : HEq (z • f) (z • g) := by
  subst hA hB
  cases h
  rfl

/-- Scaling commutes with the explicit terminal transport. -/
theorem scaledPreCrossNe_heq (i j : I) (t : Sector I)
    (hs : nextSector (true, j) true (nextSector (true, i) true t) =
      nextSector (true, i) true (nextSector (true, j) true t))
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true t)))
    (h₄ : -P.muP (nextSector (true, j) true t) + D.α i =
      -P.muP (nextSector (true, j) true (nextSector (true, i) true t))) :
    HEq (pureProbeScale (D := D) i j • P.preCrossNe i j t hs Z)
      (pureProbeScale (D := D) i j • probeCore P.T i j (P.muP_preE i t) (P.muP_preE j _)
        (P.muP_preE j t) h₄ (hs ▸ Z)) := by
  have he := eq_of_heq (P.preE_obj_heq i hs h₄ (P.muP_preE i _) Z)
  have hB := congrArg (P.step (true, j) true t trivial).obj he
  exact pureProbe_zsmul_heq rfl hB.symm (P.preCrossNe_heq i j t hs Z h₄) _

theorem pureProbe_normalized_heq (i j : I) (s : Sector I)
    (hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s))
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true s)))
    {a b b' d : X} {w : B}
    (ha : a = -P.muP s)
    (hb : b = -P.muP (nextSector (true, i) true s))
    (hb' : b' = -P.muP (nextSector (true, j) true s))
    (hd : d = -P.muP (nextSector (true, j) true (nextSector (true, i) true s)))
    (hw : w = P.W.obj (P.muM s))
    (hi : a + D.α i = b) (hij : b + D.α j = d)
    (hj : a + D.α j = b') (hji : b' + D.α i = d)
    (Z' : P.T.obj d ⟶ w) (hZ : HEq Z Z') :
    HEq (pureProbeScale (D := D) i j • P.preCrossNe i j s hs Z)
      (pureProbeScale (D := D) i j • probeCore P.T i j hi hij hj hji Z') := by
  subst a b b' d w
  have hz := (P.sector_heq hs Z).trans hZ
  have h := P.scaledPreCrossNe_heq i j s hs Z hji
  cases hz
  exact h

theorem pureProbe_left_core (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s))
    {t : Sector I}
    (e : nextSector (true, r) true (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, r) true (nextSector (true, i) true (nextSector (true, j) true s)) = t)
    (Z : P.H t) {b b' d f : X}
    (hb : b = -P.muP (nextSector (true, i) true s))
    (hb' : b' = -P.muP (nextSector (true, j) true s))
    (hd : d = -P.muP (nextSector (true, j) true (nextSector (true, i) true s)))
    (hf : f = -P.muP t)
    (hi : -P.muP s + D.α i = b) (hij' : b + D.α j = d)
    (hj : -P.muP s + D.α j = b') (hji : b' + D.α i = d)
    (hr : d + D.α r = f)
    (Z' : P.T.obj f ⟶ P.W.obj (P.muM t)) (hZ : HEq Z Z') :
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up r]
      (distinctPureProbePath ν i j r s e) (distinctPureProbePath ν j i r s e') Z)
      (pureProbeScale (D := D) i j • probeCore P.T i j hi hij' hj hji (P.T.E r hr ≫ Z')) := by
  refine (P.pureProbe_left_raw ν i j r s c L hs e e' Z).trans ?_
  have hm : P.muM t = P.muM s := by rw [← e']; rfl
  exact P.pureProbe_normalized_heq i j s hs _ rfl hb hb' hd
    (congrArg P.W.obj hm) hi hij' hj hji _
    (P.probeStep_obj_normalized r _ e' Z (hd.trans (congrArg (fun x => -P.muP x) hs))
      hf rfl hr Z' hZ)

theorem pureProbe_right_core (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    {t : Sector I}
    (e : nextSector (true, r) true (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, j) true (nextSector (true, r) true (nextSector (true, i) true s)) = t)
    (Z : P.H t) {b d d' f : X}
    (hb : b = -P.muP (nextSector (true, i) true s))
    (hd : d = -P.muP (nextSector (true, j) true (nextSector (true, i) true s)))
    (hd' : d' = -P.muP (nextSector (true, r) true (nextSector (true, i) true s)))
    (hf : f = -P.muP t)
    (hi : -P.muP s + D.α i = b) (hj : b + D.α j = d) (hr : b + D.α r = d')
    (hr' : d + D.α r = f) (hj' : d' + D.α j = f)
    (Z' : P.T.obj f ⟶ P.W.obj (P.muM t)) (hZ : HEq Z Z') :
    HEq (crossEntry (P.swappedGens c L) ν [up i] j r []
      (distinctPureProbePath ν i j r s e) (distinctPureProbePath ν i r j s e') Z)
      (P.T.E i hi ◁ (pureProbeScale (D := D) j r • probeCore P.T j r hj hr' hr hj' Z')) := by
  refine (P.pureProbe_right_raw ν i j r s c L e e' Z).trans ?_
  subst e' b
  have hA := P.probePair_obj_normalized j r (nextSector (true, i) true s) e Z
    rfl hd hf rfl hj hr' Z' hZ
  have hB := P.probePair_obj_normalized r j (nextSector (true, i) true s) rfl Z
    rfl hd' hf rfl hr hj' Z' hZ
  exact map_of_heq (P.step (true, i) true s trivial) (eq_of_heq hA) (eq_of_heq hB)
    (P.pureProbe_normalized_heq j r (nextSector (true, i) true s) e Z rfl hd hd'
      (hf.trans (congrArg (fun x => -P.muP x) e.symm)) rfl hj hr' hr hj' Z' hZ)

/-- The same three central integer coefficients preserve a braid. -/
theorem pureProbe_scale_braid {C : Type*} [Category C] [Preadditive C]
    {A B₁ B₂ C₁ C₂ E : C}
    (f : A ⟶ B₁) (g : B₁ ⟶ B₂) (h : B₂ ⟶ E)
    (l : A ⟶ C₁) (m : C₁ ⟶ C₂) (n : C₂ ⟶ E)
    (a b c : ℤ) (hb : f ≫ g ≫ h = l ≫ m ≫ n) :
    (a • f) ≫ (b • g) ≫ (c • h) = (c • l) ≫ (b • m) ≫ (a • n) := by
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul]
  rw [hb]
  congr 1
  ring

theorem pureProbe_braid_canonical (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hir : i ≠ r) {t : Sector I}
    (e : nextSector (true, r) true (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, r) true s)) = t)
    (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j r ν
      (distinctPureProbePath ν i j r s e) (distinctPureProbePath ν r j i s e') Z =
    braidRight (P.swappedGens c L) i j r ν
      (distinctPureProbePath ν i j r s e) (distinctPureProbePath ν r j i s e') Z := by
  classical
  subst e'
  let t := nextSector (true, i) true (nextSector (true, j) true (nextSector (true, r) true s))
  have e213 : nextSector (true, r) true (nextSector (true, i) true (nextSector (true, j) true s)) =
      t := by
    simp only [t, nextSector, add_comm, add_left_comm]
  have e231 : nextSector (true, i) true (nextSector (true, r) true (nextSector (true, j) true s)) =
      t := by
    simp only [t, nextSector, add_comm, add_left_comm]
  have e132 : nextSector (true, j) true (nextSector (true, r) true (nextSector (true, i) true s)) =
      t := by
    simp only [t, nextSector, add_comm, add_left_comm]
  have e312 : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, r) true s)) =
      t := by
    simp only [t, nextSector, add_comm, add_left_comm]
  let : Subsingleton (SPath (wd D ν [up j, up i, up r]) s t) :=
    ⟨fun p q => (pureProbePath_unique e213 p).trans (pureProbePath_unique e213 q).symm⟩
  let : Subsingleton (SPath (wd D ν [up j, up r, up i]) s t) :=
    ⟨fun p q => (pureProbePath_unique e231 p).trans (pureProbePath_unique e231 q).symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up r, up j]) s t) :=
    ⟨fun p q => (pureProbePath_unique e132 p).trans (pureProbePath_unique e132 q).symm⟩
  let : Subsingleton (SPath (wd D ν [up r, up i, up j]) s t) :=
    ⟨fun p q => (pureProbePath_unique e312 p).trans (pureProbePath_unique e312 q).symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up r]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up j, up r, up i]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up i, up r, up j]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up r, up i, up j]) s t)
  unfold braidLeft braidRight
  rw [Fintype.sum_subsingleton _ (distinctPureProbePath (D := D) ν j r i s e231),
    Fintype.sum_subsingleton _ (distinctPureProbePath (D := D) ν j i r s e213),
    Fintype.sum_subsingleton _ (distinctPureProbePath (D := D) ν r i j s e312),
    Fintype.sum_subsingleton _ (distinctPureProbePath (D := D) ν i r j s e132)]
  have hji := (P.muP_preE i (nextSector (true, j) true s)).trans
    (congrArg (fun x => -P.muP x) (pureProbe_swap j i s))
  have hri := (P.muP_preE i (nextSector (true, r) true s)).trans
    (congrArg (fun x => -P.muP x) (pureProbe_swap r i s))
  have hrj := (P.muP_preE j (nextSector (true, r) true s)).trans
    (congrArg (fun x => -P.muP x) (pureProbe_swap r j s))
  have hd12 := (P.muP_preE r (nextSector (true, j) true (nextSector (true, i) true s))).trans
    (congrArg (fun x => -P.muP x) e)
  have hd13 := (P.muP_preE j (nextSector (true, r) true (nextSector (true, i) true s))).trans
    (congrArg (fun x => -P.muP x) e132)
  have hd23 := (P.muP_preE i (nextSector (true, r) true (nextSector (true, j) true s))).trans
    (congrArg (fun x => -P.muP x) e231)
  have wji := congrArg (fun x => -P.muP x) (pureProbe_swap i j s)
  have wri := congrArg (fun x => -P.muP x) (pureProbe_swap i r s)
  have wrj := congrArg (fun x => -P.muP x) (pureProbe_swap j r s)
  exact probeHexagon_of_heq
    (eq_of_heq (P.distinctPureProbe_obj ν i j r s e Z rfl rfl rfl rfl
      (P.muP_preE i s) (P.muP_preE j _) hd12 Z HEq.rfl))
    (eq_of_heq (P.distinctPureProbe_obj ν j i r s e213 Z rfl wji rfl rfl
      (P.muP_preE j s) hji hd12 Z HEq.rfl))
    (eq_of_heq (P.distinctPureProbe_obj ν j r i s e231 Z rfl rfl rfl rfl
      (P.muP_preE j s) (P.muP_preE r _) hd23 Z HEq.rfl))
    (eq_of_heq (P.distinctPureProbe_obj ν r j i s rfl Z rfl wrj rfl rfl
      (P.muP_preE r s) hrj hd23 Z HEq.rfl))
    (eq_of_heq (P.distinctPureProbe_obj ν i r j s e132 Z rfl rfl rfl rfl
      (P.muP_preE i s) (P.muP_preE r _) hd13 Z HEq.rfl))
    (eq_of_heq (P.distinctPureProbe_obj ν r i j s e312 Z rfl wri rfl rfl
      (P.muP_preE r s) hri hd13 Z HEq.rfl))
    (P.pureProbe_left_core ν i j r s c L (pureProbe_swap i j s) e e213 Z
      rfl rfl rfl rfl (P.muP_preE i s) (P.muP_preE j _) (P.muP_preE j s) hji hd12 Z HEq.rfl)
    (P.pureProbe_right_core ν j i r s c L e213 e231 Z
      rfl wji rfl rfl (P.muP_preE j s) hji (P.muP_preE r _) hd12 hd23 Z HEq.rfl)
    (P.pureProbe_left_core ν j r i s c L
      (pureProbe_swap j r s) e231 rfl Z
      rfl rfl rfl rfl (P.muP_preE j s) (P.muP_preE r _) (P.muP_preE r s) hrj hd23 Z HEq.rfl)
    (P.pureProbe_right_core ν i j r s c L e e132 Z
      rfl rfl rfl rfl (P.muP_preE i s) (P.muP_preE j _) (P.muP_preE r _) hd12 hd13 Z HEq.rfl)
    (P.pureProbe_left_core ν i r j s c L (pureProbe_swap i r s) e132 e312 Z
      rfl rfl rfl rfl (P.muP_preE i s) (P.muP_preE r _) (P.muP_preE r s) hri hd13 Z HEq.rfl)
    (P.pureProbe_right_core ν r i j s c L e312 rfl Z
      rfl wri wrj rfl (P.muP_preE r s) hri hrj hd13 hd23 Z HEq.rfl)
    (by
      have h := P.distinctPureProbe_factor_braid i j r hir.symm
        (P.muP_preE i s) (P.muP_preE j s) (P.muP_preE r s)
        (P.muP_preE j _) hji (P.muP_preE r _) hri (P.muP_preE r _) hrj
        hd12 hd13 hd23 Z
      simp only [TwoSupercategory.whiskerLeft_zsmul (R := k)]
      exact pureProbe_scale_braid
        (C := P.T.obj (-P.muP s) ⟶ P.W.obj (P.muM s)) _ _ _ _ _ _ _ _ _ h)

/-- The non-correction braid on arbitrary paths with pure-probe endpoint.
Only the outer colours must differ; either adjacent pair may be equal. -/
theorem pureProbe_braid (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hir : i ≠ r) {t : Sector I}
    (e : nextSector (true, r) true (nextSector (true, j) true
      (nextSector (true, i) true s)) = t)
    (p : SPath (wd D ν [up i, up j, up r]) s t)
    (q : SPath (wd D ν [up r, up j, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j r ν p q Z =
      braidRight (P.swappedGens c L) i j r ν p q Z := by
  have e' : nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, r) true s)) = t := by
    rw [← e]
    simp only [nextSector, add_comm, add_left_comm]
  rw [pureProbePath_unique e p, pureProbePath_unique e' q]
  exact P.pureProbe_braid_canonical ν i j r s c L hir e e' Z

/-- The adjacent-equal `i i j` pure-probe braid on arbitrary source and target paths. -/
theorem adjacentPureProbe_iij (ν : X) (i j : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) {t : Sector I}
    (e : nextSector (true, j) true (nextSector (true, i) true
      (nextSector (true, i) true s)) = t)
    (p : SPath (wd D ν [up i, up i, up j]) s t)
    (q : SPath (wd D ν [up j, up i, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i i j ν p q Z =
      braidRight (P.swappedGens c L) i i j ν p q Z :=
  P.pureProbe_braid ν i i j s c L hij e p q Z

/-- The adjacent-equal `i j j` pure-probe braid on arbitrary source and target paths. -/
theorem adjacentPureProbe_ijj (ν : X) (i j : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) {t : Sector I}
    (e : nextSector (true, j) true (nextSector (true, j) true
      (nextSector (true, i) true s)) = t)
    (p : SPath (wd D ν [up i, up j, up j]) s t)
    (q : SPath (wd D ν [up j, up j, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j j ν p q Z =
      braidRight (P.swappedGens c L) i j j ν p q Z :=
  P.pureProbe_braid ν i j j s c L hij e p q Z

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
