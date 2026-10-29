/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctProbeSector

/-! # Right-whiskered distinct-colour probe braids

The factor braid underlying the all-probe sector of the swapped construction.
The reassociation lemmas allow the crossed strands and intermediate objects to
change. `ProbeReservoir.distinctPureProbe_braid` identifies all six canonical
sector-path crossing entries with the right-whiskered factor crossings, retaining
explicit terminal-sector transports. Path uniqueness for pairwise-distinct
colours collapses the intermediate sums. The only braid relation used is the
one supplied by the probe; no additional relation hypothesis is required.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {D : Datum I X} {Sc : Scalars D k}

/-- Reassociation of a right-whiskered triple. -/
def tripleRightIso {a b c d e : B} (E : a ⟶ b) (F : b ⟶ c) (G : c ⟶ d)
    (Z : d ⟶ e) : (E ≫ F ≫ G) ≫ Z ≅ E ≫ F ≫ G ≫ Z :=
  associator E (F ≫ G) Z ≪≫
    { hom := E ◁ (associator F G Z).hom
      inv := E ◁ (associator F G Z).inv
      hom_inv_id := by
        rw [← TwoSupercategory.whiskerLeft_comp (R := k), Iso.hom_inv_id,
          TwoSupercategory.whiskerLeft_id (R := k)]
      inv_hom_id := by
        rw [← TwoSupercategory.whiskerLeft_comp (R := k), Iso.inv_hom_id,
          TwoSupercategory.whiskerLeft_id (R := k)] }

/-- A crossing of the last two factors commutes with right reassociation. -/
theorem tripleRightIso_right {a b c c' d e : B} (E : a ⟶ b)
    (F : b ⟶ c) (G : c ⟶ d) (F' : b ⟶ c') (G' : c' ⟶ d)
    (Z : d ⟶ e) (y : F ≫ G ⟶ F' ≫ G') :
    E ◁ ((associator F G Z).inv ≫ y ▷ Z ≫ (associator F' G' Z).hom) =
      (tripleRightIso (k := k) E F G Z).inv ≫ (E ◁ y) ▷ Z ≫
        (tripleRightIso (k := k) E F' G' Z).hom := by
  rw [TwoSupercategory.whisker_assoc (R := k)]
  simp only [tripleRightIso, Iso.trans_hom, Iso.trans_inv, Category.assoc,
    Iso.inv_hom_id_assoc, TwoSupercategory.whiskerLeft_comp (R := k)]

/-- A crossing of the first two factors commutes with right reassociation.
The two intermediate objects and both crossed strands may differ. -/
theorem tripleRightIso_left {a b b' c d e : B}
    (E : a ⟶ b) (F : b ⟶ c) (E' : a ⟶ b') (F' : b' ⟶ c)
    (G : c ⟶ d) (Z : d ⟶ e) (x : E ≫ F ⟶ E' ≫ F') :
    (associator E F (G ≫ Z)).inv ≫ x ▷ (G ≫ Z) ≫
        (associator E' F' (G ≫ Z)).hom =
      (tripleRightIso (k := k) E F G Z).inv ≫
        ((associator E F G).inv ≫ x ▷ G ≫ (associator E' F' G).hom) ▷ Z ≫
        (tripleRightIso (k := k) E' F' G Z).hom := by
  have hpent (b : B) (E : a ⟶ b) (F : b ⟶ c) :
      (associator E F G).hom ▷ Z ≫ (tripleRightIso (k := k) E F G Z).hom =
        (associator (E ≫ F) G Z).hom ≫ (associator E F (G ≫ Z)).hom := by
    simpa only [tripleRightIso, Iso.trans_hom, Category.assoc] using
      TwoSupercategory.pentagon (R := k) E F G Z
  have hinv : (tripleRightIso (k := k) E F G Z).inv ≫
      (associator E F G).inv ▷ Z =
        (associator E F (G ≫ Z)).inv ≫ (associator (E ≫ F) G Z).inv := by
    apply (cancel_mono ((associator (E ≫ F) G Z).hom ≫
      (associator E F (G ≫ Z)).hom)).mp
    calc
      _ = 𝟙 _ := by
        rw [← hpent b E F]
        simp only [Category.assoc, TwoSupercategory.inv_hom_whiskerRight_assoc (R := k),
          Iso.inv_hom_id]
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  rw [TwoSupercategory.whiskerRight_comp (R := k),
    TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.comp_whiskerRight (R := k)]
  simp only [Category.assoc]
  rw [← Category.assoc _ ((associator E F G).inv ▷ Z), hinv,
    hpent b' E' F']
  simp only [Category.assoc]

include k in
/-- A coloured braid survives right whiskering and reassociation. All six
intermediate triples may differ; no crossings are required to be invertible. -/
theorem whisker_braid_distinct {a b₁ b₂ b₃ c₁₂ c₁₃ c₂₃ d e : B}
    (E₁ : a ⟶ b₁) (E₂ : a ⟶ b₂) (E₃ : a ⟶ b₃)
    (F₁₂ : b₁ ⟶ c₁₂) (F₂₁ : b₂ ⟶ c₁₂)
    (F₁₃ : b₁ ⟶ c₁₃) (F₃₁ : b₃ ⟶ c₁₃)
    (F₂₃ : b₂ ⟶ c₂₃) (F₃₂ : b₃ ⟶ c₂₃)
    (G₁₂ : c₁₂ ⟶ d) (G₁₃ : c₁₃ ⟶ d) (G₂₃ : c₂₃ ⟶ d)
    (Z : d ⟶ e)
    (x₁₂ : E₁ ≫ F₁₂ ⟶ E₂ ≫ F₂₁)
    (x₁₃ : E₁ ≫ F₁₃ ⟶ E₃ ≫ F₃₁)
    (x₂₃ : E₂ ≫ F₂₃ ⟶ E₃ ≫ F₃₂)
    (y₁₂ : F₃₁ ≫ G₁₃ ⟶ F₃₂ ≫ G₂₃)
    (y₁₃ : F₂₁ ≫ G₁₂ ⟶ F₂₃ ≫ G₂₃)
    (y₂₃ : F₁₂ ≫ G₁₂ ⟶ F₁₃ ≫ G₁₃)
    (hb : ((associator E₁ F₁₂ G₁₂).inv ≫ x₁₂ ▷ G₁₂ ≫ (associator E₂ F₂₁ G₁₂).hom) ≫
      E₂ ◁ y₁₃ ≫
      ((associator E₂ F₂₃ G₂₃).inv ≫ x₂₃ ▷ G₂₃ ≫ (associator E₃ F₃₂ G₂₃).hom) =
      E₁ ◁ y₂₃ ≫
      ((associator E₁ F₁₃ G₁₃).inv ≫ x₁₃ ▷ G₁₃ ≫ (associator E₃ F₃₁ G₁₃).hom) ≫
      E₃ ◁ y₁₂) :
    ((associator E₁ F₁₂ (G₁₂ ≫ Z)).inv ≫ x₁₂ ▷ (G₁₂ ≫ Z) ≫ (associator E₂ F₂₁ (G₁₂ ≫ Z)).hom) ≫
      E₂ ◁ ((associator F₂₁ G₁₂ Z).inv ≫ y₁₃ ▷ Z ≫ (associator F₂₃ G₂₃ Z).hom) ≫
      ((associator E₂ F₂₃ (G₂₃ ≫ Z)).inv ≫ x₂₃ ▷ (G₂₃ ≫ Z) ≫ (associator E₃ F₃₂ (G₂₃ ≫ Z)).hom) =
      E₁ ◁ ((associator F₁₂ G₁₂ Z).inv ≫ y₂₃ ▷ Z ≫ (associator F₁₃ G₁₃ Z).hom) ≫
      ((associator E₁ F₁₃ (G₁₃ ≫ Z)).inv ≫ x₁₃ ▷ (G₁₃ ≫ Z) ≫ (associator E₃ F₃₁ (G₁₃ ≫ Z)).hom) ≫
      E₃ ◁ ((associator F₃₁ G₁₃ Z).inv ≫ y₁₂ ▷ Z ≫ (associator F₃₂ G₂₃ Z).hom) := by
  rw [tripleRightIso_left (k := k), tripleRightIso_left (k := k), tripleRightIso_left (k := k),
    tripleRightIso_right (k := k), tripleRightIso_right (k := k), tripleRightIso_right (k := k)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [TwoSupercategory.comp_whiskerRight (R := k), Category.assoc] using
    congrArg (fun f => (tripleRightIso (k := k) E₁ F₁₂ G₁₂ Z).inv ≫ f ▷ Z ≫
      (tripleRightIso (k := k) E₃ F₃₂ G₂₃ Z).hom) hb


namespace ProbeReservoir
/-- The probe factor's distinct-colour braid, right-whiskered and reassociated.
This is the factor identity before identifying sector-path transports. -/
theorem distinctPureProbe_factor_braid (P : ProbeReservoir k B D Sc)
    (i j r : I) (hri_ne : r ≠ i) {a bi bj br cij cir cjr d : X}
    (hi : a + D.α i = bi) (hj : a + D.α j = bj) (hr : a + D.α r = br)
    (hij : bi + D.α j = cij) (hji : bj + D.α i = cij)
    (hir : bi + D.α r = cir) (hri : br + D.α i = cir)
    (hjr : bj + D.α r = cjr) (hrj : br + D.α j = cjr)
    (hd12 : cij + D.α r = d) (hd13 : cir + D.α j = d)
    (hd23 : cjr + D.α i = d) {e : B} (Z : P.T.obj d ⟶ e) :
    ((associator (P.T.E i hi) (P.T.E j hij) ((P.T.E r hd12) ≫ Z)).inv ≫ (P.T.cross j i hi hij hj
        hji) ▷ ((P.T.E r hd12) ≫ Z) ≫ (associator (P.T.E j hj) (P.T.E i hji) ((P.T.E r hd12) ≫
        Z)).hom) ≫
      (P.T.E j hj) ◁ ((associator (P.T.E i hji) (P.T.E r hd12) Z).inv ≫ (P.T.cross r i hji hd12
          hjr hd23) ▷ Z ≫ (associator (P.T.E r hjr) (P.T.E i hd23) Z).hom) ≫
      ((associator (P.T.E j hj) (P.T.E r hjr) ((P.T.E i hd23) ≫ Z)).inv ≫ (P.T.cross r j hj hjr hr
          hrj) ▷ ((P.T.E i hd23) ≫ Z) ≫ (associator (P.T.E r hr) (P.T.E j hrj) ((P.T.E i hd23) ≫
          Z)).hom) =
      (P.T.E i hi) ◁ ((associator (P.T.E j hij) (P.T.E r hd12) Z).inv ≫ (P.T.cross r j hij hd12
          hir hd13) ▷ Z ≫ (associator (P.T.E r hir) (P.T.E j hd13) Z).hom) ≫
      ((associator (P.T.E i hi) (P.T.E r hir) ((P.T.E j hd13) ≫ Z)).inv ≫ (P.T.cross r i hi hir hr
          hri) ▷ ((P.T.E j hd13) ≫ Z) ≫ (associator (P.T.E r hr) (P.T.E i hri) ((P.T.E j hd13) ≫
          Z)).hom) ≫
      (P.T.E r hr) ◁ ((associator (P.T.E i hri) (P.T.E j hd13) Z).inv ≫ (P.T.cross j i hri hd13
          hrj hd23) ▷ Z ≫ (associator (P.T.E j hrj) (P.T.E i hd23) Z).hom) := by
  apply whisker_braid_distinct (k := k)
  simpa only [Category.assoc] using
    (P.probeRel.braid r j i (fun h => hri_ne h.1)
      hi hj hr hij hir hji hjr hri hrj hd12 hd13 hd23).symm

variable [∀ a b : B, PiSupercategory k (a ⟶ b)]
variable (P : ProbeReservoir k B D Sc)

/-- The all-probe path with its terminal equality retained. -/
def distinctPureProbePath (ν : X) (i j r : I) (s : Sector I) {t : Sector I}
    (e : nextSector (true, r) true (nextSector (true, j) true
      (nextSector (true, i) true s)) = t) :
    SPath (wd D ν [up i, up j, up r]) s t :=
  SPath.three true true true trivial trivial trivial e

/-- Normalize the weights and terminal object of a probe crossing. -/
theorem preCrossNe_normalized_heq (i j : I) (s : Sector I)
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
    HEq (P.preCrossNe i j s hs Z)
      (probeCore P.T i j hi hij hj hji Z') := by
  subst a b b' d w
  have hz := (P.sector_heq hs Z).trans hZ
  have h := P.preCrossNe_heq i j s hs Z hji
  cases hz
  exact h

/-- Evaluation of a probe triple with normalized weight vertices. -/
theorem distinctPureProbe_obj (ν : X) (i j r : I) (s : Sector I) {t : Sector I}
    (e : nextSector (true, r) true (nextSector (true, j) true
      (nextSector (true, i) true s)) = t) (Z : P.H t)
    {b d f : X} {w : B}
    (hb : b = -P.muP (nextSector (true, i) true s))
    (hd : d = -P.muP (nextSector (true, j) true (nextSector (true, i) true s)))
    (hf : f = -P.muP t) (hw : w = P.W.obj (P.muM t))
    (hi : -P.muP s + D.α i = b) (hj : b + D.α j = d) (hr : d + D.α r = f)
    (Z' : P.T.obj f ⟶ w) (hZ : HEq Z Z') :
    HEq ((P.pathFunctor (distinctPureProbePath (D := D) ν i j r s e)).obj Z)
      (P.T.E i hi ≫ P.T.E j hj ≫ P.T.E r hr ≫ Z') := by
  subst e b d f w
  cases hZ
  rfl

/-- The left edge on an all-probe triple, before weight normalization. -/
theorem distinctPureProbe_left_raw (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hs : nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s))
    {t : Sector I}
    (e : nextSector (true, r) true (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, r) true (nextSector (true, i) true (nextSector (true, j) true s)) = t)
    (Z : P.H t) :
    HEq (crossEntry (P.swappedGens c L) ν [] i j [up r]
      (distinctPureProbePath ν i j r s e) (distinctPureProbePath ν j i r s e') Z)
      (P.preCrossNe i j s hs ((P.step (true, r) true _ trivial).obj (e' ▸ Z))) := by
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
    path_eq_three_distinct hij hir hjr _ _
  have hq : distinctPureProbePath (D := D) ν j i r s rfl = qg.append pv := rfl
  rw [hp, hq]
  refine (heq_of_eq (crossEntry_left (P.swappedGens c L) ν i j r pg qg pv Z)).trans ?_
  refine (sandwich_heq _ _ _).trans ?_
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hij]
  exact P.twoTwo_two_heq
    ⟨up i, SKM.wt D (SKM.wt D ν [up r]) [up j]⟩ ⟨up j, SKM.wt D ν [up r]⟩
    ⟨up j, SKM.wt D (SKM.wt D ν [up r]) [up i]⟩ ⟨up i, SKM.wt D ν [up r]⟩
    (P.crossNeEntry i j _ _ _ _) (t := s) true true true true
    trivial trivial trivial trivial hs rfl rfl _ _ HEq.rfl

/-- The right edge on an all-probe triple, retaining its terminal transport. -/
theorem distinctPureProbe_right_raw (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hjr : j ≠ r)
    {t : Sector I}
    (e : nextSector (true, r) true (nextSector (true, j) true (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, j) true (nextSector (true, r) true (nextSector (true, i) true s)) = t)
    (Z : P.H t) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] j r []
      (distinctPureProbePath ν i j r s e) (distinctPureProbePath ν i r j s e') Z)
      ((P.step (true, i) true s trivial).map
        (P.preCrossNe j r (nextSector (true, i) true s) (e.trans e'.symm) (e' ▸ Z))) := by
  subst e'
  refine (heq_of_eq (crossEntry_right (P.swappedGens c L) ν i j r true trivial
    (SPath.two true true trivial trivial e)
    (SPath.two true true trivial trivial rfl) Z)).trans ?_
  apply map_of_heq _ (P.pathFunctor_two_obj
    (c₁ := ⟨up j, SKM.wt D ν [up r]⟩) (c₂ := ⟨up r, SKM.wt D ν []⟩)
    (t := nextSector (true, i) true s)
    true true trivial trivial e Z _ (P.sector_heq e Z)) rfl
  dsimp only [swappedGens]
  refine (heq_of_eq (P.crossImage_ne c hjr ν
    (SPath.two true true trivial trivial e)
    (SPath.two true true trivial trivial rfl) Z)).trans ?_
  exact P.twoTwo_two_heq
    ⟨up j, SKM.wt D ν [up r]⟩ ⟨up r, ν⟩
    ⟨up r, SKM.wt D ν [up j]⟩ ⟨up j, ν⟩
    (P.crossNeEntry j r _ _ _ _) (t := nextSector (true, i) true s)
    true true true true trivial trivial trivial trivial e rfl rfl Z Z HEq.rfl

/-- A single probe step with freely chosen, equal weight vertices. -/
theorem probeStep_obj_normalized (i : I) (s : Sector I) {t : Sector I}
    (e : nextSector (true, i) true s = t) (Z : P.H t)
    {a b : X} {w : B} (ha : a = -P.muP s) (hb : b = -P.muP t)
    (hw : w = P.W.obj (P.muM t)) (hi : a + D.α i = b)
    (Z' : P.T.obj b ⟶ w) (hZ : HEq Z Z') :
    HEq ((P.step (true, i) true s trivial).obj (e ▸ Z)) (P.T.E i hi ≫ Z') := by
  subst e a b w
  cases hZ
  rfl

/-- The left all-probe edge as a normalized factor crossing. -/
theorem distinctPureProbe_left_core (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
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
      (probeCore P.T i j hi hij' hj hji (P.T.E r hr ≫ Z')) := by
  refine (P.distinctPureProbe_left_raw ν i j r s c L hij hir hjr hs e e' Z).trans ?_
  have hm : P.muM t = P.muM s := by rw [← e']; rfl
  exact P.preCrossNe_normalized_heq i j s hs _ rfl hb hb' hd
    (congrArg P.W.obj hm) hi hij' hj hji _
    (P.probeStep_obj_normalized r _ e' Z (hd.trans (congrArg (fun x => -P.muP x) hs))
      hf rfl hr Z' hZ)

/-- Evaluation of two probe steps with normalized vertices. -/
theorem probePair_obj_normalized (i j : I) (s : Sector I) {t : Sector I}
    (e : nextSector (true, j) true (nextSector (true, i) true s) = t) (Z : P.H t)
    {a b d : X} {w : B} (ha : a = -P.muP s)
    (hb : b = -P.muP (nextSector (true, i) true s)) (hd : d = -P.muP t)
    (hw : w = P.W.obj (P.muM t)) (hi : a + D.α i = b) (hj : b + D.α j = d)
    (Z' : P.T.obj d ⟶ w) (hZ : HEq Z Z') :
    HEq ((P.step (true, i) true s trivial).obj
      ((P.step (true, j) true _ trivial).obj (e ▸ Z)))
      (P.T.E i hi ≫ P.T.E j hj ≫ Z') := by
  subst e a b d w
  cases hZ
  rfl

/-- The right all-probe edge as a normalized whiskered factor crossing. -/
theorem distinctPureProbe_right_core (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hjr : j ≠ r)
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
      (P.T.E i hi ◁ probeCore P.T j r hj hr' hr hj' Z') := by
  refine (P.distinctPureProbe_right_raw ν i j r s c L hjr e e' Z).trans ?_
  subst e' b
  have hA := P.probePair_obj_normalized j r (nextSector (true, i) true s) e Z
    rfl hd hf rfl hj hr' Z' hZ
  have hB := P.probePair_obj_normalized r j (nextSector (true, i) true s) rfl Z
    rfl hd' hf rfl hr hj' Z' hZ
  exact map_of_heq (P.step (true, i) true s trivial) (eq_of_heq hA) (eq_of_heq hB)
    (P.preCrossNe_normalized_heq j r (nextSector (true, i) true s) e Z rfl hd hd'
      (hf.trans (congrArg (fun x => -P.muP x) e.symm)) rfl hj hr' hr hj' Z' hZ)

/-- Transport a six-edge braid along equalities of all six vertices. -/
theorem probeHexagon_of_heq {C : Type*} [Category C]
    {A B₁ B₂ D₀ C₁ C₂ A' B₁' B₂' D' C₁' C₂' : C}
    (hA : A = A') (hB₁ : B₁ = B₁') (hB₂ : B₂ = B₂') (hD : D₀ = D')
    (hC₁ : C₁ = C₁') (hC₂ : C₂ = C₂')
    {f : A ⟶ B₁} {g : B₁ ⟶ B₂} {h : B₂ ⟶ D₀}
    {l : A ⟶ C₁} {m : C₁ ⟶ C₂} {n : C₂ ⟶ D₀}
    {f' : A' ⟶ B₁'} {g' : B₁' ⟶ B₂'} {h' : B₂' ⟶ D'}
    {l' : A' ⟶ C₁'} {m' : C₁' ⟶ C₂'} {n' : C₂' ⟶ D'}
    (ef : HEq f f') (eg : HEq g g') (eh : HEq h h')
    (el : HEq l l') (em : HEq m m') (en : HEq n n')
    (hb : f' ≫ g' ≫ h' = l' ≫ m' ≫ n') : (f ≫ g) ≫ h = (l ≫ m) ≫ n := by
  subst hA hB₁ hB₂ hD hC₁ hC₂
  cases ef; cases eg; cases eh; cases el; cases em; cases en
  simpa only [Category.assoc] using hb

/-- Commuting two probe increments. -/
theorem pureProbe_swap (i j : I) (s : Sector I) :
    nextSector (true, j) true (nextSector (true, i) true s) =
      nextSector (true, i) true (nextSector (true, j) true s) := by
  simp only [nextSector, add_right_comm]

/-- The canonical all-probe sector of the pairwise-distinct braid relation. -/
theorem distinctPureProbe_braid (ν : X) (i j r : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r) {t : Sector I}
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
    ⟨path_eq_three_distinct hij.symm hjr hir⟩
  let : Subsingleton (SPath (wd D ν [up j, up r, up i]) s t) :=
    ⟨path_eq_three_distinct hjr hij.symm hir.symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up r, up j]) s t) :=
    ⟨path_eq_three_distinct hir hij hjr.symm⟩
  let : Subsingleton (SPath (wd D ν [up r, up i, up j]) s t) :=
    ⟨path_eq_three_distinct hir.symm hjr.symm hij⟩
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
    (P.distinctPureProbe_left_core ν i j r s c L hij hir hjr (pureProbe_swap i j s) e e213 Z
      rfl rfl rfl rfl (P.muP_preE i s) (P.muP_preE j _) (P.muP_preE j s) hji hd12 Z HEq.rfl)
    (P.distinctPureProbe_right_core ν j i r s c L hir e213 e231 Z
      rfl wji rfl rfl (P.muP_preE j s) hji (P.muP_preE r _) hd12 hd23 Z HEq.rfl)
    (P.distinctPureProbe_left_core ν j r i s c L hjr hij.symm hir.symm
      (pureProbe_swap j r s) e231 rfl Z
      rfl rfl rfl rfl (P.muP_preE j s) (P.muP_preE r _) (P.muP_preE r s) hrj hd23 Z HEq.rfl)
    (P.distinctPureProbe_right_core ν i j r s c L hjr e e132 Z
      rfl rfl rfl rfl (P.muP_preE i s) (P.muP_preE j _) (P.muP_preE r _) hd12 hd13 Z HEq.rfl)
    (P.distinctPureProbe_left_core ν i r j s c L hir hij hjr.symm (pureProbe_swap i r s) e132 e312 Z
      rfl rfl rfl rfl (P.muP_preE i s) (P.muP_preE r _) (P.muP_preE r s) hri hd13 Z HEq.rfl)
    (P.distinctPureProbe_right_core ν r i j s c L hij e312 rfl Z
      rfl wri wrj rfl (P.muP_preE r s) hri hrj hd13 hd23 Z HEq.rfl)
    (P.distinctPureProbe_factor_braid i j r hir.symm
      (P.muP_preE i s) (P.muP_preE j s) (P.muP_preE r s)
      (P.muP_preE j _) hji (P.muP_preE r _) hri (P.muP_preE r _) hrj
      hd12 hd13 hd23 Z)

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
