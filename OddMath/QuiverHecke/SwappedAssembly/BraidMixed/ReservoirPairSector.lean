/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ProbePairSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.InterchangePostPair
/-! # A two-reservoir mixed-colour sector braid

`reservoirPair_braid` proves the `PᵢRᵣRᵣ → RᵣRᵣPᵢ` entry of the
non-correction braid relation for `i ≠ r`. The finite sums have unique
intermediate sector paths. The crossing entries are evaluated with
`BraidEntries`, retaining its endpoint casts and the prescribed shifted
reservoir crossing. The repeated reservoir colour permits the same-colour
specialization `homMixedInterchange_postPair_conj` of the post-pair triangle.

The two mixed entries are the coefficient-one `PR → RP` direction of
`crossNeEntry`. No inverse coefficient hypothesis or invertibility of Q
is needed. Reverse Q-weighted directions, unequal reservoir colours and
other `CrossBraid` fields are not established by this module.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)
/-- The prescribed same-colour reservoir crossing passes through two mixed interchanges. -/
theorem postCrossSame_mixedJ_pair_ne (i r : I) (s : Sector I)
    (hv : StepValid (true, r) false s)
    (hw : StepValid (true, r) false (nextSector (true, r) false s))
    (Z : P.H (nextSector (true, r) false (nextSector (true, r) false
      (nextSector (true, i) true s)))) :
    (P.step (true, i) true s trivial).map
          (P.postCrossSame r (nextSector (true, i) true s) hv hw Z) ≫
        (P.mixedJ i r s hv ((P.step (true, r) false
          (nextSector (true, r) false (nextSector (true, i) true s)) hw).obj Z)).hom ≫
        (P.step (true, r) false s hv).map (P.mixedJ i r (nextSector (true, r) false s) hw Z).hom =
      (P.mixedJ i r s hv ((P.step (true, r) false
          (nextSector (true, r) false (nextSector (true, i) true s)) hw).obj Z)).hom ≫
        (P.step (true, r) false s hv).map (P.mixedJ i r (nextSector (true, r) false s) hw Z).hom ≫
        P.postCrossSame r s hv hw ((P.step (true, i) true _ trivial).obj Z) := by
  rw [postCrossSame_eq, postCrossSame_eq]
  exact homMixedInterchange_postPair_conj (k := k) _ _ _ _ _ _ _

variable (ν : X) (i r : I) (s : Sector I)
  (hv : StepValid (true, r) false s)
  (hw : StepValid (true, r) false (nextSector (true, r) false s))
/-- Source path `PᵢRᵣRᵣ`. -/
def reservoirPairSource : SPath (wd D ν [up i, up r, up r]) s
    (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s))) :=
  .cons _ true s trivial (.cons _ false _ hv (.cons _ false _ hw (.nil _)))
/-- Intermediate path `RᵣPᵢRᵣ`. -/
def reservoirPairMiddle : SPath (wd D ν [up r, up i, up r]) s
    (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s))) :=
  .cons _ false s hv (.cons _ true _ trivial (.cons _ false _ hw (.nil _)))
/-- Target path `RᵣRᵣPᵢ`. -/
def reservoirPairTarget : SPath (wd D ν [up r, up r, up i]) s
    (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s))) :=
  .cons _ false s hv (.cons _ false _ hw (.cons _ true _ trivial (.nil _)))
omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
theorem reservoirPairSource_unique (hir : i ≠ r)
    (p : SPath (wd D ν [up i, up r, up r]) s
      (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s)))) :
    p = reservoirPairSource ν i r s hv hw := by
  suffices aux : ∀ t (p : SPath (wd D ν [up i, up r, up r]) s t)
      (h : t = nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s))),
      h ▸ p = reservoirPairSource ν i r s hv hw from aux _ p rfl
  intro t p h
  cases p with
  | cons _ a _ ha p =>
    cases p with
    | cons _ b _ hb p =>
      cases p with
      | cons _ c _ hc p =>
        cases p
        have hi := congrArg (fun x : Sector I => x.1 i) h
        have hr := congrArg (fun x : Sector I => x.1 r) h
        cases a <;> cases b <;> cases c <;>
          first | rfl | (exfalso; simp [nextSector, hir, Ne.symm hir] at hi hr <;> omega)

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
theorem reservoirPairMiddle_unique (hir : i ≠ r)
    (p : SPath (wd D ν [up r, up i, up r]) s
      (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s)))) :
    p = reservoirPairMiddle ν i r s hv hw := by
  suffices aux : ∀ t (p : SPath (wd D ν [up r, up i, up r]) s t)
      (h : t = nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s))),
      h ▸ p = reservoirPairMiddle ν i r s hv hw from aux _ p rfl
  intro t p h
  cases p with
  | cons _ a _ ha p =>
    cases p with
    | cons _ b _ hb p =>
      cases p with
      | cons _ c _ hc p =>
        cases p
        have hi := congrArg (fun x : Sector I => x.1 i) h
        have hr := congrArg (fun x : Sector I => x.1 r) h
        cases a <;> cases b <;> cases c <;>
          first | rfl | (exfalso; simp [nextSector, hir, Ne.symm hir] at hi hr <;> omega)

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
theorem reservoirPairTarget_unique (hir : i ≠ r)
    (p : SPath (wd D ν [up r, up r, up i]) s
      (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s)))) :
    p = reservoirPairTarget ν i r s hv hw := by
  suffices aux : ∀ t (p : SPath (wd D ν [up r, up r, up i]) s t)
      (h : t = nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s))),
      h ▸ p = reservoirPairTarget ν i r s hv hw from aux _ p rfl
  intro t p h
  cases p with
  | cons _ a _ ha p =>
    cases p with
    | cons _ b _ hb p =>
      cases p with
      | cons _ c _ hc p =>
        cases p
        have hi := congrArg (fun x : Sector I => x.1 i) h
        have hr := congrArg (fun x : Sector I => x.1 r) h
        cases a <;> cases b <;> cases c <;>
          first | rfl | (exfalso; simp [nextSector, hir, Ne.symm hir] at hi hr <;> omega)

variable (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (Z : P.H (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s))))
theorem reservoirPair_right_same :
    crossEntry (P.swappedGens c L) ν [up i] r r []
      (reservoirPairSource ν i r s hv hw) (reservoirPairSource ν i r s hv hw) Z =
    (P.step (true, i) true s trivial).map
      (P.postCrossSame r (nextSector (true, i) true s) hv hw Z) := by
  refine (crossEntry_right (P.swappedGens c L) ν i r r true trivial
    (.cons _ false _ hv (.cons _ false _ hw (.nil _)))
    (.cons _ false _ hv (.cons _ false _ hw (.nil _))) Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

theorem reservoirPair_left_mixed (hir : i ≠ r) :
    crossEntry (P.swappedGens c L) ν [] i r [up r]
      (reservoirPairSource ν i r s hv hw) (reservoirPairMiddle ν i r s hv hw) Z =
    (P.mixedJ i r s hv ((P.step (true, r) false
      (nextSector (true, r) false (nextSector (true, i) true s)) hw).obj Z)).hom := by
  refine (crossEntry_left (P.swappedGens c L) ν i r r
    (.cons _ true s trivial (.cons _ false _ hv (.nil _)))
    (.cons _ false s hv (.cons _ true _ trivial (.nil _)))
    (.cons _ false _ hw (.nil _)) Z).trans ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hir]
  rfl

theorem reservoirPair_right_mixed (hir : i ≠ r) :
    crossEntry (P.swappedGens c L) ν [up r] i r []
      (reservoirPairMiddle ν i r s hv hw) (reservoirPairTarget ν i r s hv hw) Z =
    (P.step (true, r) false s hv).map (P.mixedJ i r (nextSector (true, r) false s) hw Z).hom := by
  refine (crossEntry_right (P.swappedGens c L) ν r i r false hv
    (.cons _ true _ trivial (.cons _ false _ hw (.nil _)))
    (.cons _ false _ hw (.cons _ true _ trivial (.nil _))) Z).trans ?_
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hir]
  rfl

theorem reservoirPair_left_same :
    crossEntry (P.swappedGens c L) ν [] r r [up i]
      (reservoirPairTarget ν i r s hv hw) (reservoirPairTarget ν i r s hv hw) Z =
    P.postCrossSame r s hv hw ((P.step (true, i) true _ trivial).obj Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν r r i
    (.cons _ false s hv (.cons _ false _ hw (.nil _)))
    (.cons _ false s hv (.cons _ false _ hw (.nil _)))
    (.cons _ true _ trivial (.nil _)) Z).trans ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [swappedGens_cross_self]
  rfl

/-- The non-correction braid entry `PᵢRᵣRᵣ → RᵣRᵣPᵢ` for `i ≠ r`. -/
theorem reservoirPair_braid (hir : i ≠ r) :
    braidLeft (P.swappedGens c L) i r r ν
      (reservoirPairSource ν i r s hv hw) (reservoirPairTarget ν i r s hv hw) Z =
    braidRight (P.swappedGens c L) i r r ν
      (reservoirPairSource ν i r s hv hw) (reservoirPairTarget ν i r s hv hw) Z := by
  classical
  let : Subsingleton (SPath (wd D ν [up i, up r, up r]) s
      (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s)))) :=
    ⟨fun p q => (reservoirPairSource_unique ν i r s hv hw hir p).trans
      (reservoirPairSource_unique ν i r s hv hw hir q).symm⟩
  let : Subsingleton (SPath (wd D ν [up r, up i, up r]) s
      (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s)))) :=
    ⟨fun p q => (reservoirPairMiddle_unique ν i r s hv hw hir p).trans
      (reservoirPairMiddle_unique ν i r s hv hw hir q).symm⟩
  let : Subsingleton (SPath (wd D ν [up r, up r, up i]) s
      (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s)))) :=
    ⟨fun p q => (reservoirPairTarget_unique ν i r s hv hw hir p).trans
      (reservoirPairTarget_unique ν i r s hv hw hir q).symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up i, up r, up r]) s
    (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s))))
  let := Fintype.ofFinite (SPath (wd D ν [up r, up i, up r]) s
    (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s))))
  let := Fintype.ofFinite (SPath (wd D ν [up r, up r, up i]) s
    (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s))))
  unfold braidLeft braidRight
  rw [Fintype.sum_subsingleton _ (reservoirPairTarget (D := D) ν i r s hv hw),
    Fintype.sum_subsingleton _ (reservoirPairMiddle (D := D) ν i r s hv hw),
    Fintype.sum_subsingleton _ (reservoirPairMiddle (D := D) ν i r s hv hw),
    Fintype.sum_subsingleton _ (reservoirPairSource (D := D) ν i r s hv hw)]
  rw [reservoirPair_left_same, reservoirPair_right_mixed _ _ _ _ _ _ _ _ _ _ hir,
    reservoirPair_left_mixed _ _ _ _ _ _ _ _ _ _ hir, reservoirPair_right_same]
  simpa only [Category.assoc] using (P.postCrossSame_mixedJ_pair_ne i r s hv hw Z).symm

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
