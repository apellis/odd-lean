/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.InterchangePair
import OddMath.QuiverHecke.SwappedAssembly.BraidEntries
import OddMath.QuiverHecke.SwappedAssembly.QuadNe
/-! # A two-probe mixed-colour sector braid

The `PᵢPᵢRᵣ → RᵣPᵢPᵢ` entry of the non-correction braid relation,
for `i ≠ r`, in the swapped assembly. `probePair_braid` is an entry of
`CrossBraid.braid`, not a construction of that structure.

The intermediate sector paths are unique. The four crossing entries reduce
using `BraidEntries`, including its endpoint casts, to the prescribed
same-colour probe crossing and the two `PR → RP` entries `mixedJ.hom`.
These directions have coefficient one in `crossNeEntry`; the reverse
`RP → PR` entries still contain `mixedQ` and are not covered here.
The same-colour crossing retains its `-koszulSign` normalization.
The universal two-probe triangle supplies the final equality. No assumption
on `CrossCoeff.IsInverse`, or on a parameter polynomial being invertible,
is used. Other sector entries and the correction cases remain open.
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
/-- The prescribed same-colour probe crossing passes through two mixed interchanges. -/
theorem preCrossSame_mixedJ_pair_ne (i r : I) (s : Sector I)
    (hR : StepValid (true, r) false s)
    (Z : P.H (nextSector (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)))) :
    P.preCrossSame i s ((P.step (true, r) false (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z) ≫
      (P.step (true, i) true s trivial).map
        (P.mixedJ i r (nextSector (true, i) true s) hR Z).hom ≫
      (P.mixedJ i r s hR ((P.step (true, i) true _ trivial).obj Z)).hom =
    (P.step (true, i) true s trivial).map
        (P.mixedJ i r (nextSector (true, i) true s) hR Z).hom ≫
      (P.mixedJ i r s hR ((P.step (true, i) true _ trivial).obj Z)).hom ≫
      (P.step (true, r) false s hR).map (P.preCrossSame i (nextSector (true, r) false s) Z) := by
  simp only [preCrossSame, mixedJ, step, homContentPreE, homContentPostE, Functor.comp_map,
    homPre, homPost, Functor.map_zsmul, Linear.smul_comp, Linear.comp_smul,
    TwoSupercategory.zsmul_whiskerRight (R := k)]
  congr 1
  exact P.T.cross_mixedInterchange_pair i i r s.1 _ _ _ _ Z _

variable (ν : X) (i r : I) (s : Sector I) (hR : StepValid (true, r) false s)
/-- Source path `PᵢPᵢRᵣ`. -/
def probePairSource : SPath (wd D ν [up i, up i, up r]) s
    (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))) :=
  .cons _ true s trivial (.cons _ true _ trivial (.cons _ false _ hR (.nil _)))
/-- Intermediate path `PᵢRᵣPᵢ`. -/
def probePairMiddle : SPath (wd D ν [up i, up r, up i]) s
    (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))) :=
  .cons _ true s trivial (.cons _ false _ hR (.cons _ true _ trivial (.nil _)))
/-- Target path `RᵣPᵢPᵢ`. -/
def probePairTarget : SPath (wd D ν [up r, up i, up i]) s
    (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))) :=
  .cons _ false s hR (.cons _ true _ trivial (.cons _ true _ trivial (.nil _)))
omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
theorem probePairSource_unique (hir : i ≠ r)
    (p : SPath (wd D ν [up i, up i, up r]) s
      (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s)))) :
    p = probePairSource ν i r s hR := by
  suffices aux : ∀ t (p : SPath (wd D ν [up i, up i, up r]) s t)
      (h : t = nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))),
      h ▸ p = probePairSource ν i r s hR from aux _ p rfl
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
theorem probePairMiddle_unique (hir : i ≠ r)
    (p : SPath (wd D ν [up i, up r, up i]) s
      (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s)))) :
    p = probePairMiddle ν i r s hR := by
  suffices aux : ∀ t (p : SPath (wd D ν [up i, up r, up i]) s t)
      (h : t = nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))),
      h ▸ p = probePairMiddle ν i r s hR from aux _ p rfl
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
theorem probePairTarget_unique (hir : i ≠ r)
    (p : SPath (wd D ν [up r, up i, up i]) s
      (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s)))) :
    p = probePairTarget ν i r s hR := by
  suffices aux : ∀ t (p : SPath (wd D ν [up r, up i, up i]) s t)
      (h : t = nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))),
      h ▸ p = probePairTarget ν i r s hR from aux _ p rfl
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
  (Z : P.H (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))))
theorem probePair_left_same :
    crossEntry (P.swappedGens c L) ν [] i i [up r]
      (probePairSource ν i r s hR) (probePairSource ν i r s hR) Z =
    P.preCrossSame i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν i i r
    (.cons _ true s trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ true s trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ false _ hR (.nil _)) Z).trans ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [swappedGens_cross_self]
  rfl

theorem probePair_right_mixed (hir : i ≠ r) :
    crossEntry (P.swappedGens c L) ν [up i] i r []
      (probePairSource ν i r s hR) (probePairMiddle ν i r s hR) Z =
    (P.step (true, i) true s trivial).map
      (P.mixedJ i r (nextSector (true, i) true s) hR Z).hom := by
  refine (crossEntry_right (P.swappedGens c L) ν i i r true trivial
    (.cons _ true _ trivial (.cons _ false _ hR (.nil _)))
    (.cons _ false _ hR (.cons _ true _ trivial (.nil _))) Z).trans ?_
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hir]
  rfl

theorem probePair_left_mixed (hir : i ≠ r) :
    crossEntry (P.swappedGens c L) ν [] i r [up i]
      (probePairMiddle ν i r s hR) (probePairTarget ν i r s hR) Z =
    (P.mixedJ i r s hR ((P.step (true, i) true _ trivial).obj Z)).hom := by
  refine (crossEntry_left (P.swappedGens c L) ν i r i
    (.cons _ true s trivial (.cons _ false _ hR (.nil _)))
    (.cons _ false s hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.nil _)) Z).trans ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hir]
  rfl

theorem probePair_right_same :
    crossEntry (P.swappedGens c L) ν [up r] i i []
      (probePairTarget ν i r s hR) (probePairTarget ν i r s hR) Z =
    (P.step (true, r) false s hR).map (P.preCrossSame i (nextSector (true, r) false s) Z) := by
  refine (crossEntry_right (P.swappedGens c L) ν r i i false hR
    (.cons _ true _ trivial (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.cons _ true _ trivial (.nil _))) Z).trans ?_
  rw [swappedGens_cross_self]
  rfl

/-- The non-correction braid entry `PᵢPᵢRᵣ → RᵣPᵢPᵢ` for `i ≠ r`. -/
theorem probePair_braid (hir : i ≠ r) :
    braidLeft (P.swappedGens c L) i i r ν
      (probePairSource ν i r s hR) (probePairTarget ν i r s hR) Z =
    braidRight (P.swappedGens c L) i i r ν
      (probePairSource ν i r s hR) (probePairTarget ν i r s hR) Z := by
  classical
  let : Subsingleton (SPath (wd D ν [up i, up i, up r]) s
      (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s)))) :=
    ⟨fun p q => (probePairSource_unique ν i r s hR hir p).trans
      (probePairSource_unique ν i r s hR hir q).symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up r, up i]) s
      (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s)))) :=
    ⟨fun p q => (probePairMiddle_unique ν i r s hR hir p).trans
      (probePairMiddle_unique ν i r s hR hir q).symm⟩
  let : Subsingleton (SPath (wd D ν [up r, up i, up i]) s
      (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s)))) :=
    ⟨fun p q => (probePairTarget_unique ν i r s hR hir p).trans
      (probePairTarget_unique ν i r s hR hir q).symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up i, up i, up r]) s
    (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))))
  let := Fintype.ofFinite (SPath (wd D ν [up i, up r, up i]) s
    (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))))
  let := Fintype.ofFinite (SPath (wd D ν [up r, up i, up i]) s
    (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))))
  unfold braidLeft braidRight
  rw [Fintype.sum_subsingleton _ (probePairMiddle (D := D) ν i r s hR),
    Fintype.sum_subsingleton _ (probePairSource (D := D) ν i r s hR),
    Fintype.sum_subsingleton _ (probePairTarget (D := D) ν i r s hR),
    Fintype.sum_subsingleton _ (probePairMiddle (D := D) ν i r s hR)]
  rw [probePair_left_same, probePair_right_mixed _ _ _ _ _ _ _ _ _ hir,
    probePair_left_mixed _ _ _ _ _ _ _ _ _ hir, probePair_right_same]
  simpa only [Category.assoc] using P.preCrossSame_mixedJ_pair_ne i r s hR Z

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
