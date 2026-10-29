/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctProbeSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctProbeDots

/-! # Reverse mixed edges for two arbitrary probe colours

Literal reverse entries retain both mixed Q factors. The canonical forward move
is an isomorphism independently of the Q factors. These are the edge reductions
for the reverse two-probe sector of the non-correction braid relation.
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
variable (ν : X) (i j r : I) (s : Sector I) (hR : StepValid (true, r) false s)
  {t : Sector I}
  (e : nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) = t)

section Edges
variable (c : P.CrossCoeff Sc) (L : P.LeftwardData) (Z : P.H t)

/-- The reverse left entry, including its terminal sector transport. -/
theorem reverseDistinctProbe_left_mixed_heq (hir : i ≠ r) :
    HEq (crossEntry (P.swappedGens c L) ν [] r i [up j]
      (distinctProbeTarget ν i j r s hR e) (distinctProbeMiddle ν i j r s hR e) Z)
      ((P.mixedJ i r s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z))).inv ≫
        P.mixedQ i r s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z))) := by
  subst e
  apply heq_of_eq
  refine (crossEntry_left (P.swappedGens c L) ν r i j
    (.cons _ false s hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true s trivial (.cons _ false _ hR (.nil _)))
    (.cons _ true _ trivial (.nil _)) Z).trans ?_
  change 𝟙 _ ≫ P.crossImage c r i (SKM.wt D ν [up j])
    (.cons _ false s hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true s trivial (.cons _ false _ hR (.nil _)))
    ((P.step (true, j) true _ trivial).obj Z) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  exact P.crossImage_ne c (Ne.symm hir) _ _ _ _

/-- The reverse right entry, including its terminal sector transport. -/
theorem reverseDistinctProbe_right_mixed_heq (hjr : j ≠ r) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] r j []
      (distinctProbeMiddle ν i j r s hR e) (distinctProbeSource ν i j r s hR e) Z)
      ((P.step (true, i) true s trivial).map
        ((P.mixedJ j r (nextSector (true, i) true s) hR (e ▸ Z)).inv ≫
          P.mixedQ j r (nextSector (true, i) true s) hR (e ▸ Z))) := by
  subst e
  apply heq_of_eq
  refine (crossEntry_right (P.swappedGens c L) ν i r j true trivial
    (.cons _ false _ hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.cons _ false _ hR (.nil _))) Z).trans ?_
  change (P.step (true, i) true s trivial).map
    (P.crossImage c r j ν
      (.cons _ false (nextSector (true, i) true s) hR (.cons _ true _ trivial (.nil _)))
      (.cons _ true (nextSector (true, i) true s) trivial (.cons _ false _ hR (.nil _))) Z) = _
  exact congrArg (P.step (true, i) true s trivial).map
    (P.crossImage_ne c (Ne.symm hjr) ν _ _ Z)

/-- The literal reverse two-entry path, with neither Q factor inverted. -/
theorem reverseDistinctProbe_move_heq (hir : i ≠ r) (hjr : j ≠ r) :
    HEq
      (crossEntry (P.swappedGens c L) ν [] r i [up j]
          (distinctProbeTarget ν i j r s hR e) (distinctProbeMiddle ν i j r s hR e) Z ≫
        crossEntry (P.swappedGens c L) ν [up i] r j []
          (distinctProbeMiddle ν i j r s hR e) (distinctProbeSource ν i j r s hR e) Z)
      (((P.mixedJ i r s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z))).inv ≫
          P.mixedQ i r s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z))) ≫
        (P.step (true, i) true s trivial).map
          ((P.mixedJ j r (nextSector (true, i) true s) hR (e ▸ Z)).inv ≫
            P.mixedQ j r (nextSector (true, i) true s) hR (e ▸ Z))) := by
  subst e
  apply heq_of_eq
  exact congrArg₂ (· ≫ ·)
    (eq_of_heq (P.reverseDistinctProbe_left_mixed_heq ν i j r s hR rfl c L Z hir))
    (eq_of_heq (P.reverseDistinctProbe_right_mixed_heq ν i j r s hR rfl c L Z hjr))
end Edges

variable (Z : P.H t)

/-- Canonical forward movement of the reservoir across the two probes. -/
def distinctProbeMoveIso :
    (P.pathFunctor (distinctProbeSource (D := D) ν i j r s hR e)).obj Z ≅
      (P.pathFunctor (distinctProbeTarget (D := D) ν i j r s hR e)).obj Z := by
  subst e
  exact ((P.step (true, i) true s trivial).mapIso
    (P.mixedJ j r (nextSector (true, i) true s) hR Z)).trans
      (P.mixedJ i r s hR ((P.step (true, j) true _ trivial).obj Z))

/-- Raw formula for the hom of the canonical move, with terminal transport. -/
theorem distinctProbeMoveIso_hom_heq :
    HEq (P.distinctProbeMoveIso ν i j r s hR e Z).hom
      ((P.step (true, i) true s trivial).map
          (P.mixedJ j r (nextSector (true, i) true s) hR (e ▸ Z)).hom ≫
        (P.mixedJ i r s hR ((P.step (true, j) true _ trivial).obj (e ▸ Z))).hom) := by
  subst e
  rfl

/-- The canonical move hom is the forward two-entry path when both mixed
colour pairs are unequal. No inequality between the probes is needed. -/
theorem distinctProbeMoveIso_hom_eq (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hir : i ≠ r) (hjr : j ≠ r) :
    (P.distinctProbeMoveIso ν i j r s hR e Z).hom =
      crossEntry (P.swappedGens c L) ν [up i] j r []
          (distinctProbeSource ν i j r s hR e) (distinctProbeMiddle ν i j r s hR e) Z ≫
        crossEntry (P.swappedGens c L) ν [] i r [up j]
          (distinctProbeMiddle ν i j r s hR e) (distinctProbeTarget ν i j r s hR e) Z := by
  exact eq_of_heq ((P.distinctProbeMoveIso_hom_heq ν i j r s hR e Z).trans
    (P.distinctProbe_move_heq ν i j r s hR e c L Z hir hjr).symm)

/-- The ordered two-Q weight on the source sector, conjugated by its canonical
object equality. This uses only the raw dots, not a Q-transport hypothesis. -/
def distinctProbeSectorWeight :
    End ((P.pathFunctor (distinctProbeSource (D := D) ν i j r s hR e)).obj Z) :=
  eqToHom (P.distinctProbeSource_obj ν i j r s hR e Z) ≫
    (qExpr Sc (P.distinctProbeOuterDot i j r s hR (e ▸ Z))
        (P.distinctProbeSpectatorDot i j r s hR (e ▸ Z)) i r ≫
      qExpr Sc (P.distinctProbeInnerDot i j r s hR (e ▸ Z))
        (P.distinctProbeSpectatorDot i j r s hR (e ▸ Z)) j r) ≫
    eqToHom (P.distinctProbeSource_obj ν i j r s hR e Z).symm

/-- The conjugated sector weight is heterogeneously the raw ordered Q product. -/
theorem distinctProbeSectorWeight_heq :
    HEq (P.distinctProbeSectorWeight ν i j r s hR e Z)
      (qExpr Sc (P.distinctProbeOuterDot i j r s hR (e ▸ Z))
          (P.distinctProbeSpectatorDot i j r s hR (e ▸ Z)) i r ≫
        qExpr Sc (P.distinctProbeInnerDot i j r s hR (e ▸ Z))
          (P.distinctProbeSpectatorDot i j r s hR (e ▸ Z)) j r) := by
  exact sandwich_heq _ _ _

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
