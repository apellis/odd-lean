/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReservoirPairQCentrality
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.QWeightedReverseSector
/-! The reverse two-reservoir sector braid, with both Q factors retained.
No Q factor or same-colour crossing is inverted. -/

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
variable (ν : X) (i r : I) (s : Sector I)
  (hv : StepValid (true, r) false s)
  (hw : StepValid (true, r) false (nextSector (true, r) false s))
variable (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (Z : P.H (nextSector (true, r) false (nextSector (true, r) false (nextSector (true, i) true s))))
/-- The reverse mixed entry on the left pair. -/
theorem reverseReservoirPair_left_mixed (hir : i ≠ r) :
    crossEntry (P.swappedGens c L) ν [] r i [up r]
      (reservoirPairMiddle ν i r s hv hw) (reservoirPairSource ν i r s hv hw) Z =
    (P.reservoirPairFirstIso i r s hv hw Z).inv ≫
      P.mixedQ i r s hv (P.reservoirPairRest i r s hw Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν r i r
    (.cons _ false s hv (.cons _ true _ trivial (.nil _)))
    (.cons _ true s trivial (.cons _ false _ hv (.nil _)))
    (.cons _ false _ hw (.nil _)) Z).trans ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  dsimp only [swappedGens]
  rw [P.crossImage_ne c (Ne.symm hir)]
  rfl

/-- The reverse mixed entry on the right pair. -/
theorem reverseReservoirPair_right_mixed (hir : i ≠ r) :
    crossEntry (P.swappedGens c L) ν [up r] r i []
      (reservoirPairTarget ν i r s hv hw) (reservoirPairMiddle ν i r s hv hw) Z =
    (P.step (true, r) false s hv).map
      ((P.mixedJ i r (nextSector (true, r) false s) hw Z).inv ≫
        P.mixedQ i r (nextSector (true, r) false s) hw Z) := by
  refine (crossEntry_right (P.swappedGens c L) ν r r i false hv
    (.cons _ false _ hw (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.cons _ false _ hw (.nil _))) Z).trans ?_
  dsimp only [swappedGens]
  rw [P.crossImage_ne c (Ne.symm hir)]
  rfl

/-- The non-correction braid entry `RᵣRᵣPᵢ → PᵢRᵣRᵣ`, retaining both Q factors. -/
theorem reverseReservoirPair_braid (hir : i ≠ r) :
    braidLeft (P.swappedGens c L) r r i ν
      (reservoirPairTarget ν i r s hv hw) (reservoirPairSource ν i r s hv hw) Z =
    braidRight (P.swappedGens c L) r r i ν
      (reservoirPairTarget ν i r s hv hw) (reservoirPairSource ν i r s hv hw) Z := by
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
  rw [Fintype.sum_subsingleton _ (reservoirPairMiddle (D := D) ν i r s hv hw),
    Fintype.sum_subsingleton _ (reservoirPairTarget (D := D) ν i r s hv hw),
    Fintype.sum_subsingleton _ (reservoirPairSource (D := D) ν i r s hv hw),
    Fintype.sum_subsingleton _ (reservoirPairMiddle (D := D) ν i r s hv hw)]
  rw [reservoirPair_left_same, reservoirPair_right_same,
    reverseReservoirPair_left_mixed _ _ _ _ _ _ _ _ _ _ hir,
    reverseReservoirPair_right_mixed _ _ _ _ _ _ _ _ _ _ hir]
  have h := ReverseWeightedPair.transport
    (P.reservoirPairFirstIso i r s hv hw Z)
    ((P.step (true, r) false s hv).mapIso
      (P.mixedJ i r (nextSector (true, r) false s) hw Z))
    (P.reservoirPairCross i r s hv hw Z)
    (P.postCrossSame r s hv hw ((P.step (true, i) true _ trivial).obj Z))
    ((P.step (true, r) false s hv).map
      (P.mixedQ i r (nextSector (true, r) false s) hw Z))
    (P.mixedQ i r s hv (P.reservoirPairRest i r s hw Z))
    (P.postCrossSame_mixedJ_pair_ne i r s hv hw Z)
    (by simpa only [Commute, SemiconjBy, End.mul_def, Category.assoc] using
      reservoirPairQProduct_central Sc P i r s hv hw Z)
  simpa only [reservoirPairFirstIso, reservoirPairRest, reservoirPairCross,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc] using h.symm

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
