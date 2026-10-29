/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.MiddleDistinctReservoirSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctReservoirQPair

/-! # Reverse one-probe sector with unequal reservoir colours

Both prescribed Q factors are retained, with a shared probe spectator.
Only mixed comparison isomorphisms are cancelled.
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
section Paths
variable (ν : X) (i r q : I) (s : Sector I)
  (hr : StepValid (true, r) false s)
  (hq : StepValid (true, q) false (nextSector (true, r) false s))
  {t : Sector I}
  (e : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) = t)
  (Z : P.H t)

/-- The two mixed comparisons composed. -/
def distinctReservoirMoveIso :=
  (P.distinctReservoirFirstSectorIso ν i r q s hr hq e Z).trans
    (P.distinctReservoirSecondSectorIso ν i r q s hr hq e Z)

/-- Both reverse Q factors on the path with the probe first. -/
def distinctReservoirSectorWeight :=
  ((P.distinctReservoirFirstSectorIso ν i r q s hr hq e Z).hom ≫
    P.distinctReservoirMiddleSectorQ ν i r q s hr hq e Z ≫
    (P.distinctReservoirFirstSectorIso ν i r q s hr hq e Z).inv) ≫
      P.distinctReservoirOuterSectorQ ν i r q s hr hq e Z

/-- Both weights are the two prescribed polynomials in a common probe dot. -/
theorem distinctReservoirSectorWeight_heq :
    HEq (P.distinctReservoirSectorWeight ν i r q s hr hq e Z)
      (qExpr Sc (P.prPreDot i r s hr (P.distinctReservoirRest i r q s hq (e ▸ Z)))
          (P.distinctReservoirLastDot i r q s hr hq (e ▸ Z)) i q ≫
        P.mixedQ i r s hr (P.distinctReservoirRest i r q s hq (e ▸ Z))) := by
  subst e
  apply heq_of_eq
  change ((P.distinctReservoirFirstIso i r q s hr hq Z).hom ≫
    (P.step (true, r) false s hr).map (P.mixedQ i q (nextSector (true, r) false s) hq Z) ≫
    (P.distinctReservoirFirstIso i r q s hr hq Z).inv) ≫ _ = _
  rw [P.distinctReservoirFirstIso_conj_mixedQ]
  rfl

variable (c : P.CrossCoeff Sc) (L : P.LeftwardData)
/-- The composite forward mixed entry is the composite comparison. -/
theorem distinctReservoirMoveIso_hom_eq (hir : i ≠ r) (hiq : i ≠ q) :
    (P.distinctReservoirMoveIso ν i r q s hr hq e Z).hom =
      crossEntry (P.swappedGens c L) ν [] i r [up q]
        (distinctReservoirSource ν i r q s hr hq e) (distinctReservoirMiddle ν i r q s hr hq e) Z ≫
      crossEntry (P.swappedGens c L) ν [up r] i q []
        (distinctReservoirMiddle ν i r q s hr hq e) (distinctReservoirTarget ν i r q s hr hq e) Z := by
  rw [distinctReservoirMoveIso, Iso.trans_hom,
    P.distinctReservoirFirstSectorIso_hom_eq ν i r q s hr hq e Z c L hir,
    P.distinctReservoirSecondSectorIso_hom_eq ν i r q s hr hq e Z c L hiq]

/-- The reverse mixed movement keeps both weights, without cancelling either. -/
theorem reverseDistinctReservoir_move_eq (hir : i ≠ r) (hiq : i ≠ q) :
    crossEntry (P.swappedGens c L) ν [up r] q i []
        (distinctReservoirTarget ν i r q s hr hq e) (distinctReservoirMiddle ν i r q s hr hq e) Z ≫
      crossEntry (P.swappedGens c L) ν [] r i [up q]
        (distinctReservoirMiddle ν i r q s hr hq e) (distinctReservoirSource ν i r q s hr hq e) Z =
      (P.distinctReservoirMoveIso ν i r q s hr hq e Z).inv ≫
        P.distinctReservoirSectorWeight ν i r q s hr hq e Z := by
  rw [P.reverseDistinctReservoir_first_eq ν i r q s hr hq e Z c L hir,
    P.reverseDistinctReservoir_second_eq ν i r q s hr hq e Z c L hiq]
  simp only [distinctReservoirMoveIso, distinctReservoirSectorWeight, Iso.trans_inv,
    Category.assoc, Iso.inv_hom_id_assoc]
end Paths

/-- The two-factor weight crosses the prescribed unequal reservoir entry. -/
theorem distinctReservoirSectorWeight_cross (ν : X) (i r q : I) (s : Sector I)
    (hr : StepValid (true, r) false s)
    (hq : StepValid (true, q) false (nextSector (true, r) false s))
    (hq' : StepValid (true, q) false s)
    (hr' : StepValid (true, r) false (nextSector (true, q) false s))
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hrq : r ≠ q)
    (hsP : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))
    (Z : P.H (nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))) :
    P.distinctReservoirSectorWeight ν i r q s hr hq hsP Z ≫
        crossEntry (P.swappedGens c L) ν [up i] r q []
          (distinctReservoirSource ν i r q s hr hq hsP) (distinctReservoirSource ν i q r s hq' hr' rfl) Z =
      crossEntry (P.swappedGens c L) ν [up i] r q []
          (distinctReservoirSource ν i r q s hr hq hsP) (distinctReservoirSource ν i q r s hq' hr' rfl) Z ≫
        P.distinctReservoirSectorWeight ν i q r s hq' hr' rfl Z := by
  apply rectangle_of_heq
    (P.distinctReservoirSource_obj ν i r q s hr hq hsP Z)
    (P.distinctReservoirSource_obj ν i r q s hr hq hsP Z)
    (P.distinctReservoirSource_obj ν i r q s hr hq hsP Z) rfl rfl
    (P.distinctReservoirSectorWeight_heq ν i r q s hr hq hsP Z)
    (P.distinctReservoir_right ν i r q s hr hq hq' hr' hsP c L Z hrq)
    (P.distinctReservoir_right ν i r q s hr hq hq' hr' hsP c L Z hrq)
    (P.distinctReservoirSectorWeight_heq ν i q r s hq' hr' rfl Z)
  exact heq_of_eq (P.postCrossNe_qExpr_pair i r q s hr hq hq' hr' hrq hsP Z)

/-- The reverse one-probe sector for three pairwise distinct colours, retaining
both different parameter-polynomial weights. -/
theorem reverseDistinctReservoir_braid (ν : X) (i r q : I) (s : Sector I)
    (hr : StepValid (true, r) false s)
    (hq : StepValid (true, q) false (nextSector (true, r) false s))
    (hq' : StepValid (true, q) false s)
    (hr' : StepValid (true, r) false (nextSector (true, q) false s))
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hir : i ≠ r) (hiq : i ≠ q) (hrq : r ≠ q)
    (hsP : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))
    (Z : P.H (nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))) :
    braidLeft (P.swappedGens c L) r q i ν
      (distinctReservoirTarget ν i r q s hr hq hsP) (distinctReservoirSource ν i q r s hq' hr' rfl) Z =
    braidRight (P.swappedGens c L) r q i ν
      (distinctReservoirTarget ν i r q s hr hq hsP) (distinctReservoirSource ν i q r s hq' hr' rfl) Z := by
  classical
  let t := nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s))
  let : Subsingleton (SPath (wd D ν [up i, up r, up q]) s t) :=
    ⟨path_eq_three_distinct hir hiq hrq⟩
  let := Fintype.ofFinite (SPath (wd D ν [up i, up r, up q]) s t)
  let : Subsingleton (SPath (wd D ν [up i, up q, up r]) s t) :=
    ⟨path_eq_three_distinct hiq hir hrq.symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up i, up q, up r]) s t)
  let : Subsingleton (SPath (wd D ν [up r, up i, up q]) s t) :=
    ⟨path_eq_three_distinct hir.symm hrq hiq⟩
  let := Fintype.ofFinite (SPath (wd D ν [up r, up i, up q]) s t)
  let : Subsingleton (SPath (wd D ν [up q, up i, up r]) s t) :=
    ⟨path_eq_three_distinct hiq.symm hrq.symm hir⟩
  let := Fintype.ofFinite (SPath (wd D ν [up q, up i, up r]) s t)
  let : Subsingleton (SPath (wd D ν [up r, up q, up i]) s t) :=
    ⟨path_eq_three_distinct hrq hir.symm hiq.symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up r, up q, up i]) s t)
  let : Subsingleton (SPath (wd D ν [up q, up r, up i]) s t) :=
    ⟨path_eq_three_distinct hrq.symm hiq.symm hir.symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up q, up r, up i]) s t)
  have hf := P.distinctReservoir_braid ν i r q s hr hq hq' hr' c L hir hiq hrq hsP Z
  unfold braidLeft braidRight at hf
  rw [Fintype.sum_subsingleton _ (distinctReservoirTarget (D := D) ν i r q s hr hq hsP),
    Fintype.sum_subsingleton _ (distinctReservoirMiddle (D := D) ν i r q s hr hq hsP),
    Fintype.sum_subsingleton _ (distinctReservoirMiddle (D := D) ν i q r s hq' hr' rfl),
    Fintype.sum_subsingleton _ (distinctReservoirSource (D := D) ν i q r s hq' hr' rfl)] at hf
  conv_rhs at hf => rw [Category.assoc]
  rw [← P.distinctReservoirMoveIso_hom_eq ν i r q s hr hq hsP Z c L hir hiq,
    ← P.distinctReservoirMoveIso_hom_eq ν i q r s hq' hr' rfl Z c L hiq hir] at hf
  unfold braidLeft braidRight
  rw [Fintype.sum_subsingleton _ (distinctReservoirMiddle (D := D) ν i q r s hq' hr' rfl),
    Fintype.sum_subsingleton _ (distinctReservoirTarget (D := D) ν i q r s hq' hr' rfl),
    Fintype.sum_subsingleton _ (distinctReservoirSource (D := D) ν i r q s hr hq hsP),
    Fintype.sum_subsingleton _ (distinctReservoirMiddle (D := D) ν i r q s hr hq hsP)]
  conv_lhs => rw [Category.assoc]
  rw [P.reverseDistinctReservoir_move_eq ν i r q s hr hq hsP Z c L hir hiq,
    P.reverseDistinctReservoir_move_eq ν i q r s hq' hr' rfl Z c L hiq hir]
  symm
  apply (cancel_epi (P.distinctReservoirMoveIso ν i r q s hr hq hsP Z).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [P.distinctReservoirSectorWeight_cross ν i r q s hr hq hq' hr' c L hrq hsP Z]
  rw [← Category.assoc (P.distinctReservoirMoveIso ν i r q s hr hq hsP Z).hom, hf]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
