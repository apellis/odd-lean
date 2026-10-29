/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctReservoirQ

/-! # Middle one-probe sector with unequal reservoir colours

The single Q weight is retained. Only mixed comparison isomorphisms are cancelled.
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

/-- The first mixed comparison on sector objects. -/
def distinctReservoirFirstSectorIso :
    (P.pathFunctor (distinctReservoirSource (D := D) ν i r q s hr hq e)).obj Z ≅
      (P.pathFunctor (distinctReservoirMiddle (D := D) ν i r q s hr hq e)).obj Z := by
  subst e
  exact P.distinctReservoirFirstIso i r q s hr hq Z

/-- The second mixed comparison on sector objects. -/
def distinctReservoirSecondSectorIso :
    (P.pathFunctor (distinctReservoirMiddle (D := D) ν i r q s hr hq e)).obj Z ≅
      (P.pathFunctor (distinctReservoirTarget (D := D) ν i r q s hr hq e)).obj Z := by
  subst e
  exact (P.step (true, r) false s hr).mapIso
    (P.mixedJ i q (nextSector (true, r) false s) hq Z)

/-- The weight of the reverse first mixed edge. -/
def distinctReservoirOuterSectorQ :
    End ((P.pathFunctor (distinctReservoirSource (D := D) ν i r q s hr hq e)).obj Z) := by
  subst e
  exact P.mixedQ i r s hr (P.distinctReservoirRest i r q s hq Z)

/-- The weight of the reverse second mixed edge. -/
def distinctReservoirMiddleSectorQ :
    End ((P.pathFunctor (distinctReservoirMiddle (D := D) ν i r q s hr hq e)).obj Z) := by
  subst e
  exact (P.step (true, r) false s hr).map (P.mixedQ i q (nextSector (true, r) false s) hq Z)

/-- The first Q weight in dot coordinates. -/
theorem distinctReservoirOuterSectorQ_heq :
    HEq (P.distinctReservoirOuterSectorQ ν i r q s hr hq e Z)
      (P.mixedQ i r s hr (P.distinctReservoirRest i r q s hq (e ▸ Z))) := by
  subst e
  rfl

/-- The second Q weight conjugated to the first path. -/
theorem distinctReservoirMiddleSectorQ_conj_heq :
    HEq ((P.distinctReservoirFirstSectorIso ν i r q s hr hq e Z).hom ≫
      P.distinctReservoirMiddleSectorQ ν i r q s hr hq e Z ≫
      (P.distinctReservoirFirstSectorIso ν i r q s hr hq e Z).inv)
      (qExpr Sc (P.prPreDot i r s hr (P.distinctReservoirRest i r q s hq (e ▸ Z)))
        (P.distinctReservoirLastDot i r q s hr hq (e ▸ Z)) i q) := by
  subst e
  exact heq_of_eq (P.distinctReservoirFirstIso_conj_mixedQ i r q s hr hq Z)

variable (c : P.CrossCoeff Sc) (L : P.LeftwardData)

/-- The first forward mixed edge is the comparison. -/
theorem distinctReservoirFirstSectorIso_hom_eq (hir : i ≠ r) :
    (P.distinctReservoirFirstSectorIso ν i r q s hr hq e Z).hom =
      crossEntry (P.swappedGens c L) ν [] i r [up q]
        (distinctReservoirSource ν i r q s hr hq e) (distinctReservoirMiddle ν i r q s hr hq e) Z := by
  subst e
  symm
  refine (crossEntry_left (P.swappedGens c L) ν i r q
    (.cons _ true s trivial (.cons _ false _ hr (.nil _)))
    (.cons _ false s hr (.cons _ true _ trivial (.nil _)))
    (.cons _ false _ hq (.nil _)) Z).trans ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hir]
  rfl

/-- The second forward mixed edge is the mapped comparison. -/
theorem distinctReservoirSecondSectorIso_hom_eq (hiq : i ≠ q) :
    (P.distinctReservoirSecondSectorIso ν i r q s hr hq e Z).hom =
      crossEntry (P.swappedGens c L) ν [up r] i q []
        (distinctReservoirMiddle ν i r q s hr hq e) (distinctReservoirTarget ν i r q s hr hq e) Z := by
  subst e
  symm
  refine (crossEntry_right (P.swappedGens c L) ν r i q false hr
    (.cons _ true _ trivial (.cons _ false _ hq (.nil _)))
    (.cons _ false _ hq (.cons _ true _ trivial (.nil _))) Z).trans ?_
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hiq]
  rfl

/-- The reverse first edge retains its prescribed Q factor. -/
theorem reverseDistinctReservoir_first_eq (hir : i ≠ r) :
    crossEntry (P.swappedGens c L) ν [] r i [up q]
      (distinctReservoirMiddle ν i r q s hr hq e) (distinctReservoirSource ν i r q s hr hq e) Z =
      (P.distinctReservoirFirstSectorIso ν i r q s hr hq e Z).inv ≫
        P.distinctReservoirOuterSectorQ ν i r q s hr hq e Z := by
  subst e
  refine (crossEntry_left (P.swappedGens c L) ν r i q
    (.cons _ false s hr (.cons _ true _ trivial (.nil _)))
    (.cons _ true s trivial (.cons _ false _ hr (.nil _)))
    (.cons _ false _ hq (.nil _)) Z).trans ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hir.symm]
  rfl

/-- The reverse second edge retains its prescribed Q factor. -/
theorem reverseDistinctReservoir_second_eq (hiq : i ≠ q) :
    crossEntry (P.swappedGens c L) ν [up r] q i []
      (distinctReservoirTarget ν i r q s hr hq e) (distinctReservoirMiddle ν i r q s hr hq e) Z =
      (P.distinctReservoirSecondSectorIso ν i r q s hr hq e Z).inv ≫
        P.distinctReservoirMiddleSectorQ ν i r q s hr hq e Z := by
  subst e
  refine (crossEntry_right (P.swappedGens c L) ν r q i false hr
    (.cons _ false _ hq (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.cons _ false _ hq (.nil _))) Z).trans ?_
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hiq.symm]
  exact (P.step (true, r) false s hr).map_comp _ _
end Paths

/-- The single Q weight transported across the reservoir edge. -/
theorem distinctReservoirOuterSectorQ_cross (ν : X) (i r q : I) (s : Sector I)
    (hr : StepValid (true, r) false s)
    (hq : StepValid (true, q) false (nextSector (true, r) false s))
    (hq' : StepValid (true, q) false s)
    (hr' : StepValid (true, r) false (nextSector (true, q) false s))
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hrq : r ≠ q)
    (hsP : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))
    (Z : P.H (nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))) :
    P.distinctReservoirOuterSectorQ ν i r q s hr hq hsP Z ≫
        crossEntry (P.swappedGens c L) ν [up i] r q []
          (distinctReservoirSource ν i r q s hr hq hsP) (distinctReservoirSource ν i q r s hq' hr' rfl) Z =
      crossEntry (P.swappedGens c L) ν [up i] r q []
          (distinctReservoirSource ν i r q s hr hq hsP) (distinctReservoirSource ν i q r s hq' hr' rfl) Z ≫
        ((P.distinctReservoirFirstSectorIso ν i q r s hq' hr' rfl Z).hom ≫
          P.distinctReservoirMiddleSectorQ ν i q r s hq' hr' rfl Z ≫
          (P.distinctReservoirFirstSectorIso ν i q r s hq' hr' rfl Z).inv) := by
  apply rectangle_of_heq
    (P.distinctReservoirSource_obj ν i r q s hr hq hsP Z)
    (P.distinctReservoirSource_obj ν i r q s hr hq hsP Z)
    (P.distinctReservoirSource_obj ν i r q s hr hq hsP Z) rfl rfl
    (P.distinctReservoirOuterSectorQ_heq ν i r q s hr hq hsP Z)
    (P.distinctReservoir_right ν i r q s hr hq hq' hr' hsP c L Z hrq)
    (P.distinctReservoir_right ν i r q s hr hq hq' hr' hsP c L Z hrq)
    (P.distinctReservoirMiddleSectorQ_conj_heq ν i q r s hq' hr' rfl Z)
  exact heq_of_eq (P.postCrossNe_qExpr_outer i r q s hr hq hq' hr' hrq hsP Z)

/-- The middle one-probe sector for three pairwise distinct colours. -/
theorem middleDistinctReservoir_braid (ν : X) (i r q : I) (s : Sector I)
    (hr : StepValid (true, r) false s)
    (hq : StepValid (true, q) false (nextSector (true, r) false s))
    (hq' : StepValid (true, q) false s)
    (hr' : StepValid (true, r) false (nextSector (true, q) false s))
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hir : i ≠ r) (hiq : i ≠ q) (hrq : r ≠ q)
    (hsP : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))
    (Z : P.H (nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))) :
    braidLeft (P.swappedGens c L) r i q ν
      (distinctReservoirMiddle ν i r q s hr hq hsP) (distinctReservoirMiddle ν i q r s hq' hr' rfl) Z =
    braidRight (P.swappedGens c L) r i q ν
      (distinctReservoirMiddle ν i r q s hr hq hsP) (distinctReservoirMiddle ν i q r s hq' hr' rfl) Z := by
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
  rw [← P.distinctReservoirFirstSectorIso_hom_eq ν i r q s hr hq hsP Z c L hir,
    ← P.distinctReservoirSecondSectorIso_hom_eq ν i r q s hr hq hsP Z c L hiq,
    ← P.distinctReservoirFirstSectorIso_hom_eq ν i q r s hq' hr' rfl Z c L hiq,
    ← P.distinctReservoirSecondSectorIso_hom_eq ν i q r s hq' hr' rfl Z c L hir] at hf
  unfold braidLeft braidRight
  rw [Fintype.sum_subsingleton _ (distinctReservoirSource (D := D) ν i q r s hq' hr' rfl),
    Fintype.sum_subsingleton _ (distinctReservoirSource (D := D) ν i r q s hr hq hsP),
    Fintype.sum_subsingleton _ (distinctReservoirTarget (D := D) ν i q r s hq' hr' rfl),
    Fintype.sum_subsingleton _ (distinctReservoirTarget (D := D) ν i r q s hr hq hsP)]
  rw [← P.distinctReservoirFirstSectorIso_hom_eq ν i q r s hq' hr' rfl Z c L hiq,
    ← P.distinctReservoirSecondSectorIso_hom_eq ν i r q s hr hq hsP Z c L hiq,
    P.reverseDistinctReservoir_first_eq ν i r q s hr hq hsP Z c L hir,
    P.reverseDistinctReservoir_second_eq ν i q r s hq' hr' rfl Z c L hir]
  symm
  apply (cancel_epi (P.distinctReservoirFirstSectorIso ν i r q s hr hq hsP Z).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (P.distinctReservoirFirstSectorIso ν i r q s hr hq hsP Z).hom,
    ← Category.assoc ((P.distinctReservoirFirstSectorIso ν i r q s hr hq hsP Z).hom ≫
      (P.distinctReservoirSecondSectorIso ν i r q s hr hq hsP Z).hom), hf]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (P.distinctReservoirOuterSectorQ ν i r q s hr hq hsP Z),
    P.distinctReservoirOuterSectorQ_cross ν i r q s hr hq hq' hr' c L hrq hsP Z]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
