/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.InterchangePostPairTransport
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctProbeSector

/-! # Transport for a probe crossing two reservoir colours

A transport-aware form of the shifted interchange triangle. The crossing is
expanded to the same right-associated expression as the prescribed `postCrossNe`.
The forward one-probe sector retains all endpoint transports.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- The prescribed unequal reservoir crossing passes through the two mixed comparisons. -/
theorem postCrossNe_mixedJ_pair_heq (i r q : I) (s : Sector I)
    (hr : StepValid (true, r) false s)
    (hq : StepValid (true, q) false (nextSector (true, r) false s))
    (hq' : StepValid (true, q) false s)
    (hr' : StepValid (true, r) false (nextSector (true, q) false s))
    (hs : nextSector (true, q) false (nextSector (true, r) false s) =
      nextSector (true, r) false (nextSector (true, q) false s))
    (hsP : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))
    (Z : P.H (nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))) :
    HEq
      ((P.step (true, i) true s trivial).map
          (P.postCrossNe r q (nextSector (true, i) true s) hr hq hq' hr' hsP Z) ≫
        (P.mixedJ i q s hq' ((P.step (true, r) false
          (nextSector (true, q) false (nextSector (true, i) true s)) hr').obj Z)).hom ≫
        (P.step (true, q) false s hq').map
          (P.mixedJ i r (nextSector (true, q) false s) hr' Z).hom)
      ((P.mixedJ i r s hr ((P.step (true, q) false
          (nextSector (true, r) false (nextSector (true, i) true s)) hq).obj (hsP ▸ Z))).hom ≫
        (P.step (true, r) false s hr).map
          (P.mixedJ i q (nextSector (true, r) false s) hq (hsP ▸ Z)).hom ≫
        (P.step (true, r) false s hr).map
          ((P.step (true, q) false (nextSector (true, r) false s) hq).map
            (eqToHom (P.probe_obj_sector_transport i hs Z))) ≫
        P.postCrossNe r q s hr hq hq' hr' hs
          ((P.step (true, i) true (nextSector (true, r) false
            (nextSector (true, q) false s)) trivial).obj Z)) := by
  have h₃ : P.muM (nextSector (true, q) false (nextSector (true, r) false s)) + D.α r =
      P.muM (nextSector (true, q) false s) := by
    rw [hs]
    exact P.muM_postE r hr'
  have ht := resCore_mixedInterchange_transport P.W r q i s.1
    (congrArg P.muM hs) (P.muM_postE q hq) (P.muM_postE r hr) h₃
    (P.muM_postE q hq') (P.muM_postE r hr') (P.T.E i (P.muP_preE i s))
    ((hsP ▸ Z) : P.H (nextSector (true, q) false
      (nextSector (true, r) false (nextSector (true, i) true s)))) Z (P.sector_heq hsP Z)
    ((hs ▸ (P.step (true, i) true (nextSector (true, r) false
      (nextSector (true, q) false s)) trivial).obj Z) :
        P.H (nextSector (true, q) false (nextSector (true, r) false s)))
    (P.probe_obj_sector_transport i hs Z)
    (eq_of_heq (P.postE_obj_heq r (nextSector (true, i) true s).1 hsP h₃
      (P.muM_postE r hr') Z))
    (eq_of_heq (P.postE_obj_heq r s.1 hs h₃ (P.muM_postE r hr')
      ((P.step (true, i) true (nextSector (true, r) false
        (nextSector (true, q) false s)) trivial).obj Z)))
  apply heq_of_eq
  refine Eq.trans ?_ (Eq.trans ht ?_)
  · apply congrArg₂ (fun f g => f ≫ g)
    · rfl
    · apply congrArg₂ (fun f g => f ≫ g)
      · rfl
      · rfl
  · apply congrArg₂ (fun f g => f ≫ g)
    · rfl
    · apply congrArg₂ (fun f g => f ≫ g)
      · rfl
      · apply congrArg₂ (fun f g => f ≫ g)
        · rfl
        · rfl

section Paths
variable (ν : X) (i r q : I) (s : Sector I)
  (hr : StepValid (true, r) false s)
  (hq : StepValid (true, q) false (nextSector (true, r) false s))
  {t : Sector I}
  (e : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) = t)

/-- The path with the probe before both reservoir letters. -/
def distinctReservoirSource : SPath (wd D ν [up i, up r, up q]) s t :=
  SPath.three true false false trivial hr hq e
/-- The path with the probe between the reservoir letters. -/
def distinctReservoirMiddle : SPath (wd D ν [up r, up i, up q]) s t :=
  SPath.three false true false hr trivial hq e
/-- The path with the probe after both reservoir letters. -/
def distinctReservoirTarget : SPath (wd D ν [up r, up q, up i]) s t :=
  SPath.three false false true hr hq trivial e

variable (c : P.CrossCoeff Sc) (L : P.LeftwardData) (Z : P.H t)

/-- Evaluation of the two forward mixed edges. -/
theorem distinctReservoir_move_heq (hir : i ≠ r) (hiq : i ≠ q) :
    HEq
      (crossEntry (P.swappedGens c L) ν [] i r [up q]
          (distinctReservoirSource ν i r q s hr hq e)
          (distinctReservoirMiddle ν i r q s hr hq e) Z ≫
        crossEntry (P.swappedGens c L) ν [up r] i q []
          (distinctReservoirMiddle ν i r q s hr hq e)
          (distinctReservoirTarget ν i r q s hr hq e) Z)
      ((P.mixedJ i r s hr ((P.step (true, q) false
          (nextSector (true, r) false (nextSector (true, i) true s)) hq).obj (e ▸ Z))).hom ≫
        (P.step (true, r) false s hr).map
          (P.mixedJ i q (nextSector (true, r) false s) hq (e ▸ Z)).hom) := by
  subst e
  apply heq_of_eq
  apply congrArg₂ (fun f g => f ≫ g)
  · refine (crossEntry_left (P.swappedGens c L) ν i r q
      (.cons _ true s trivial (.cons _ false _ hr (.nil _)))
      (.cons _ false s hr (.cons _ true _ trivial (.nil _)))
      (.cons _ false _ hq (.nil _)) Z).trans ?_
    apply eq_of_heq
    refine (sandwich_heq _ _ _).trans ?_
    dsimp only [swappedGens]
    erw [P.crossImage_ne c hir]
    rfl
  · refine (crossEntry_right (P.swappedGens c L) ν r i q false hr
      (.cons _ true _ trivial (.cons _ false _ hq (.nil _)))
      (.cons _ false _ hq (.cons _ true _ trivial (.nil _))) Z).trans ?_
    dsimp only [swappedGens]
    erw [P.crossImage_ne c hiq]
    rfl

/-- Evaluation of the source path object. -/
theorem distinctReservoirSource_obj :
    (P.pathFunctor (distinctReservoirSource (D := D) ν i r q s hr hq e)).obj Z =
      (P.step (true, i) true s trivial).obj
        ((P.step (true, r) false (nextSector (true, i) true s) hr).obj
          ((P.step (true, q) false (nextSector (true, r) false
            (nextSector (true, i) true s)) hq).obj (e ▸ Z))) := by
  subst e
  rfl

/-- Evaluation of the target path object. -/
theorem distinctReservoirTarget_obj :
    (P.pathFunctor (distinctReservoirTarget (D := D) ν i r q s hr hq e)).obj Z =
      (P.step (true, r) false s hr).obj
        ((P.step (true, q) false (nextSector (true, r) false s) hq).obj
          ((P.step (true, i) true _ trivial).obj (e ▸ Z))) := by
  subst e
  rfl
end Paths

section ReservoirEdges
variable (ν : X) (i r q : I) (s : Sector I)
  (hr : StepValid (true, r) false s)
  (hq : StepValid (true, q) false (nextSector (true, r) false s))
  (hq' : StepValid (true, q) false s)
  (hr' : StepValid (true, r) false (nextSector (true, q) false s))
  (hs : nextSector (true, q) false (nextSector (true, r) false s) =
    nextSector (true, r) false (nextSector (true, q) false s))
  (hsP : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) =
    nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (Z : P.H (nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s))))

/-- The reservoir crossing with the probe on the left. -/
theorem distinctReservoir_right (hrq : r ≠ q) :
    HEq (crossEntry (P.swappedGens c L) ν [up i] r q []
      (distinctReservoirSource ν i r q s hr hq hsP)
      (distinctReservoirSource ν i q r s hq' hr' rfl) Z)
      ((P.step (true, i) true s trivial).map
        (P.postCrossNe r q (nextSector (true, i) true s) hr hq hq' hr' hsP Z)) := by
  dsimp only [distinctReservoirSource, SPath.three]
  erw [crossEntry_right]
  apply map_of_heq _ (P.pathFunctor_two_obj
    (c₁ := ⟨up r, SKM.wt D ν [up q]⟩) (c₂ := ⟨up q, SKM.wt D ν []⟩)
    (t := nextSector (true, i) true s)
    false false hr hq hsP Z _ (P.sector_heq hsP Z)) rfl
  dsimp only [swappedGens]
  erw [P.crossImage_ne c hrq]
  exact P.twoTwo_two_heq
    ⟨up r, SKM.wt D ν [up q]⟩ ⟨up q, ν⟩
    ⟨up q, SKM.wt D ν [up r]⟩ ⟨up r, ν⟩
    (P.crossNeEntry r q _ _ _ _) (t := nextSector (true, i) true s)
    false false false false hr hq hq' hr' hsP rfl rfl Z Z HEq.rfl

/-- The reservoir crossing with the probe on the right, including its endpoint comparison. -/
theorem distinctReservoir_left (hir : i ≠ r) (hiq : i ≠ q) (hrq : r ≠ q) :
    HEq (crossEntry (P.swappedGens c L) ν [] r q [up i]
      (distinctReservoirTarget ν i r q s hr hq hsP)
      (distinctReservoirTarget ν i q r s hq' hr' rfl) Z)
      ((P.step (true, r) false s hr).map
        ((P.step (true, q) false (nextSector (true, r) false s) hq).map
          (eqToHom (P.probe_obj_sector_transport i hs Z))) ≫
        P.postCrossNe r q s hr hq hq' hr' hs
          ((P.step (true, i) true (nextSector (true, r) false
            (nextSector (true, q) false s)) trivial).obj Z)) := by
  let pg : SPath (wd D (SKM.wt D ν [up i]) [up r, up q]) s
      (nextSector (true, r) false (nextSector (true, q) false s)) :=
    SPath.two false false hr hq hs
  let qg : SPath (wd D (SKM.wt D ν [up i]) [up q, up r]) s
      (nextSector (true, r) false (nextSector (true, q) false s)) :=
    SPath.two false false hq' hr' rfl
  let pv : SPath (wd D ν [up i])
      (nextSector (true, r) false (nextSector (true, q) false s))
      (nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s))) :=
    .cons _ true _ trivial (.nil _)
  have hp : distinctReservoirTarget (D := D) ν i r q s hr hq hsP = pg.append pv :=
    path_eq_three_distinct hrq hir.symm hiq.symm _ _
  have hqg : distinctReservoirTarget (D := D) ν i q r s hq' hr' rfl = qg.append pv := rfl
  rw [hp, hqg]
  erw [crossEntry_left]
  have hed : HEq
      (crossEntry (P.swappedGens c L) ν [] r q [up i] (pg.append pv) (qg.append pv) Z)
      (P.postCrossNe r q s hr hq hq' hr' hs
        ((P.step (true, i) true _ trivial).obj Z)) := by
    erw [crossEntry_left]
    refine (sandwich_heq _ _ _).trans ?_
    dsimp only [swappedGens]
    erw [P.crossImage_ne c hrq]
    exact P.twoTwo_two_heq
      ⟨up r, SKM.wt D (SKM.wt D ν [up i]) [up q]⟩ ⟨up q, SKM.wt D ν [up i]⟩
      ⟨up q, SKM.wt D (SKM.wt D ν [up i]) [up r]⟩ ⟨up r, SKM.wt D ν [up i]⟩
      (P.crossNeEntry r q _ _ _ _) (t := s) false false false false
      hr hq hq' hr' hs rfl rfl _ _ HEq.rfl
  erw [crossEntry_left] at hed
  refine hed.trans ?_
  symm
  rw [eqToHom_map, eqToHom_map]
  simpa only [eqToHom_refl, Category.comp_id] using sandwich_heq
    (congrArg (fun Y => (P.step (true, r) false s hr).obj
      ((P.step (true, q) false (nextSector (true, r) false s) hq).obj Y))
      (P.probe_obj_sector_transport i hs Z)) rfl
    (P.postCrossNe r q s hr hq hq' hr' hs
      ((P.step (true, i) true _ trivial).obj Z))
end ReservoirEdges

/-- The universal forward unequal-reservoir sector `PᵢRᵣR_q → R_qRᵣPᵢ`.
No factor crossing or parameter polynomial is assumed invertible. -/
theorem distinctReservoir_braid (ν : X) (i r q : I) (s : Sector I)
    (hr : StepValid (true, r) false s)
    (hq : StepValid (true, q) false (nextSector (true, r) false s))
    (hq' : StepValid (true, q) false s)
    (hr' : StepValid (true, r) false (nextSector (true, q) false s))
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hir : i ≠ r) (hiq : i ≠ q) (hrq : r ≠ q)
    (hsP : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))
    (Z : P.H (nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))) :
    braidLeft (P.swappedGens c L) i r q ν
      (distinctReservoirSource ν i r q s hr hq hsP)
      (distinctReservoirTarget ν i q r s hq' hr' rfl) Z =
    braidRight (P.swappedGens c L) i r q ν
      (distinctReservoirSource ν i r q s hr hq hsP)
      (distinctReservoirTarget ν i q r s hq' hr' rfl) Z := by
  classical
  have hs : nextSector (true, q) false (nextSector (true, r) false s) =
      nextSector (true, r) false (nextSector (true, q) false s) := by
    simp only [nextSector, tsub_right_comm]
  let t := nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s))
  let : Subsingleton (SPath (wd D ν [up r, up i, up q]) s t) :=
    ⟨path_eq_three_distinct hir.symm hrq hiq⟩
  let : Subsingleton (SPath (wd D ν [up r, up q, up i]) s t) :=
    ⟨path_eq_three_distinct hrq hir.symm hiq.symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up q, up r]) s t) :=
    ⟨path_eq_three_distinct hiq hir hrq.symm⟩
  let : Subsingleton (SPath (wd D ν [up q, up i, up r]) s t) :=
    ⟨path_eq_three_distinct hiq.symm hrq.symm hir⟩
  let := Fintype.ofFinite (SPath (wd D ν [up r, up i, up q]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up r, up q, up i]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up i, up q, up r]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up q, up i, up r]) s t)
  unfold braidLeft braidRight
  rw [Fintype.sum_subsingleton _ (distinctReservoirTarget (D := D) ν i r q s hr hq hsP),
    Fintype.sum_subsingleton _ (distinctReservoirMiddle (D := D) ν i r q s hr hq hsP),
    Fintype.sum_subsingleton _ (distinctReservoirMiddle (D := D) ν i q r s hq' hr' rfl),
    Fintype.sum_subsingleton _ (distinctReservoirSource (D := D) ν i q r s hq' hr' rfl)]
  symm
  erw [Category.assoc]
  exact rectangle_of_heq
    (P.distinctReservoirSource_obj ν i r q s hr hq hsP Z)
    (P.distinctReservoirSource_obj ν i r q s hr hq hsP Z)
    rfl (P.distinctReservoirTarget_obj ν i r q s hr hq hsP Z) rfl
    (P.distinctReservoir_right ν i r q s hr hq hq' hr' hsP c L Z hrq)
    (P.distinctReservoir_move_heq ν i q r s hq' hr' rfl c L Z hiq hir)
    (P.distinctReservoir_move_heq ν i r q s hr hq hsP c L Z hir hiq)
    (P.distinctReservoir_left ν i r q s hr hq hq' hr' hs hsP c L Z hir hiq hrq)
    (by
      apply heq_of_eq
      refine (eq_of_heq (P.postCrossNe_mixedJ_pair_heq i r q s hr hq hq' hr' hs hsP Z)).trans ?_
      exact (Category.assoc _ _ _).symm)

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
