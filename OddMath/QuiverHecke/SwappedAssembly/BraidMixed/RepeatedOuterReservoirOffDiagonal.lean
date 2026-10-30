/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctProbeSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedBraid
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctReservoirSector

/-! # Two-reservoir repeated-outer off-diagonal braid

The `Pi Rj Ri → Ri Rj Pi` matrix entry of Brundan–Ellis,
*Super Kac–Moody 2-categories*, (1.9). The two intermediate-path families
are classified structurally for arbitrary colours. Spectator vanishing
reduces both sums to the comparison rectangle for the reservoir crossing.
`repeatedReservoir_offDiag_transport` is the arbitrary-terminal entry;
the reverse direction and diagonal corrections are separate obligations.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM
universe u
variable {I X : Type u} [AddCommGroup X] {D : Datum I X}
namespace ProbeReservoir
/-- The `i i j` endpoint supports exactly the two placements of the reservoir
among the repeated colour, with the other colour also in the reservoir. -/
theorem adjacentPost_iij_cases {ν : X} {i j : I} (hij : i ≠ j) {s t : Sector I}
    (hR : StepValid (true, i) false s)
    (hJ : StepValid (true, j) false (nextSector (true, i) false s))
    (e₀ : nextSector (true, j) false (nextSector (true, i) true
      (nextSector (true, i) false s)) = t)
    (e₁ : nextSector (true, j) false (nextSector (true, i) false
      (nextSector (true, i) true s)) = t)
    (p : SPath (wd D ν [up i, up i, up j]) s t) :
    p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩) (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩) false true false hR trivial hJ e₀ ∨
      p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩) (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩) true false false trivial hR hJ e₁ := by
  obtain ⟨a, b, c, ha, hb, hc, e, rfl⟩ := SPath.exists_eq_three p
  have hi := congrArg (fun x : Sector I => x.1 i) (e.trans e₀.symm)
  have hj := congrArg (fun x : Sector I => x.1 j) (e.trans e₀.symm)
  cases a <;> cases b <;> cases c <;>
    first | exact Or.inl rfl | exact Or.inr rfl |
      (exfalso; simp [nextSector, hij, Ne.symm hij] at hi hj)

/-- The middle word `i j i` has two paths in this occupied endpoint. -/
theorem adjacentPost_iji_cases {ν : X} {i j : I} (hij : i ≠ j) {s t : Sector I}
    (hR : StepValid (true, i) false s)
    (hJ : StepValid (true, j) false (nextSector (true, i) false s))
    (hJ₀ : StepValid (true, j) false s)
    (hR₀ : StepValid (true, i) false (nextSector (true, j) false s))
    (e₀ : nextSector (true, i) true (nextSector (true, j) false
      (nextSector (true, i) false s)) = t)
    (e₁ : nextSector (true, i) false (nextSector (true, j) false
      (nextSector (true, i) true s)) = t)
    (p : SPath (wd D ν [up i, up j, up i]) s t) :
    p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩) (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) false false true hR hJ trivial e₀ ∨
      p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩) (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) true false false trivial hJ₀ hR₀ e₁ := by
  obtain ⟨a, b, c, ha, hb, hc, e, rfl⟩ := SPath.exists_eq_three p
  have hi := congrArg (fun x : Sector I => x.1 i) (e.trans e₀.symm)
  have hj := congrArg (fun x : Sector I => x.1 j) (e.trans e₀.symm)
  cases a <;> cases b <;> cases c <;>
    first | exact Or.inl rfl | exact Or.inr rfl |
      (exfalso; simp [nextSector, hij, Ne.symm hij] at hi hj)

/-- The target word `j i i` still supports both repeated-colour placements. -/
theorem adjacentPost_jii_cases {ν : X} {i j : I} (hij : i ≠ j) {s t : Sector I}
    (hJ₀ : StepValid (true, j) false s)
    (hR₀ : StepValid (true, i) false (nextSector (true, j) false s))
    (e₀ : nextSector (true, i) true (nextSector (true, i) false
      (nextSector (true, j) false s)) = t)
    (e₁ : nextSector (true, i) false (nextSector (true, i) true
      (nextSector (true, j) false s)) = t)
    (p : SPath (wd D ν [up j, up i, up i]) s t) :
    p = SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩) (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) false false true hJ₀ hR₀ trivial e₀ ∨
      p = SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩) (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) false true false hJ₀ trivial hR₀ e₁ := by
  obtain ⟨a, b, c, ha, hb, hc, e, rfl⟩ := SPath.exists_eq_three p
  have hi := congrArg (fun x : Sector I => x.1 i) (e.trans e₀.symm)
  have hj := congrArg (fun x : Sector I => x.1 j) (e.trans e₀.symm)
  cases a <;> cases b <;> cases c <;>
    first | exact Or.inl rfl | exact Or.inr rfl |
      (exfalso; simp [nextSector, hij, Ne.symm hij] at hi hj)

theorem adjacentPost_iij_sum {M : Type*} [AddCommMonoid M] {ν : X} {i j : I} (hij : i ≠ j) {s t : Sector I}
    (hR : StepValid (true, i) false s)
    (hJ : StepValid (true, j) false (nextSector (true, i) false s))
    (e₀ : nextSector (true, j) false (nextSector (true, i) true
      (nextSector (true, i) false s)) = t)
    (e₁ : nextSector (true, j) false (nextSector (true, i) false
      (nextSector (true, i) true s)) = t)
    (f : SPath (wd D ν [up i, up i, up j]) s t → M) :
    let := Fintype.ofFinite (SPath (wd D ν [up i, up i, up j]) s t)
    ∑ p, f p = f (SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩) (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩) false true false hR trivial hJ e₀) + f (SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩) (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩) true false false trivial hR hJ e₁) := by
  classical
  let := Fintype.ofFinite (SPath (wd D ν [up i, up i, up j]) s t)
  refine Fintype.sum_eq_add _ _ (by intro h; cases h) ?_
  intro p hp
  rcases adjacentPost_iij_cases hij hR hJ e₀ e₁ p with h | h
  · exact False.elim (hp.1 h)
  · exact False.elim (hp.2 h)

theorem adjacentPost_iji_sum {M : Type*} [AddCommMonoid M] {ν : X} {i j : I} (hij : i ≠ j) {s t : Sector I}
    (hR : StepValid (true, i) false s)
    (hJ : StepValid (true, j) false (nextSector (true, i) false s))
    (hJ₀ : StepValid (true, j) false s)
    (hR₀ : StepValid (true, i) false (nextSector (true, j) false s))
    (e₀ : nextSector (true, i) true (nextSector (true, j) false
      (nextSector (true, i) false s)) = t)
    (e₁ : nextSector (true, i) false (nextSector (true, j) false
      (nextSector (true, i) true s)) = t)
    (f : SPath (wd D ν [up i, up j, up i]) s t → M) :
    let := Fintype.ofFinite (SPath (wd D ν [up i, up j, up i]) s t)
    ∑ p, f p = f (SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩) (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) false false true hR hJ trivial e₀) + f (SPath.three (c₁ := ⟨up i, SKM.wt D ν [up j, up i]⟩) (c₂ := ⟨up j, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) true false false trivial hJ₀ hR₀ e₁) := by
  classical
  let := Fintype.ofFinite (SPath (wd D ν [up i, up j, up i]) s t)
  refine Fintype.sum_eq_add _ _ (by intro h; cases h) ?_
  intro p hp
  rcases adjacentPost_iji_cases hij hR hJ hJ₀ hR₀ e₀ e₁ p with h | h
  · exact False.elim (hp.1 h)
  · exact False.elim (hp.2 h)

theorem adjacentPost_jii_sum {M : Type*} [AddCommMonoid M] {ν : X} {i j : I} (hij : i ≠ j) {s t : Sector I}
    (hJ₀ : StepValid (true, j) false s)
    (hR₀ : StepValid (true, i) false (nextSector (true, j) false s))
    (e₀ : nextSector (true, i) true (nextSector (true, i) false
      (nextSector (true, j) false s)) = t)
    (e₁ : nextSector (true, i) false (nextSector (true, i) true
      (nextSector (true, j) false s)) = t)
    (f : SPath (wd D ν [up j, up i, up i]) s t → M) :
    let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up i]) s t)
    ∑ p, f p = f (SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩) (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) false false true hJ₀ hR₀ trivial e₀) + f (SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩) (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩) false true false hJ₀ trivial hR₀ e₁) := by
  classical
  let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up i]) s t)
  refine Fintype.sum_eq_add _ _ (by intro h; cases h) ?_
  intro p hp
  rcases adjacentPost_jii_cases hij hJ₀ hR₀ e₀ e₁ p with h | h
  · exact False.elim (hp.1 h)
  · exact False.elim (hp.2 h)

variable {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {Sc : Scalars D k}

variable (P : ProbeReservoir k B D Sc)

section Paths
variable (ν : X) (i r q : I) (s : Sector I)
  (hr : StepValid (true, r) false s)
  (hq : StepValid (true, q) false (nextSector (true, r) false s))
  {t : Sector I}
  (e : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) = t)

variable (c : P.CrossCoeff Sc) (L : P.LeftwardData) (Z : P.H t)

/-- Evaluation of the two forward mixed edges. -/
theorem mixedReservoir_move_heq :
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
    by_cases hir : i = r
    · subst r
      erw [swappedGens_cross_self]
      rfl
    · dsimp only [swappedGens]
      erw [P.crossImage_ne c hir]
      rfl
  · refine (crossEntry_right (P.swappedGens c L) ν r i q false hr
      (.cons _ true _ trivial (.cons _ false _ hq (.nil _)))
      (.cons _ false _ hq (.cons _ true _ trivial (.nil _))) Z).trans ?_
    by_cases hiq : i = q
    · subst q
      erw [swappedGens_cross_self]
      rfl
    · dsimp only [swappedGens]
      erw [P.crossImage_ne c hiq]
      rfl

end Paths
section ReservoirEdges
variable (ν : X) (i r : I) (s : Sector I)
  (hr : StepValid (true, r) false s)
  (hq : StepValid (true, i) false (nextSector (true, r) false s))
  (hq' : StepValid (true, i) false s)
  (hr' : StepValid (true, r) false (nextSector (true, i) false s))
  (hs : nextSector (true, i) false (nextSector (true, r) false s) =
    nextSector (true, r) false (nextSector (true, i) false s))
  (hsP : nextSector (true, i) false (nextSector (true, r) false (nextSector (true, i) true s)) =
    nextSector (true, r) false (nextSector (true, i) false (nextSector (true, i) true s)))
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (Z : P.H (nextSector (true, r) false (nextSector (true, i) false (nextSector (true, i) true s))))

/-- The reservoir crossing with the probe on the right, including its endpoint comparison. -/
theorem repeatedReservoir_left (hir : i ≠ r) :
    HEq (crossEntry (P.swappedGens c L) ν [] r i [up i]
      (distinctReservoirTarget ν i r i s hr hq hsP)
      (distinctReservoirTarget ν i i r s hq' hr' rfl) Z)
      ((P.step (true, r) false s hr).map
        ((P.step (true, i) false (nextSector (true, r) false s) hq).map
          (eqToHom (P.probe_obj_sector_transport i hs Z))) ≫
        P.postCrossNe r i s hr hq hq' hr' hs
          ((P.step (true, i) true (nextSector (true, r) false
            (nextSector (true, i) false s)) trivial).obj Z)) := by
  let pg : SPath (wd D (SKM.wt D ν [up i]) [up r, up i]) s
      (nextSector (true, r) false (nextSector (true, i) false s)) :=
    SPath.two false false hr hq hs
  let qg : SPath (wd D (SKM.wt D ν [up i]) [up i, up r]) s
      (nextSector (true, r) false (nextSector (true, i) false s)) :=
    SPath.two false false hq' hr' rfl
  let pv : SPath (wd D ν [up i])
      (nextSector (true, r) false (nextSector (true, i) false s))
      (nextSector (true, r) false (nextSector (true, i) false (nextSector (true, i) true s))) :=
    .cons _ true _ trivial (.nil _)
  have hp : distinctReservoirTarget (D := D) ν i r i s hr hq hsP = pg.append pv :=
by
      rcases adjacentPost_jii_cases hir hr hq hsP hsP (pg.append pv) with h | h
      · exact h.symm
      · cases h
  have hqg : distinctReservoirTarget (D := D) ν i i r s hq' hr' rfl = qg.append pv := rfl
  rw [hp, hqg]
  erw [crossEntry_left]
  have hed : HEq
      (crossEntry (P.swappedGens c L) ν [] r i [up i] (pg.append pv) (qg.append pv) Z)
      (P.postCrossNe r i s hr hq hq' hr' hs
        ((P.step (true, i) true _ trivial).obj Z)) := by
    erw [crossEntry_left]
    refine (sandwich_heq _ _ _).trans ?_
    dsimp only [swappedGens]
    erw [P.crossImage_ne c hir.symm]
    exact P.twoTwo_two_heq
      ⟨up r, SKM.wt D (SKM.wt D ν [up i]) [up i]⟩ ⟨up i, SKM.wt D ν [up i]⟩
      ⟨up i, SKM.wt D (SKM.wt D ν [up i]) [up r]⟩ ⟨up r, SKM.wt D ν [up i]⟩
      (P.crossNeEntry r i _ _ _ _) (t := s) false false false false
      hr hq hq' hr' hs rfl rfl _ _ HEq.rfl
  erw [crossEntry_left] at hed
  refine hed.trans ?_
  symm
  rw [eqToHom_map, eqToHom_map]
  simpa only [eqToHom_refl, Category.comp_id] using sandwich_heq
    (congrArg (fun Y => (P.step (true, r) false s hr).obj
      ((P.step (true, i) false (nextSector (true, r) false s) hq).obj Y))
      (P.probe_obj_sector_transport i hs Z)) rfl
    (P.postCrossNe r i s hr hq hq' hr' hs
      ((P.step (true, i) true _ trivial).obj Z))
end ReservoirEdges



private lemma reservoir_route {C : Type u} [Category C] [Preadditive C]
    {A B V T : C} (f : A ⟶ B) (f' : A ⟶ V) (g : B ⟶ B)
    (h : V ⟶ B) (j : B ⟶ V) (l : V ⟶ V) (r : B ⟶ T) (r' : V ⟶ T)
    (hf : f = 0) (hr : r' = 0) :
    (f ≫ g + f' ≫ h) ≫ r + (f ≫ j + f' ≫ l) ≫ r' = (f' ≫ h) ≫ r := by
  rw [hf, hr]
  simp only [Limits.zero_comp, Limits.comp_zero, zero_add, add_zero]

section Routes
variable (ν : X) (i j : I) (s : Sector I)
  (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (hj₀ : StepValid (true, j) false s)
  (hi₀ : StepValid (true, i) false (nextSector (true, j) false s))
  (e : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) =
    nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)))
  (Z : P.H (nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s))))

lemma repeatedReservoir_left_route (G : P.Generators) (hij : i ≠ j) :
    let n := distinctReservoirSource (D := D) ν i j i s hj₀ hi₀ e
    let m := distinctReservoirTarget (D := D) ν i i j s hi hj rfl
    let a := distinctReservoirMiddle (D := D) ν i j i s hj₀ hi₀ e
    let b := distinctReservoirTarget (D := D) ν i j i s hj₀ hi₀ e
    braidLeft G i j i ν n m Z =
      (crossEntry G ν [] i j [up i] n a Z ≫ crossEntry G ν [up j] i i [] a b Z) ≫
        crossEntry G ν [] j i [up i] b m Z := by
  classical
  dsimp only
  have hf := P.crossEntry_left_three_zero G ν i j i true false false false false true
    Bool.false_ne_true trivial hj₀ hj₀ hi₀ hi₀ trivial e e Z
  have hr := P.crossEntry_left_three_zero G ν j i i false true false false false true
    Bool.false_ne_true hj₀ trivial hi hj hi₀ trivial e rfl Z
  unfold braidLeft
  erw [adjacentPost_jii_sum hij hj₀ hi₀ e e]
  erw [adjacentPost_jii_sum hij hj₀ hi₀ e e, adjacentPost_jii_sum hij hj₀ hi₀ e e]
  exact reservoir_route _ _ _ _ _ _ _ _ hf hr

lemma repeatedReservoir_right_route (G : P.Generators) (hij : i ≠ j) :
    let n := distinctReservoirSource (D := D) ν i j i s hj₀ hi₀ e
    let m := distinctReservoirTarget (D := D) ν i i j s hi hj rfl
    let a := distinctReservoirSource (D := D) ν i i j s hi hj rfl
    let b := distinctReservoirMiddle (D := D) ν i i j s hi hj rfl
    braidRight G i j i ν n m Z =
      (crossEntry G ν [up i] j i [] n a Z ≫ crossEntry G ν [] i i [up j] a b Z) ≫
        crossEntry G ν [up i] i j [] b m Z := by
  classical
  dsimp only
  have hf := crossEntry_right_eq_zero G ν i j i true false (by decide)
    trivial hi (SPath.two false false hj₀ hi₀ e)
    (SPath.two true false trivial hj rfl) Z
  have hr := crossEntry_right_eq_zero G ν i i j true false (by decide)
    trivial hi (SPath.two false false hi hj rfl)
    (SPath.two false true hj trivial rfl) Z
  unfold braidRight
  erw [adjacentPost_iij_sum (ν := ν) hij hi hj rfl rfl]
  erw [adjacentPost_iij_sum (ν := ν) hij hi hj rfl rfl,
    adjacentPost_iij_sum (ν := ν) hij hi hj rfl rfl]
  exact reservoir_route _ _ _ _ _ _ _ _ hf hr

/-- The coefficient-free off-diagonal entry Pi Rj Ri to Ri Rj Pi of
Brundan–Ellis (1.9), retaining the literal finite matrix sums. -/
theorem repeatedReservoir_offDiag (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν
      (distinctReservoirSource ν i j i s hj₀ hi₀ e)
      (distinctReservoirTarget ν i i j s hi hj rfl) Z =
    braidRight (P.swappedGens c L) i j i ν
      (distinctReservoirSource ν i j i s hj₀ hi₀ e)
      (distinctReservoirTarget ν i i j s hi hj rfl) Z := by
  have hs : nextSector (true, i) false (nextSector (true, j) false s) =
      nextSector (true, j) false (nextSector (true, i) false s) := by
    simp only [nextSector, tsub_right_comm]
  rw [P.repeatedReservoir_left_route ν i j s hi hj hj₀ hi₀ e Z _ hij,
    P.repeatedReservoir_right_route ν i j s hi hj hj₀ hi₀ e Z _ hij]
  symm
  erw [Category.assoc]
  exact rectangle_of_heq
    (P.distinctReservoirSource_obj ν i j i s hj₀ hi₀ e Z)
    (P.distinctReservoirSource_obj ν i j i s hj₀ hi₀ e Z)
    rfl (P.distinctReservoirTarget_obj ν i j i s hj₀ hi₀ e Z) rfl
    (P.distinctReservoir_right ν i j i s hj₀ hi₀ hi hj e c L Z hij.symm)
    (P.mixedReservoir_move_heq ν i i j s hi hj rfl c L Z)
    (P.mixedReservoir_move_heq ν i j i s hj₀ hi₀ e c L Z)
    (P.repeatedReservoir_left ν i j s hj₀ hi₀ hi hj hs e c L Z hij)
    (by
      apply heq_of_eq
      refine (eq_of_heq (P.postCrossNe_mixedJ_pair_heq i j i s hj₀ hi₀ hi hj hs e Z)).trans ?_
      exact (Category.assoc _ _ _).symm)
end Routes

/-- The two-reservoir forward off-diagonal field at an arbitrary terminal sector. -/
theorem repeatedReservoir_offDiag_transport (P : ProbeReservoir k B D Sc)
    (ν : X) (i j : I) (s : Sector I)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hj₀ : StepValid (true, j) false s)
    (hi₀ : StepValid (true, i) false (nextSector (true, j) false s))
    {t : Sector I}
    (e₀ : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (e₁ : nextSector (true, i) true (nextSector (true, j) false (nextSector (true, i) false s)) = t)
    (Z : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν
      (SPath.three true false false trivial hj₀ hi₀ e₀)
      (SPath.three false false true hi hj trivial e₁) Z =
    braidRight (P.swappedGens c L) i j i ν
      (SPath.three true false false trivial hj₀ hi₀ e₀)
      (SPath.three false false true hi hj trivial e₁) Z := by
  subst e₁
  exact P.repeatedReservoir_offDiag ν i j s hi hj hj₀ hi₀ e₀ Z c L hij
end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly