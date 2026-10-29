/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SlideNe
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Cross

/-! # The dot slide relations for the swapped generators

The relations (1.8) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, for
the images of the upward crossing and the dot in the swapped action
(`docs/Nondegeneracy/SwappedActionAssembly.md`, §3). The distinct-colour entries
(`SlideNe.lean`) are assembled into the slides `slideL`, `slideR` at every pair of summand
paths; together with the same-colour slides (`SlideSame.lean`) this gives `CrossSlide` for
`P.swappedGens c L`.

## Main results

* `ProbeReservoir.swappedGens_slideNe`: the distinct-colour slides at every pair of paths.
* `ProbeReservoir.swappedGens_crossSlide`: `CrossSlide (P.swappedGens c L)`, for a crossing
  coefficient satisfying its characterizing identities under the inputs F2, F3.
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

/-! ## Transport of a slide identity along equal objects -/

section Transport

variable {C : Type*} [Category C] [Preadditive C] [Linear k C]

theorem slideL_of_heq {A B' A' B'' : C} (hA : A = A') (hB : B' = B'') {a : A ⟶ A} {f : A ⟶ B'}
    {b : B' ⟶ B'} {a' : A' ⟶ A'} {f' : A' ⟶ B''} {b' : B'' ⟶ B''} (ha : HEq a a')
    (hf : HEq f f') (hb : HEq b b') (z : k) (h : a' ≫ f' = z • (f' ≫ b')) :
    a ≫ f = z • (f ≫ b) := by
  subst hA hB
  cases ha; cases hf; cases hb
  exact h

theorem slideR_of_heq {A B' A' B'' : C} (hA : A = A') (hB : B' = B'') {a : A ⟶ A} {f : A ⟶ B'}
    {b : B' ⟶ B'} {a' : A' ⟶ A'} {f' : A' ⟶ B''} {b' : B'' ⟶ B''} (ha : HEq a a')
    (hf : HEq f f') (hb : HEq b b') (z : k) (h : f' ≫ b' = z • (a' ≫ f')) :
    f ≫ b = z • (a ≫ f) := by
  subst hA hB
  cases ha; cases hf; cases hb
  exact h

end Transport

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

theorem pathFunctor_two_obj {c₁ c₂ : Col I X} {t t' : Sector I} (τ₁ τ₂ : Bool)
    (hw₁ : StepValid c₁.l τ₁ t) (hw₂ : StepValid c₂.l τ₂ (nextSector c₁.l τ₁ t))
    (e : nextSector c₂.l τ₂ (nextSector c₁.l τ₁ t) = t') (Z : P.H t')
    (Z₁ : P.H (nextSector c₂.l τ₂ (nextSector c₁.l τ₁ t))) (hZ : HEq Z₁ Z) :
    (P.pathFunctor (SPath.two τ₁ τ₂ hw₁ hw₂ e)).obj Z =
      (P.step c₁.l τ₁ t hw₁).obj ((P.step c₂.l τ₂ _ hw₂).obj Z₁) := by
  subst e; cases hZ; rfl

theorem twoTwo_two_heq (c₁ c₂ d₁ d₂ : Col I X) (f : P.TwoEntry c₁ c₂ d₁ d₂)
    {t s s' : Sector I} (σ₁ σ₂ τ₁ τ₂ : Bool) (hv₁ : StepValid c₁.l σ₁ t)
    (hv₂ : StepValid c₂.l σ₂ (nextSector c₁.l σ₁ t)) (hw₁ : StepValid d₁.l τ₁ t)
    (hw₂ : StepValid d₂.l τ₂ (nextSector d₁.l τ₁ t))
    (e : nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t) = s)
    (e' : nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t) = s') (hs : s = s') (Z : P.H s')
    (Z' : P.H (nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))) (hZ : HEq Z' Z) :
    HEq (P.twoTwo c₁ c₂ d₁ d₂ f (SPath.two σ₁ σ₂ hv₁ hv₂ e) (SPath.two τ₁ τ₂ hw₁ hw₂ e') hs Z)
      (f t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ (e.trans (hs.trans e'.symm)) Z') := by
  subst e e'; cases hZ; rfl

theorem crossImage_ne (c : P.CrossCoeff Sc) {i j : I} (hij : i ≠ j) (ν : X) {t s : Sector I}
    (p : SPath (wd D ν [up i, up j]) t s) (q : SPath (wd D ν [up j, up i]) t s) (Z : P.H s) :
    P.crossImage c i j ν p q Z = P.twoTwo _ _ _ _ (P.crossNeEntry i j _ _ _ _) p q rfl Z := by
  rw [crossImage]
  split_ifs with h
  · exact absurd h hij
  · rfl

/-! ## The dots on two-letter paths -/

theorem leftDot_two_probe_heq (c : P.CrossCoeff Sc) (L : P.LeftwardData) (i j : I) (ν : X)
    {s t : Sector I} (σ₂ : Bool) (hv₂ : StepValid (true, j) σ₂ (nextSector (true, i) true s))
    (e : nextSector (true, j) σ₂ (nextSector (true, i) true s) = t) (Z : P.H t)
    (Z₁ : P.H (nextSector (true, j) σ₂ (nextSector (true, i) true s))) (hZ : HEq Z₁ Z) :
    HEq (leftDot (P.swappedGens c L) i j ν
        (SPath.two true σ₂ trivial hv₂ e : SPath (wd D ν [up i, up j]) s t) Z)
      (P.T.dot i (P.muP_preE i s) ▷ (P.step (true, j) σ₂ _ hv₂).obj Z₁) := by
  subst e; cases hZ
  exact heq_of_eq (P.leftDot_swapped_probe c L i j ν s σ₂ hv₂ Z₁)

theorem leftDot_two_reservoir_heq (c : P.CrossCoeff Sc) (L : P.LeftwardData) (i j : I) (ν : X)
    {s t : Sector I} (hv₁ : StepValid (true, i) false s) (σ₂ : Bool)
    (hv₂ : StepValid (true, j) σ₂ (nextSector (true, i) false s))
    (e : nextSector (true, j) σ₂ (nextSector (true, i) false s) = t) (Z : P.H t)
    (Z₁ : P.H (nextSector (true, j) σ₂ (nextSector (true, i) false s))) (hZ : HEq Z₁ Z) :
    HEq (leftDot (P.swappedGens c L) i j ν
        (SPath.two false σ₂ hv₁ hv₂ e : SPath (wd D ν [up i, up j]) s t) Z)
      (homContentPostDot P.T.obj P.W i s.1 (P.muP s) (P.muM_postE i hv₁)
        ((P.step (true, j) σ₂ _ hv₂).obj Z₁)) := by
  subst e; cases hZ
  exact heq_of_eq (P.leftDot_swapped_reservoir c L i j ν s hv₁ σ₂ hv₂ Z₁)

theorem rightDot_two_probe_heq (c : P.CrossCoeff Sc) (L : P.LeftwardData) (i j : I) (ν : X)
    {s t : Sector I} (σ₁ : Bool) (hv₁ : StepValid (true, i) σ₁ s)
    (e : nextSector (true, j) true (nextSector (true, i) σ₁ s) = t) (Z : P.H t)
    (Z₁ : P.H (nextSector (true, j) true (nextSector (true, i) σ₁ s))) (hZ : HEq Z₁ Z) :
    HEq (rightDot (P.swappedGens c L) i j ν
        (SPath.two σ₁ true hv₁ trivial e : SPath (wd D ν [up i, up j]) s t) Z)
      ((P.step (true, i) σ₁ s hv₁).map (P.T.dot j (P.muP_preE j _) ▷ Z₁)) := by
  subst e; cases hZ
  exact heq_of_eq (P.rightDot_swapped_probe c L i j ν s σ₁ hv₁ Z₁)

theorem rightDot_two_reservoir_heq (c : P.CrossCoeff Sc) (L : P.LeftwardData) (i j : I)
    (ν : X) {s t : Sector I} (σ₁ : Bool) (hv₁ : StepValid (true, i) σ₁ s)
    (hv₂ : StepValid (true, j) false (nextSector (true, i) σ₁ s))
    (e : nextSector (true, j) false (nextSector (true, i) σ₁ s) = t) (Z : P.H t)
    (Z₁ : P.H (nextSector (true, j) false (nextSector (true, i) σ₁ s))) (hZ : HEq Z₁ Z) :
    HEq (rightDot (P.swappedGens c L) i j ν
        (SPath.two σ₁ false hv₁ hv₂ e : SPath (wd D ν [up i, up j]) s t) Z)
      ((P.step (true, i) σ₁ s hv₁).map (homContentPostDot P.T.obj P.W j
        (nextSector (true, i) σ₁ s).1 (P.muP _) (P.muM_postE j hv₂) Z₁)) := by
  subst e; cases hZ
  exact heq_of_eq (P.rightDot_swapped_reservoir c L i j ν s σ₁ hv₁ hv₂ Z₁)

/-! ## The assembled distinct-colour slides -/

/-- **The distinct-colour slides `slideL` and `slideR`** for the swapped generators, at every
pair of summand paths. Only the four pairs of paths with equal right sectors contribute; on
each the slides are those of the corresponding crossing entry. -/
theorem swappedGens_slideNe (c : P.CrossCoeff Sc) (L : P.LeftwardData) (i j : I) (ν : X)
    (hij : i ≠ j) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j]) s t) (q : SPath (wd D ν [up j, up i]) s t) (Z : P.H t) :
    (leftDot (P.swappedGens c L) i j ν p Z ≫ (P.swappedGens c L).cross i j ν p q Z =
      zsign k (D.parity i * D.parity j) •
        ((P.swappedGens c L).cross i j ν p q Z ≫ rightDot (P.swappedGens c L) j i ν q Z)) ∧
    ((P.swappedGens c L).cross i j ν p q Z ≫ leftDot (P.swappedGens c L) j i ν q Z =
      zsign k (D.parity i * D.parity j) •
        (rightDot (P.swappedGens c L) i j ν p Z ≫ (P.swappedGens c L).cross i j ν p q Z)) := by
  have hx : (P.swappedGens c L).cross i j ν p q Z =
      P.twoTwo _ _ _ _ (P.crossNeEntry i j _ _ _ _) p q rfl Z := P.crossImage_ne c hij ν p q Z
  rw [hx]
  obtain ⟨σ₁, σ₂, hv₁, hv₂, e, rfl⟩ := SPath.exists_eq_two p
  obtain ⟨τ₁, τ₂, hw₁, hw₂, e', rfl⟩ := SPath.exists_eq_two q
  have hE := e.trans e'.symm
  have hi := congrArg (fun x : Sector I => x.1 i) hE
  have hj := congrArg (fun x : Sector I => x.1 j) hE
  have hZ' : HEq ((P.castH e').obj Z) Z := P.castH_obj_heq e' Z
  cases σ₁ <;> cases σ₂ <;> cases τ₁ <;> cases τ₂ <;>
    simp [nextSector, hij, Ne.symm hij] at hi hj
  case true.true.true.true =>
    set Z' := (P.castH e').obj Z
    have hs := e.trans (rfl.trans e'.symm)
    have hZ₁ : HEq (hs ▸ Z') Z := (P.sector_heq hs Z').trans hZ'
    have hA := P.pathFunctor_two_obj _ _ hv₁ hv₂ e Z _ hZ₁
    have hB := P.pathFunctor_two_obj _ _ hw₁ hw₂ e' Z _ hZ'
    have hf := P.twoTwo_two_heq _ _ _ _
      (P.crossNeEntry i j (SKM.wt D ν [up j]) (SKM.wt D ν []) (SKM.wt D ν [up i]) (SKM.wt D ν []))
      _ _ _ _ hv₁ hv₂ hw₁ hw₂ e e' rfl Z Z' hZ'
    have hl := P.leftDot_two_probe_heq c L i j ν _ hv₂ e Z _ hZ₁
    have hr := P.rightDot_two_probe_heq c L j i ν _ hw₁ e' Z _ hZ'
    have hl' := P.leftDot_two_probe_heq c L j i ν _ hw₂ e' Z _ hZ'
    have hr' := P.rightDot_two_probe_heq c L i j ν _ hv₁ e Z _ hZ₁
    have h1 := P.preCrossNe_slideL i j hij s hs Z'
    have h2 := P.preCrossNe_slideR i j hij s hs Z'
    have hf' : HEq _ (P.preCrossNe i j s hs Z') := hf
    exact ⟨slideL_of_heq hA hB hl hf' hr _ h1, slideR_of_heq hA hB hr' hf' hl' _ h2⟩
  case false.false.false.false =>
    set Z' := (P.castH e').obj Z
    have hs := e.trans (rfl.trans e'.symm)
    have hZ₁ : HEq (hs ▸ Z') Z := (P.sector_heq hs Z').trans hZ'
    have hA := P.pathFunctor_two_obj _ _ hv₁ hv₂ e Z _ hZ₁
    have hB := P.pathFunctor_two_obj _ _ hw₁ hw₂ e' Z _ hZ'
    have hf := P.twoTwo_two_heq _ _ _ _
      (P.crossNeEntry i j (SKM.wt D ν [up j]) (SKM.wt D ν []) (SKM.wt D ν [up i]) (SKM.wt D ν []))
      _ _ _ _ hv₁ hv₂ hw₁ hw₂ e e' rfl Z Z' hZ'
    have hf' : HEq _ (P.postCrossNe i j s hv₁ hv₂ hw₁ hw₂ hs Z') := hf
    exact ⟨slideL_of_heq hA hB (P.leftDot_two_reservoir_heq c L i j ν hv₁ false hv₂ e Z _ hZ₁)
      hf' (P.rightDot_two_reservoir_heq c L j i ν false hw₁ hw₂ e' Z _ hZ') _
      (P.postCrossNe_slideL i j hij s hv₁ hv₂ hw₁ hw₂ hs Z'),
      slideR_of_heq hA hB (P.rightDot_two_reservoir_heq c L i j ν false hv₁ hv₂ e Z _ hZ₁) hf'
      (P.leftDot_two_reservoir_heq c L j i ν hw₁ false hw₂ e' Z _ hZ') _
      (P.postCrossNe_slideR i j hij s hv₁ hv₂ hw₁ hw₂ hs Z')⟩
  case true.false.false.true =>
    set Z' := (P.castH e').obj Z
    have hA := P.pathFunctor_two_obj _ _ hv₁ hv₂ e Z Z' hZ'
    have hB := P.pathFunctor_two_obj _ _ hw₁ hw₂ e' Z _ hZ'
    have hf := P.twoTwo_two_heq _ _ _ _
      (P.crossNeEntry i j (SKM.wt D ν [up j]) (SKM.wt D ν []) (SKM.wt D ν [up i]) (SKM.wt D ν []))
      _ _ _ _ hv₁ hv₂ hw₁ hw₂ e e' rfl Z Z' hZ'
    have hf' : HEq _ (P.mixedJ i j s hv₂ Z').hom := hf
    obtain ⟨h1, h2⟩ := P.mixedJ_ne_slides i j s hv₂ Z'
    exact ⟨slideL_of_heq hA hB (P.leftDot_two_probe_heq c L i j ν false hv₂ e Z Z' hZ')
      hf' (P.rightDot_two_probe_heq c L j i ν false hw₁ e' Z Z' hZ') _ h1,
      slideR_of_heq hA hB (P.rightDot_two_reservoir_heq c L i j ν true hv₁ hv₂ e Z Z' hZ') hf'
      (P.leftDot_two_reservoir_heq c L j i ν hw₁ true hw₂ e' Z Z' hZ') _ h2⟩
  case false.true.true.false =>
    set Z' := (P.castH e').obj Z
    have hA := P.pathFunctor_two_obj _ _ hv₁ hv₂ e Z Z' hZ'
    have hB := P.pathFunctor_two_obj _ _ hw₁ hw₂ e' Z _ hZ'
    have hf := P.twoTwo_two_heq _ _ _ _
      (P.crossNeEntry i j (SKM.wt D ν [up j]) (SKM.wt D ν []) (SKM.wt D ν [up i]) (SKM.wt D ν []))
      _ _ _ _ hv₁ hv₂ hw₁ hw₂ e e' rfl Z Z' hZ'
    have hf' : HEq _ ((P.mixedJ j i s hw₂ Z').inv ≫ P.mixedQ j i s hw₂ Z') := hf
    obtain ⟨h1, h2⟩ := P.mixedJinvQ_ne_slides i j s hw₂ Z'
    exact ⟨slideL_of_heq hA hB (P.leftDot_two_reservoir_heq c L i j ν hv₁ true hv₂ e Z Z' hZ')
      hf' (P.rightDot_two_reservoir_heq c L j i ν true hw₁ hw₂ e' Z Z' hZ') _ h1,
      slideR_of_heq hA hB (P.rightDot_two_probe_heq c L i j ν false hv₁ e Z Z' hZ') hf'
      (P.leftDot_two_probe_heq c L j i ν false hw₂ e' Z Z' hZ') _ h2⟩

open Classical in
/-- **The dot slide relations (1.8) for the swapped generators**, for a crossing coefficient
satisfying its characterizing identities under the inputs F2, F3 of the written proof
(`CrossCoeffInputs`). -/
theorem swappedGens_crossSlide (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (hin : P.CrossCoeffInputs) (L : P.LeftwardData) : CrossSlide (P.swappedGens c L) where
  slideL i j ν hij _ _ p q Z := (P.swappedGens_slideNe c L i j ν hij p q Z).1
  slideLEq i ν _ _ p q Z := (P.swappedGens_slideEq c hc hin L i ν p q Z).1
  slideR i j ν hij _ _ p q Z := (P.swappedGens_slideNe c L i j ν hij p q Z).2
  slideREq i ν _ _ p q Z := (P.swappedGens_slideEq c hc hin L i ν p q Z).2

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
