/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Matrices

/-! # The out-of-window `♦`-cups and caps in the swapped layer representation

The relations `dcupZero` and `dcapZero` of `OddMath.SKM.Presentation` say that the `♦`-cup
`dcup i n` with rightmost weight `ν` vanishes when `n ≥ ⟨hᵢ, ν⟩`, and the `♦`-cap `dcap i n`
vanishes when `n ≥ -⟨hᵢ, ν⟩`. These generators are the matrix entries of the inverses in
Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, (2.8)–(2.9); outside the
height windows of (1.13)–(1.14) there is no such entry.

In the swapped Hom construction (`docs/Nondegeneracy/SwappedActionAssembly.md`, §3, last
row of the table, and §4, (A7)) these generators are assigned zero outside their windows.
This file proves `WindowZeroRelations` for the swapped layer representation from exactly that
assignment (`DcupDcapWindowZero`): a layer whose generator image vanishes acts by zero
(`layerMap_eq_zero`), so each relation evaluates to zero after any whiskering.

The proof uses no property of the generator images inside the windows; in particular it
does not depend on the normalization of the even-colour bubbles at height zero (at height
zero both windows are empty and every `♦`-cup and cap is assigned zero).

Main declarations: `ProbeReservoir.layerMap_eq_zero`,
`ProbeReservoir.DcupDcapWindowZero`, `ProbeReservoir.windowZeroRelations`.
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

/-- The Hom-sector functor of one strand is additive. -/
private instance step_additive (l : Letter I) (side : Bool) (s : Sector I) (hv : StepValid l side s) :
    (P.step l side s hv).Additive := by
  obtain ⟨_ | _, i⟩ := l <;> cases side <;>
    (dsimp only [step, homContentPreE, homContentPreF]; infer_instance)

/-- The Hom-sector functor of a path is additive. -/
private instance pathFunctor_additive :
    {w : List (Col I X)} → {s t : Sector I} → (p : SPath w s t) → (P.pathFunctor p).Additive
  | _, _, _, .nil _ => by rw [pathFunctor_nil]; infer_instance
  | _, _, _, .cons c side s hv p => by
    have := pathFunctor_additive p
    rw [pathFunctor_cons]; infer_instance

variable {P} {Gs Ys : ∀ s, P.H s}

/-- A layer whose generator image has only zero components acts by zero. -/
theorem layerMap_eq_zero (gens : P.Generators) (L : Layer (SKM.sig D))
    (h : ∀ {t s : Sector I} (p : SPath (wd D L.gen.2 L.gen.1.dom) t s)
      (p' : SPath (wd D L.gen.2 L.gen.1.cod) t s) (Z : P.H s), gens.image L.gen p p' Z = 0) :
    layerMap (Gs := Gs) (Ys := Ys) gens L = 0 := by
  ext x
  funext sl sr q
  simp only [layerMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
  unfold layerFun
  split_ifs with hL
  · refine Finset.sum_eq_zero fun pg _ => ?_
    simp only [layerEntry, h, Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
  · rfl

/-- The swapped generator images vanish outside the height windows: the `♦`-cup with label
`n` and rightmost weight `ν` when `⟨hᵢ, ν⟩ ≤ n`, and the `♦`-cap when `-⟨hᵢ, ν⟩ ≤ n`
(`SwappedActionAssembly.md`, §3 and (A7)). -/
structure DcupDcapWindowZero (gens : P.Generators) : Prop where
  dcup : ∀ (i : I) (n : ℕ) (ν : X), D.h i ν ≤ n → ∀ {t s : Sector I}
    (p : SPath (wd D ν (Shape.dcup i n).dom) t s) (p' : SPath (wd D ν (Shape.dcup i n).cod) t s)
    (Z : P.H s), gens.dcup i n ν p p' Z = 0
  dcap : ∀ (i : I) (n : ℕ) (ν : X), -D.h i ν ≤ n → ∀ {t s : Sector I}
    (p : SPath (wd D ν (Shape.dcap i n).dom) t s) (p' : SPath (wd D ν (Shape.dcap i n).cod) t s)
    (Z : P.H s), gens.dcap i n ν p p' Z = 0

variable (Gs Ys) in
/-- **`WindowZeroRelations` for the swapped layer representation**: the relations `dcupZero`
and `dcapZero` hold, whiskered arbitrarily, as soon as the out-of-window `♦`-cups and caps
are assigned zero. -/
theorem windowZeroRelations {gens : P.Generators} (hz : DcupDcapWindowZero gens) :
    WindowZeroRelations Sc (P.layerRep Gs Ys gens) := by
  intro r hr u v _
  cases r with
  | dcupZero i ν n hn =>
    change (P.layerRep Gs Ys gens).toLocal.evalW _ _ u v (SKM.relation D Sc (SKM.Rel.dcupZero i ν n hn)) = 0
    have h0 : (P.layerRep Gs Ys gens).act
        ((SKM.lay D ν [] (Shape.dcup i n) []).whisker u v) = 0 :=
      layerMap_eq_zero gens _ fun p p' Z => hz.dcup i n ν hn p p' Z
    ext x
    simp [SKM.relation, SKM.dg, SKM.dcupL, SKM.layList, LayerRep.toLocal, h0]
  | dcapZero i ν n hn =>
    change (P.layerRep Gs Ys gens).toLocal.evalW _ _ u v (SKM.relation D Sc (SKM.Rel.dcapZero i ν n hn)) = 0
    have h0 : (P.layerRep Gs Ys gens).act
        ((SKM.lay D ν [] (Shape.dcap i n) []).whisker u v) = 0 :=
      layerMap_eq_zero gens _ fun p p' Z => hz.dcap i n ν hn p p' Z
    ext x
    simp [SKM.relation, SKM.dg, SKM.dcapL, SKM.layList, LayerRep.toLocal, h0]
  | _ => simp [relGroup] at hr

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
