/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.InterchangePostPair

/-! # Transport for a probe crossing two reservoir colours

A transport-aware form of the shifted interchange triangle. The crossing is
expanded to the same right-associated expression as the prescribed `postCrossNe`.
This is infrastructure for the one-probe braid sector, not yet a theorem about
`braidLeft` and `braidRight`. Source target: Brundan–Ellis,
arXiv:1701.04133v2, Definition 1.5, equation (1.9).
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

/-- The reservoir triangle retains the equality transport on the reversed path. -/
theorem resCore_mixedInterchange_transport (W : RouquierFamily (k := k) (B := B) D)
    (i j r : I) (β : I →₀ ℕ) {a a' b c d : X} (ha : a = a')
    (h₁ : a + D.α j = b) (h₂ : b + D.α i = d)
    (h₃ : a + D.α i = c) (h₄ : c + D.α j = d) (h₃' : a' + D.α i = c)
    {x y : B} (E : x ⟶ y) (Z : y ⟶ W.obj a) (Z' : y ⟶ W.obj a')
    (hZ : HEq Z Z') (V : x ⟶ W.obj a) (hV : E ≫ Z = V)
    (eS : (homParityShift (k := k) (homContentShift D i (β + Finsupp.single r 1))).obj
        (Z ≫ W.E i h₃) =
      (homParityShift (k := k) (homContentShift D i (β + Finsupp.single r 1))).obj
        (Z' ≫ W.E i h₃'))
    (eV : (homParityShift (k := k) (homContentShift D i β)).obj (V ≫ W.E i h₃) =
      (homParityShift (k := k) (homContentShift D i β)).obj ((E ≫ Z') ≫ W.E i h₃')) :
    let ki := homContentShift D i β
    let kj := homContentShift D j β
    let ui := homContentShift D i (β + Finsupp.single r 1)
    let uj := homContentShift D j (β + Finsupp.single r 1)
    E ◁ ((postPairIso (k := k) (W.E i h₂) Z (W.E j h₁) ui uj).hom ≫
        (homParityShift (k := k) (uj + ui)).map
          ((associator Z (W.E j h₁) (W.E i h₂)).hom ≫
            Z ◁ W.cross i j h₁ h₂ h₃ h₄ ≫ (associator Z (W.E i h₃) (W.E j h₄)).inv) ≫
        eqToHom (by rw [add_comm]) ≫
        (postPairIso (k := k) (W.E j h₄) Z (W.E i h₃) uj ui).inv ≫
        (homParityShift (k := k) uj).map (eqToHom eS ▷ W.E j h₄)) ≫
      (homMixedInterchange (k := k) E (W.E j h₄) uj kj
        ((homParityShift (k := k) ui).obj (Z' ≫ W.E i h₃'))).hom ≫
      (homParityShift (k := k) kj).map
        ((homMixedInterchange (k := k) E (W.E i h₃') ui ki Z').hom ▷ W.E j h₄) =
    (homMixedInterchange (k := k) E (W.E i h₂) ui ki
      ((homParityShift (k := k) uj).obj (Z ≫ W.E j h₁))).hom ≫
      (homParityShift (k := k) ki).map
        ((homMixedInterchange (k := k) E (W.E j h₁) uj kj Z).hom ▷ W.E i h₂) ≫
      (homParityShift (k := k) ki).map
        ((homParityShift (k := k) kj).map (eqToHom hV ▷ W.E j h₁) ▷ W.E i h₂) ≫
      (postPairIso (k := k) (W.E i h₂) V (W.E j h₁) ki kj).hom ≫
      (homParityShift (k := k) (kj + ki)).map
        ((associator V (W.E j h₁) (W.E i h₂)).hom ≫
          V ◁ W.cross i j h₁ h₂ h₃ h₄ ≫ (associator V (W.E i h₃) (W.E j h₄)).inv) ≫
      eqToHom (by rw [add_comm]) ≫
      (postPairIso (k := k) (W.E j h₄) V (W.E i h₃) kj ki).inv ≫
        (homParityShift (k := k) kj).map (eqToHom eV ▷ W.E j h₄) := by
  subst a'
  cases hZ
  subst V
  dsimp only
  simp only [eqToHom_refl, TwoSupercategory.id_whiskerRight (R := k)]
  rw [(homParityShift (k := k) (homContentShift D j (β + Finsupp.single r 1))).map_id]
  rw [(homParityShift (k := k) (homContentShift D j β)).map_id]
  simp only [Category.comp_id]
  rw [TwoSupercategory.id_whiskerRight (R := k),
    (homParityShift (k := k) (homContentShift D i β)).map_id,
    (homParityShift (k := k) (homContentShift D j β)).map_id]
  simp only [Category.id_comp, Category.comp_id]
  simpa only [resCore, Category.assoc] using
    resCore_mixedInterchange_pair W i j r β h₁ h₂ h₃ h₄ E Z

variable (P : ProbeReservoir k B D Sc)

/-- Probe evaluation commutes with transport of the reservoir sector. -/
theorem probe_obj_sector_transport (i : I) {s t : Sector I} (h : s = t)
    (Z : P.H (nextSector (true, i) true t)) :
    (P.step (true, i) true s trivial).obj ((congrArg (nextSector (true, i) true) h) ▸ Z) =
      h ▸ (P.step (true, i) true t trivial).obj Z := by
  subst t
  rfl

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
