/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalRouquierFamily
import OddMath.QuiverHecke.CyclotomicAction.RouquierKernelComparison

/-!
# The weight-level Rouquier mate, dotted units and dotted counits through the kernels

`RouquierKernelComparison` identifies, at one height, the dotted unit, the dotted counit and
the Rouquier mate of the cyclotomic action with the dotted cup `j_m ⊗ M`, the dotted cap
`κ_m ⊗ M` and the mate kernel `s ⊗ M`. This file carries these identifications through the
content blocks and the weight-indexed products of `globalRouquierData`, the data entering the
local inversion criterion of Kang–Kashiwara–Oh (KKO I, arXiv:1206.5933v2) as in
`docs/Nondegeneracy/DeformedMatrixComparison.md`, displays (2) and (4).

Write `d_m = rouquierDotSign p m`, `p = |i|`. At the content level:

* `heightContentMate`: the content mate (unit, crossing, counit, with all height transports)
  is minus `contentMateKernel`, the mate kernel tensored with the module;
* `contentUnit_dotPow`: the unit followed by the `m`-th dot power is `d_m` times
  `contentCupKernel`;
* `contentDotPow_counit`: the `m`-th dot power followed by the counit is `d_m` times
  `contentCapKernel`.

At the weight level, for a block `β` and its successor `blockSucc β`:

* `globalRouquierMate_app_blockSucc`: the component of the weight-level `rouquierMate` of the
  signed crossing is the transported `contentMateKernel`, up to the canonical `eqToHom`s;
* `globalActionDotPow_app_blockSucc`: the `m`-th power of the weight-level dot is the
  transported content dot power;
* `globalDottedCounit_app_blockSucc`: the dotted counit is `d_m` times the transported
  `contentCapKernel`;
* `globalDottedUnit_app`: the dotted unit is `d_m` times `contentCupKernel`, followed by the
  canonical identification of objects.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] [DecidableEq I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

section SCatEven
variable {A B : SCat k}

omit [Fintype I] [DecidableEq I] in
@[simp] theorem scat_whiskerLeft_id {C : SCat k} (F : A ⟶ B) (G : B ⟶ C) :
    F ◁ 𝟙 G = 𝟙 (F ≫ G) := by
  apply SCat.hom_ext <;> intro Z <;> rfl

omit [Fintype I] [DecidableEq I] in
@[simp] theorem scat_id_whiskerRight {C : SCat k} (F : A ⟶ B) (G : B ⟶ C) :
    𝟙 F ▷ G = 𝟙 (F ≫ G) := by
  apply SCat.hom_ext <;> intro Z <;> simp

omit [Fintype I] [DecidableEq I] in
/-- The Rouquier mate in `𝔖ℭ𝔞𝔱` with even unit and counit, componentwise: the unit, then the
crossing under `F₂`, then the counit under `F₂ E₂`. -/
theorem scat_rouquierMate_app {a b c : SCat k} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c}
    {F₂ : c ⟶ b} (A₁ : SKM.SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SKM.SuperAdjunction (k := k) E₂ F₂) (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (hu : ∀ Z, A₂.unit.app 1 Z = 0) (hc : ∀ Z, A₁.counit.app 1 Z = 0) (r : ZMod 2)
    (Z : b.carrier) :
    (SKM.rouquierMate A₁ A₂ t).app r Z =
      A₂.unit.app 0 (Superfunctor.obj (F₁ ≫ E₁) Z) ≫
        Superfunctor.map F₂ (t.app r (Superfunctor.obj F₁ Z)) ≫
          Superfunctor.map F₂ (Superfunctor.map E₂ (A₁.counit.app 0 Z)) := by
  rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) r with rfl | rfl
  · simp [SKM.rouquierMate, hu, hc]
  · simp [SKM.rouquierMate, hu, hc]

end SCatEven

section Content
variable (i : I)

/-! ### Dotted units and counits on content blocks -/

end Content

section Weight
variable (i : I) (Λ : X) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

end Weight
end OddMath.QuiverHecke.CyclotomicAction
