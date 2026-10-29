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
theorem scat_comp_app_of_even_left {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H)
    (hx : ∀ Z, x.app 1 Z = 0) (r : ZMod 2) (Z : A.carrier) :
    (x ≫ y).app r Z = x.app 0 Z ≫ y.app r Z := by
  rw [SCat.comp_app, hx, Limits.zero_comp, add_zero]

omit [Fintype I] [DecidableEq I] in
theorem scat_comp_app_of_even_right {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H)
    (hy : ∀ Z, y.app 1 Z = 0) (r : ZMod 2) (Z : A.carrier) :
    (x ≫ y).app r Z = x.app r Z ≫ y.app 0 Z := by
  rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) r with rfl | rfl
  · rw [SCat.comp_app_zero, hy, Limits.comp_zero, add_zero]
  · rw [SCat.comp_app_one, hy, Limits.comp_zero, zero_add]

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

omit [Fintype I] [DecidableEq I] in
/-- Components of a composite of homogeneous 2-morphisms in `𝔖ℭ𝔞𝔱`. -/
theorem scat_comp_app_of_mem {F G H : A ⟶ B} {x : F ⟶ G} {y : G ⟶ H} {s t : ZMod 2}
    (hx : x ∈ parity (R := k) F G s) (hy : y ∈ parity (R := k) G H t) (Z : A.carrier) :
    (x ≫ y).app (s + t) Z = x.app s Z ≫ y.app t Z := by
  have hx' := Superfunctor.mem_parity_iff_isHomogeneous.1 hx
  have hy' := Superfunctor.mem_parity_iff_isHomogeneous.1 hy
  rw [SCat.comp_app]
  rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) s with rfl | rfl
  · have h1 := congrFun (hx' 1 (by decide)) Z
    simp only [Pi.zero_apply] at h1
    simp only [h1, Limits.zero_comp, add_zero, zero_add]
  · have e : (1 : ZMod 2) + t + 1 = t := by
      rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) t with rfl | rfl <;> decide
    have h0 := congrFun (hx' 0 (by decide)) Z
    simp only [Pi.zero_apply] at h0
    simp only [h0, Limits.zero_comp, zero_add, e]

end SCatEven

omit [Fintype I] [DecidableEq I] in
theorem natTrans_app_of_eq {C₁ C₂ : Type*} [Category C₁] [Category C₂] {F G : C₁ ⥤ C₂}
    (α : F ⟶ G) {Z Z' : C₁} (e : Z = Z') :
    α.app Z = eqToHom (congrArg F.obj e) ≫ α.app Z' ≫ eqToHom (congrArg G.obj e).symm := by
  subst e
  simp

omit [Fintype I] [DecidableEq I] in
theorem eqToHom_map_id_eqToHom {C₁ C₂ : Type*} [Category C₁] [Category C₂] (F : C₁ ⥤ C₂)
    {Z : C₁} {A : C₂} (e : A = F.obj Z) :
    eqToHom e ≫ F.map (𝟙 Z) ≫ eqToHom e.symm = 𝟙 A := by
  subst e
  simp

section Content
variable (i : I)

/-- The mate kernel `s ⊗ N` on a content block of height `|β| + 1`, between the induced
restriction and the restricted induction. -/
def contentMateKernel (β₀ : Multiset I)
    (N : ObjectProperty.FullSubcategory
      (heightContentSupported D Sc a ha (β₀.card + 1) (({i} : Multiset I) + β₀))) :
    (heightContentInduction D Sc i a ha β₀.card β₀).obj
        ((heightContentRestriction D Sc i a ha β₀.card β₀ rfl).obj N) ⟶
      (heightContentRestriction D Sc i a ha (β₀.card + 1) (({i} : Multiset I) + β₀) (card_of_add (β := β₀) (δ := ({i} : Multiset I) + β₀) i rfl).symm).obj
        ((heightContentInduction D Sc i a ha (β₀.card + 1) (({i} : Multiset I) + β₀)).obj N) :=
  ⟨(SuperBimodule.assoc (heightInductionCorner D Sc i a ha β₀.card)
      (heightRestrictionCorner D Sc i a ha β₀.card) N.obj).inv ≫
    SuperBimodule.whiskerRight (rouquierMateKernel D Sc i a ha β₀.card) N.obj ≫
    (SuperBimodule.assoc (heightRestrictionCorner D Sc i a ha (β₀.card + 1))
      (heightInductionCorner D Sc i a ha (β₀.card + 1)) N.obj).hom⟩

omit [DecidableEq I] in
theorem contentMateKernel_hom (β₀ : Multiset I)
    (N : ObjectProperty.FullSubcategory
      (heightContentSupported D Sc a ha (β₀.card + 1) (({i} : Multiset I) + β₀))) :
    (contentMateKernel D Sc a ha i β₀ N).hom =
      (SuperBimodule.assoc (heightInductionCorner D Sc i a ha β₀.card)
          (heightRestrictionCorner D Sc i a ha β₀.card) N.obj).inv ≫
        SuperBimodule.whiskerRight (rouquierMateKernel D Sc i a ha β₀.card) N.obj ≫
        (SuperBimodule.assoc (heightRestrictionCorner D Sc i a ha (β₀.card + 1))
          (heightInductionCorner D Sc i a ha (β₀.card + 1)) N.obj).hom := rfl

omit [DecidableEq I] in
theorem heightContentInduction_obj_obj (n : ℕ) (β : Multiset I)
    (M : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)) :
    ((heightContentInduction D Sc i a ha n β).toFunctor.obj M).obj =
      SuperBimodule.tensor (heightInductionCorner D Sc i a ha n) M.obj := rfl

omit [DecidableEq I] in
theorem heightContentRestriction_obj_obj (n : ℕ) (β : Multiset I) (hβ : β.card = n)
    (M : ObjectProperty.FullSubcategory
      (heightContentSupported D Sc a ha (n + 1) (({i} : Multiset I) + β))) :
    ((heightContentRestriction D Sc i a ha n β hβ).toFunctor.obj M).obj =
      SuperBimodule.tensor (heightRestrictionCorner D Sc i a ha n) M.obj := rfl

omit [Fintype I] [DecidableEq I] in
theorem superfunctor_id_toFunctor_obj {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] (M : C) : (Superfunctor.id k C).toFunctor.obj M = M := rfl

omit [DecidableEq I] in
theorem heightContentUnit_hom (n : ℕ) (β : Multiset I) (hβ : β.card = n)
    (M : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)) :
    ((heightContentAdjunction D Sc i a ha n β hβ).unit.app M).hom =
      heightSuperUnitComponent D Sc i a ha n M.obj := rfl

omit [DecidableEq I] in
theorem heightContentCounit_hom (n : ℕ) (β : Multiset I) (hβ : β.card = n)
    (M : ObjectProperty.FullSubcategory
      (heightContentSupported D Sc a ha (n + 1) (({i} : Multiset I) + β))) :
    ((heightContentAdjunction D Sc i a ha n β hβ).counit.app M).hom =
      heightSuperCounitComponent D Sc i a ha n M.obj := rfl

omit [DecidableEq I] in
theorem heightContentRestriction_map_hom (n : ℕ) (β : Multiset I) (hβ : β.card = n)
    {M M' : ObjectProperty.FullSubcategory
      (heightContentSupported D Sc a ha (n + 1) (({i} : Multiset I) + β))} (f : M ⟶ M') :
    ((heightContentRestriction D Sc i a ha n β hβ).toFunctor.map f).hom =
      SuperBimodule.whiskerLeft (heightRestrictionCorner D Sc i a ha n) f.hom := rfl

omit [DecidableEq I] in
theorem heightContentInduction_map_hom (n : ℕ) (β : Multiset I)
    {M M' : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)}
    (f : M ⟶ M') :
    ((heightContentInduction D Sc i a ha n β).toFunctor.map f).hom =
      SuperBimodule.whiskerLeft (heightInductionCorner D Sc i a ha n) f.hom := rfl

omit [Fintype I] [DecidableEq I] in
theorem superfunctor_id_map {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {M M' : C} (f : M ⟶ M') : (Superfunctor.id k C).map f = f := rfl

omit [Fintype I] [DecidableEq I] in
theorem fullHomEquiv_apply' {C : Type*} [Category C] [Preadditive C] [Linear k C]
    (P : ObjectProperty C) (M N : P.FullSubcategory) (f : M ⟶ N) :
    fullHomEquiv (k := k) P M N f = f.hom := rfl

omit [DecidableEq I] in
/-- The diagonal component of the height crossing, at the parity of its colour. -/
theorem heightSuperInductionCrossing_app_self (n : ℕ)
    (Z : HeightModules D Sc a ha n) :
    (heightSuperInductionCrossing D Sc i i a ha n).app (D.parity i) Z =
      heightInductionCrossingApp D Sc i i a ha n Z := by
  simp [heightSuperInductionCrossing, zmod2_mul_self]

omit [DecidableEq I] in
theorem heightContentCastUnit_app_self {m : ℕ} {γ : Multiset I} (hm : m = m) (hγ : γ = γ)
    (Z : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)) :
    (heightContentCastAdjunction D Sc a ha hm hγ).unit.app Z = 𝟙 Z := by
  cases hm
  cases hγ
  rfl

omit [DecidableEq I] in
theorem heightContentCastCounit_app_self {m : ℕ} {γ : Multiset I} (hm : m = m) (hγ : γ = γ)
    (Z : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)) :
    (heightContentCastAdjunction D Sc a ha hm hγ).counit.app Z = 𝟙 Z := by
  cases hm
  cases hγ
  rfl

omit [DecidableEq I] in
/-- The mate on content blocks, without height transports. -/
theorem heightContentMate_self (β₀ : Multiset I)
    (hm : (({i} : Multiset I) + β₀).card = β₀.card + 1)
    (hc : ({i} : Multiset I) + (({i} : Multiset I) + β₀) =
      ({i} : Multiset I) + (({i} : Multiset I) + β₀))
    (N : ObjectProperty.FullSubcategory
      (heightContentSupported D Sc a ha (β₀.card + 1) (({i} : Multiset I) + β₀)))
    (O O' : ObjectProperty.FullSubcategory
      (heightContentSupported D Sc a ha (β₀.card + 1) (({i} : Multiset I) + β₀))) :
    ∀ (a₁ : O = _) (a₂ : _ = _) (a₃ : _ = _) (a₄ : _ = O') (e₁ : O = _) (e₂ : _ = O'),
    eqToHom a₁ ≫
    (heightContentAdjunction D Sc i a ha (β₀.card + 1) (({i} : Multiset I) + β₀) hm).unit.app
        ((heightContentInduction D Sc i a ha β₀.card β₀).obj
          ((heightContentRestriction D Sc i a ha β₀.card β₀ rfl).obj N)) ≫ eqToHom a₂ ≫
      (heightContentRestriction D Sc i a ha (β₀.card + 1) (({i} : Multiset I) + β₀) hm).toFunctor.map
        ((heightBlockCross D Sc a ha i i β₀.card β₀
          (({i} : Multiset I) + (({i} : Multiset I) + β₀)) hc).app (D.parity i)
          ((heightContentRestriction D Sc i a ha β₀.card β₀ rfl).obj N)) ≫ eqToHom a₃ ≫
      (heightContentRestriction D Sc i a ha (β₀.card + 1) (({i} : Multiset I) + β₀) hm).toFunctor.map
        ((heightContentInduction D Sc i a ha (β₀.card + 1) (({i} : Multiset I) + β₀)).toFunctor.map
          ((heightContentAdjunction D Sc i a ha β₀.card β₀ rfl).counit.app N)) ≫ eqToHom a₄ =
      -(eqToHom e₁ ≫ contentMateKernel D Sc a ha i β₀ N ≫ eqToHom e₂) := by
  intro a₁ a₂ a₃ a₄ e₁ e₂
  subst a₁ a₄
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply (fullHomEquiv (k := k) _ _ _).injective
  rw [map_neg]
  simp only [fullHomEquiv_apply', ObjectProperty.FullSubcategory.comp_hom,
    heightContentUnit_hom, heightContentCounit_hom, heightContentRestriction_map_hom,
    heightContentInduction_map_hom, heightBlockCross_app, heightSuperInductionCrossing_app_self]
  dsimp only [heightContentInduction_obj_obj, heightContentRestriction_obj_obj, Superfunctor.obj]
  rw [contentMateKernel_hom]
  exact heightRouquierMate_eq D Sc i a ha β₀.card N.obj

omit [DecidableEq I] in
/-- **The mate on content blocks**: unit, crossing `ψ` and counit, with height transports, are
minus the transported mate kernel. -/
theorem heightContentMate (β₀ : Multiset I) {m₁ m₂ : ℕ} {γ₁ γ₂ : Multiset I}
    (p₁ : β₀.card + 1 = m₁) (hγ₁ : ({i} : Multiset I) + β₀ = γ₁) (hm₁ : γ₁.card = m₁)
    (p₂ : m₁ + 1 = m₂) (hγ₂ : ({i} : Multiset I) + γ₁ = γ₂) (hc : ({i} : Multiset I) + (({i} : Multiset I) + β₀) = γ₂)
    (pX : β₀.card + 1 + 1 = m₂)
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₁ γ₁))
    (O O' : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₁ γ₁)) :
    ∀ (a₁ : O = _) (a₂ : _ = _) (a₃ : _ = _) (a₄ : _ = O') (e₁ : O = _) (e₂ : _ = O'),
    eqToHom a₁ ≫
      ((heightContentAdjunction D Sc i a ha m₁ γ₁ hm₁).comp
          (heightContentCastAdjunction D Sc a ha p₂ hγ₂)).unit.app
        (((heightContentInduction D Sc i a ha β₀.card β₀).comp
            (heightContentCast D Sc a ha p₁ hγ₁)).obj
          (((heightContentCast D Sc a ha p₁.symm hγ₁.symm).comp
            (heightContentRestriction D Sc i a ha β₀.card β₀ rfl)).obj N)) ≫ eqToHom a₂ ≫
      ((heightContentCast D Sc a ha p₂.symm hγ₂.symm).comp
          (heightContentRestriction D Sc i a ha m₁ γ₁ hm₁)).toFunctor.map
        ((heightContentCast D Sc a ha pX rfl).map
          ((heightBlockCross D Sc a ha i i β₀.card β₀ γ₂ hc).app (D.parity i)
            (((heightContentCast D Sc a ha p₁.symm hγ₁.symm).comp
              (heightContentRestriction D Sc i a ha β₀.card β₀ rfl)).obj N))) ≫ eqToHom a₃ ≫
      ((heightContentCast D Sc a ha p₂.symm hγ₂.symm).comp
          (heightContentRestriction D Sc i a ha m₁ γ₁ hm₁)).toFunctor.map
        (((heightContentInduction D Sc i a ha m₁ γ₁).comp
            (heightContentCast D Sc a ha p₂ hγ₂)).toFunctor.map
          (((heightContentAdjunction D Sc i a ha β₀.card β₀ rfl).comp
            (heightContentCastAdjunction D Sc a ha p₁ hγ₁)).counit.app N)) ≫ eqToHom a₄ =
      -(eqToHom e₁ ≫ (heightContentCast D Sc a ha p₁ hγ₁).map
          (contentMateKernel D Sc a ha i β₀
            ((heightContentCast D Sc a ha p₁.symm hγ₁.symm).obj N)) ≫ eqToHom e₂) := by
  intro a₁ a₂ a₃ a₄ e₁ e₂
  subst p₁ hγ₁ p₂ hγ₂ a₁ a₄
  simp only [heightContentCast_rfl, Superfunctor.id_comp, Superfunctor.comp_id,
    Adjunction.comp_unit_app, Adjunction.comp_counit_app, heightContentCastUnit_app_self,
    heightContentCastCounit_app_self, superfunctor_id_map,
    Category.comp_id, CategoryTheory.Functor.map_id, superfunctor_id_toFunctor_obj]
  exact heightContentMate_self D Sc a ha i β₀ _ _ N _ _ _ _ _ _ _ _

omit [DecidableEq I] in
/-- The target of the transported mate kernel is the composite of the transported restriction
and induction. -/
theorem heightContentCast_restriction_induction_obj (β₀ : Multiset I) {m₁ m₂ : ℕ}
    {γ₁ γ₂ : Multiset I} (p₁ : β₀.card + 1 = m₁) (hγ₁ : ({i} : Multiset I) + β₀ = γ₁)
    (hm₁ : γ₁.card = m₁) (p₂ : m₁ + 1 = m₂) (hγ₂ : ({i} : Multiset I) + γ₁ = γ₂)
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₁ γ₁)) :
    (heightContentCast D Sc a ha p₁ hγ₁).obj
        ((heightContentRestriction D Sc i a ha (β₀.card + 1) (({i} : Multiset I) + β₀)
            (card_of_add (β := β₀) (δ := ({i} : Multiset I) + β₀) i rfl).symm).obj
          ((heightContentInduction D Sc i a ha (β₀.card + 1) (({i} : Multiset I) + β₀)).obj
            ((heightContentCast D Sc a ha p₁.symm hγ₁.symm).obj N))) =
      ((heightContentCast D Sc a ha p₂.symm hγ₂.symm).comp
          (heightContentRestriction D Sc i a ha m₁ γ₁ hm₁)).obj
        (((heightContentInduction D Sc i a ha m₁ γ₁).comp
          (heightContentCast D Sc a ha p₂ hγ₂)).obj N) := by
  subst p₁ hγ₁ p₂ hγ₂
  simp only [heightContentCast_rfl, Superfunctor.id_comp, Superfunctor.comp_id]
  rfl

/-! ### Dotted units and counits on content blocks -/

/-- The `m`-th dot power on content induction, `x^m ⊗ Y` on `P ⊗ Y`. -/
def contentDotPow (β₀ : Multiset I) (m : ℕ)
    (Y : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha β₀.card β₀)) :
    (heightContentInduction D Sc i a ha β₀.card β₀).obj Y ⟶
      (heightContentInduction D Sc i a ha β₀.card β₀).obj Y :=
  ⟨SuperBimodule.whiskerRight (heightInductionDotPow D Sc i a ha β₀.card m) Y.obj⟩

/-- The dotted cup kernel `j_m ⊗ Y` on a content block. -/
def contentCupKernel (β₀ : Multiset I) (m : ℕ)
    (Y : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha β₀.card β₀)) :
    Y ⟶ (heightContentRestriction D Sc i a ha β₀.card β₀ rfl).obj
      ((heightContentInduction D Sc i a ha β₀.card β₀).obj Y) :=
  ⟨(SuperBimodule.leftUnitor Y.obj).inv ≫
    SuperBimodule.whiskerRight (rouquierCupKernel D Sc i a ha β₀.card m) Y.obj ≫
    (SuperBimodule.assoc (heightRestrictionCorner D Sc i a ha β₀.card)
      (heightInductionCorner D Sc i a ha β₀.card) Y.obj).hom⟩

/-- The dotted cap kernel `κ_m ⊗ N` on a content block. -/
def contentCapKernel (β₀ : Multiset I) (m : ℕ)
    (N : ObjectProperty.FullSubcategory
      (heightContentSupported D Sc a ha (β₀.card + 1) (({i} : Multiset I) + β₀))) :
    (heightContentInduction D Sc i a ha β₀.card β₀).obj
        ((heightContentRestriction D Sc i a ha β₀.card β₀ rfl).obj N) ⟶ N :=
  ⟨(SuperBimodule.assoc (heightInductionCorner D Sc i a ha β₀.card)
      (heightRestrictionCorner D Sc i a ha β₀.card) N.obj).inv ≫
    SuperBimodule.whiskerRight (rouquierCapKernel D Sc i a ha β₀.card m) N.obj ≫
    (SuperBimodule.leftUnitor N.obj).hom⟩

omit [DecidableEq I] in
/-- The unit followed by the dot power is `d_m` times the dotted cup. -/
theorem contentUnit_dotPow (β₀ : Multiset I) (m : ℕ)
    (Y : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha β₀.card β₀)) :
    (heightContentAdjunction D Sc i a ha β₀.card β₀ rfl).unit.app Y ≫
        (heightContentRestriction D Sc i a ha β₀.card β₀ rfl).toFunctor.map
          (contentDotPow D Sc a ha i β₀ m Y) =
      ((rouquierDotSign (D.parity i) m : ℤ) : k) • contentCupKernel D Sc a ha i β₀ m Y := by
  apply (fullHomEquiv (k := k) _ _ _).injective
  rw [map_smul]
  exact heightSuperUnit_dotPow D Sc i a ha β₀.card m Y.obj

omit [DecidableEq I] in
/-- The dot power followed by the counit is `d_m` times the dotted cap. -/
theorem contentDotPow_counit (β₀ : Multiset I) (m : ℕ)
    (N : ObjectProperty.FullSubcategory
      (heightContentSupported D Sc a ha (β₀.card + 1) (({i} : Multiset I) + β₀))) :
    contentDotPow D Sc a ha i β₀ m ((heightContentRestriction D Sc i a ha β₀.card β₀ rfl).obj N) ≫
        (heightContentAdjunction D Sc i a ha β₀.card β₀ rfl).counit.app N =
      ((rouquierDotSign (D.parity i) m : ℤ) : k) • contentCapKernel D Sc a ha i β₀ m N := by
  apply (fullHomEquiv (k := k) _ _ _).injective
  rw [map_smul]
  exact heightDotPow_superCounit D Sc i a ha β₀.card m N.obj

omit [DecidableEq I] in
theorem contentDotPow_zero (β₀ : Multiset I)
    (Y : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha β₀.card β₀)) :
    contentDotPow D Sc a ha i β₀ 0 Y = 𝟙 _ := by
  apply (fullHomEquiv (k := k) _ _ _).injective
  exact SuperBimodule.id_whiskerRight _ _

omit [DecidableEq I] in
theorem contentDotPow_succ (β₀ : Multiset I) (m : ℕ)
    (Y : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha β₀.card β₀)) :
    contentDotPow D Sc a ha i β₀ (m + 1) Y =
      contentDotPow D Sc a ha i β₀ m Y ≫
        (heightContentDot D Sc i a ha β₀.card β₀).app (D.parity i) Y := by
  apply (fullHomEquiv (k := k) _ _ _).injective
  change SuperBimodule.whiskerRight (heightInductionDotPow D Sc i a ha β₀.card m ≫
      heightInductionSuperDot D Sc i a ha β₀.card) Y.obj =
    SuperBimodule.whiskerRight (heightInductionDotPow D Sc i a ha β₀.card m) Y.obj ≫
      (if D.parity i = D.parity i then
        SuperBimodule.whiskerRight (heightInductionSuperDot D Sc i a ha β₀.card) Y.obj else 0)
  split_ifs with hp
  · rw [SuperBimodule.comp_whiskerRight]
  · exact absurd rfl hp

omit [DecidableEq I] in
theorem heightContentCastTrans_app {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m') (hγ : γ = γ')
    {F : C ⥤ ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)}
    [F.Additive] [F.Linear k] [IsSuperfunctor k F] (η : SuperNatTrans k F F) (q : ZMod 2)
    (Y : C) :
    (heightContentCastTrans D Sc a ha hm hγ η).app q Y =
      (heightContentCast D Sc a ha hm hγ).map (η.app q Y) := by
  subst hm
  subst hγ
  rfl

omit [DecidableEq I] in
theorem heightContentCast_cast_obj {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m')
    (hγ : γ = γ') (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m' γ')) :
    (heightContentCast D Sc a ha hm hγ).obj ((heightContentCast D Sc a ha hm.symm hγ.symm).obj N) =
      N := by
  subst hm
  subst hγ
  rfl

omit [DecidableEq I] in
theorem heightContentCastCounit_app {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m')
    (hγ : γ = γ') (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m' γ')) :
    (heightContentCastAdjunction D Sc a ha hm hγ).counit.app N =
      eqToHom (heightContentCast_cast_obj D Sc a ha hm hγ N) := by
  subst hm
  subst hγ
  rfl

omit [DecidableEq I] in
theorem heightContentCastUnit_app {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m')
    (hγ : γ = γ') (Y : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)) :
    (heightContentCastAdjunction D Sc a ha hm hγ).unit.app Y =
      eqToHom (heightContentCast_cast_obj D Sc a ha hm.symm hγ.symm Y).symm := by
  subst hm
  subst hγ
  rfl

omit [DecidableEq I] in
theorem heightContentCast_symm_map_map {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m')
    (hγ : γ = γ') {Y Y' : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)}
    (f : Y ⟶ Y') :
    (heightContentCast D Sc a ha hm.symm hγ.symm).map ((heightContentCast D Sc a ha hm hγ).map f) =
      eqToHom (heightContentCast_cast_obj D Sc a ha hm.symm hγ.symm Y) ≫ f ≫
        eqToHom (heightContentCast_cast_obj D Sc a ha hm.symm hγ.symm Y').symm := by
  subst hm
  subst hγ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end Content

section Weight
variable (i : I) (Λ : X) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

theorem globalRouquierMate_app_blockSucc (M : WeightProduct D Sc a ha Λ x₁)
    (β : WeightBlocks D Λ x₀) :
    (SKM.rouquierMate (globalActionAdjunction D Sc a ha i Λ h₁)
      (globalActionAdjunction D Sc a ha i Λ h₂)
      (globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂)).app (D.parity i) M
        (blockSucc D Λ i h₁ β) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₁ β
          (Superfunctor.obj (globalActionF D Sc a ha i Λ h₁) M)) ≫
        (heightContentCast D Sc a ha (card_of_add i (blockSucc_val D Λ i h₁ β).symm)
          (blockSucc_val D Λ i h₁ β).symm).map
          (contentMateKernel D Sc a ha i β.1
            ((heightContentCast D Sc a ha (card_of_add i (blockSucc_val D Λ i h₁ β).symm).symm
              (blockSucc_val D Λ i h₁ β)).obj (M (blockSucc D Λ i h₁ β)))) ≫
        eqToHom ((heightContentCast_restriction_induction_obj D Sc a ha i β.1
            (card_of_add i (blockSucc_val D Λ i h₁ β).symm) (blockSucc_val D Λ i h₁ β).symm rfl
            (card_of_add i (blockSucc_val D Λ i h₂ (blockSucc D Λ i h₁ β)).symm)
            (blockSucc_val D Λ i h₂ (blockSucc D Λ i h₁ β)).symm
            (M (blockSucc D Λ i h₁ β))).trans
          (congrArg (blockRes D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)).obj
            (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β) M).symm)) := by
  rw [scat_rouquierMate_app _ _ _
    (fun Z => by simp [globalActionAdjunction, globalActionUnit, SuperNatTrans.ofNatTrans])
    (fun Z => by simp [globalActionAdjunction, globalActionCounit, SuperNatTrans.ofNatTrans])]
  change globalWeightUnitApp D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β) _ ≫
      (blockRes D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)).map
        ((globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂).app (D.parity i)
          (Superfunctor.obj (globalActionF D Sc a ha i Λ h₁) M)
          (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β))) ≫
      (blockRes D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)).map
        (Superfunctor.map (globalActionE D Sc a ha i Λ h₂)
          ((globalActionAdjunction D Sc a ha i Λ h₁).counit.app 0 M)
          (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β))) = _
  have hs : globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂ =
      -globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂ := by
    simp [globalActionSignedCross]
  have hX : (globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂).app (D.parity i)
      (Superfunctor.obj (globalActionF D Sc a ha i Λ h₁) M)
      (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) =
      globalWeightCrossVia D Sc a ha i i Λ h₁ h₂ h₁ h₂ (D.parity i)
        (Superfunctor.obj (globalActionF D Sc a ha i Λ h₁) M) β
        (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) rfl :=
    globalWeightCrossComponent_of D Sc a ha i i Λ h₁ h₂ h₁ h₂ _ _ β
      (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) rfl
  have hE : Superfunctor.map (globalActionE D Sc a ha i Λ h₂)
      ((globalActionAdjunction D Sc a ha i Λ h₁).counit.app 0 M)
      (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β) _) ≫
        (blockInd D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)).map
          ((globalActionAdjunction D Sc a ha i Λ h₁).counit.app 0 M (blockSucc D Λ i h₁ β)) ≫
          eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)
            M).symm :=
    inductionComponent_map_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β) _
  have hC : (globalActionAdjunction D Sc a ha i Λ h₁).counit.app 0 M (blockSucc D Λ i h₁ β) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₁ β
        ((globalF D Sc i a ha Λ h₁).obj M)) ≫
        (blockAdj D Sc a ha i Λ h₁ β).counit.app (M (blockSucc D Λ i h₁ β)) :=
    globalWeightCounitComponent_blockSucc D Sc a ha i Λ h₁ M β
  rw [hs, SCat.neg_app]
  erw [Pi.neg_apply]
  rw [hX, hE, hC]
  unfold globalWeightUnitApp globalWeightCrossVia
  erw [natTrans_app_of_eq (blockAdj D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)).unit
    (inductionComponent_obj_blockSucc D Sc a ha i Λ h₁ β
      (Superfunctor.obj (globalActionF D Sc a ha i Λ h₁) M))]
  simp only [Functor.map_comp, Functor.map_neg, eqToHom_map, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc, Preadditive.neg_comp, Preadditive.comp_neg]
  rw [neg_eq_iff_eq_neg]
  exact heightContentMate D Sc a ha i β.1 (card_of_add i (blockSucc_val D Λ i h₁ β).symm)
    (blockSucc_val D Λ i h₁ β).symm rfl
    (card_of_add i (blockSucc_val D Λ i h₂ (blockSucc D Λ i h₁ β)).symm)
    (blockSucc_val D Λ i h₂ (blockSucc D Λ i h₁ β)).symm _ _
    (M (blockSucc D Λ i h₁ β)) _ _ _ _ _ _ _ _

omit [DecidableEq I] in
/-- The dot at a successor block is the transported content dot. -/
theorem globalActionDot_app_blockSucc {x y : X} (h : x + D.α i = y) (q : ZMod 2)
    (Z : WeightProduct D Sc a ha Λ x) (β : WeightBlocks D Λ x) :
    (globalActionDot D Sc a ha i Λ h).app q Z (blockSucc D Λ i h β) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β Z) ≫
        (heightContentCast D Sc a ha (card_of_add i (blockSucc_val D Λ i h β).symm)
          (blockSucc_val D Λ i h β).symm).map
          ((heightContentDot D Sc i a ha β.1.card β.1).app q (Z β)) ≫
        eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β Z).symm := by
  change globalWeightDotComponent D Sc a ha i Λ h q Z (blockSucc D Λ i h β) = _
  rw [globalWeightDotComponent_blockSucc]
  congr 2
  exact heightContentCastTrans_app D Sc a ha _ _ _ q (Z β)

omit [DecidableEq I] in
/-- Parity of the vertical powers of the weight-level dot. -/
theorem globalActionDotPow_mem {x y : X} (h : x + D.α i = y) (m : ℕ) :
    SKM.rouquierPower (globalActionDot D Sc a ha i Λ h) m ∈
      parity (R := k) _ _ ((m : ZMod 2) * D.parity i) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, zero_mul]
    exact id_mem (R := k) _
  | succ m ih =>
    have hc := comp_mem ih (globalActionDot_mem D Sc a ha i Λ h)
    rwa [show (m : ZMod 2) * D.parity i + D.parity i = ((m + 1 : ℕ) : ZMod 2) * D.parity i by
      push_cast; ring] at hc

omit [DecidableEq I] in
/-- The dot power at a successor block is the transported content dot power. -/
theorem globalActionDotPow_app_blockSucc {x y : X} (h : x + D.α i = y) (m : ℕ)
    (Z : WeightProduct D Sc a ha Λ x) (β : WeightBlocks D Λ x) :
    (SKM.rouquierPower (globalActionDot D Sc a ha i Λ h) m).app ((m : ZMod 2) * D.parity i) Z
        (blockSucc D Λ i h β) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β Z) ≫
        (heightContentCast D Sc a ha (card_of_add i (blockSucc_val D Λ i h β).symm)
          (blockSucc_val D Λ i h β).symm).map (contentDotPow D Sc a ha i β.1 m (Z β)) ≫
        eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β Z).symm := by
  induction m with
  | zero =>
    rw [contentDotPow_zero, Nat.cast_zero, zero_mul]
    refine Eq.trans ?_ (eqToHom_map_id_eqToHom (heightContentCast D Sc a ha
      (card_of_add i (blockSucc_val D Λ i h β).symm) (blockSucc_val D Λ i h β).symm).toFunctor
      _).symm
    rfl
  | succ m ih =>
    have hP := globalActionDotPow_mem D Sc a ha i Λ h m
    rw [show SKM.rouquierPower (globalActionDot D Sc a ha i Λ h) (m + 1) =
        SKM.rouquierPower (globalActionDot D Sc a ha i Λ h) m ≫ globalActionDot D Sc a ha i Λ h
      from rfl, Nat.cast_succ, add_mul, one_mul,
      scat_comp_app_of_mem hP (globalActionDot_mem D Sc a ha i Λ h)]
    erw [CategoryTheory.Pi.comp_apply]
    rw [ih, globalActionDot_app_blockSucc, contentDotPow_succ]
    simp

omit [DecidableEq I] in
/-- **The dotted counit at a successor block** is `d_m` times the transported dotted cap
kernel `κ_m ⊗ N`. -/
theorem globalDottedCounit_app_blockSucc (m : ℕ) (M : WeightProduct D Sc a ha Λ x₁)
    (β : WeightBlocks D Λ x₀) :
    (globalActionF D Sc a ha i Λ h₁ ◁ SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₁) m ≫
        (globalActionAdjunction D Sc a ha i Λ h₁).counit).app ((m : ZMod 2) * D.parity i) M
        (blockSucc D Λ i h₁ β) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₁ β
          (Superfunctor.obj (globalActionF D Sc a ha i Λ h₁) M)) ≫
        (heightContentCast D Sc a ha (card_of_add i (blockSucc_val D Λ i h₁ β).symm)
          (blockSucc_val D Λ i h₁ β).symm).map
          (((rouquierDotSign (D.parity i) m : ℤ) : k) • contentCapKernel D Sc a ha i β.1 m
            ((heightContentCast D Sc a ha (card_of_add i (blockSucc_val D Λ i h₁ β).symm).symm
              (blockSucc_val D Λ i h₁ β)).obj (M (blockSucc D Λ i h₁ β)))) ≫
        eqToHom (heightContentCast_cast_obj D Sc a ha
          (card_of_add i (blockSucc_val D Λ i h₁ β).symm) (blockSucc_val D Λ i h₁ β).symm
          (M (blockSucc D Λ i h₁ β))) := by
  rw [scat_comp_app_of_even_right _ _
    (fun Z => by simp [globalActionAdjunction, globalActionCounit, SuperNatTrans.ofNatTrans]),
    SCat.whiskerLeft_app]
  have hC : (globalActionAdjunction D Sc a ha i Λ h₁).counit.app 0 M (blockSucc D Λ i h₁ β) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₁ β
        ((globalF D Sc i a ha Λ h₁).obj M)) ≫
        (blockAdj D Sc a ha i Λ h₁ β).counit.app (M (blockSucc D Λ i h₁ β)) :=
    globalWeightCounitComponent_blockSucc D Sc a ha i Λ h₁ M β
  erw [CategoryTheory.Pi.comp_apply]
  rw [globalActionDotPow_app_blockSucc, hC, blockAdj, globalContentAdjunction,
    Adjunction.comp_counit_app, heightContentCastCounit_app]
  simp only [Superfunctor.map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Functor.map_comp_assoc]
  erw [contentDotPow_counit]

omit [DecidableEq I] in
/-- **The dotted unit at a block** is `d_m` times the dotted cup kernel `j_m ⊗ Z_δ`. -/
theorem globalDottedUnit_app (m : ℕ) (Z : WeightProduct D Sc a ha Λ x₁)
    (δ : WeightBlocks D Λ x₁) :
    ((globalActionAdjunction D Sc a ha i Λ h₂).unit ≫
        SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) m ▷ globalActionF D Sc a ha i Λ h₂).app
        ((m : ZMod 2) * D.parity i) Z δ =
      ((rouquierDotSign (D.parity i) m : ℤ) : k) • contentCupKernel D Sc a ha i δ.1 m (Z δ) ≫
        eqToHom ((congrArg (heightContentRestriction D Sc i a ha δ.1.card δ.1 rfl).obj
            (heightContentCast_cast_obj D Sc a ha
              (card_of_add i (blockSucc_val D Λ i h₂ δ).symm).symm
              (blockSucc_val D Λ i h₂ δ)
              ((heightContentInduction D Sc i a ha δ.1.card δ.1).obj (Z δ)))).symm.trans
          (congrArg (blockRes D Sc a ha i Λ h₂ δ).obj
            (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ δ Z).symm)) := by
  rw [scat_comp_app_of_even_left _ _
    (fun Z => by simp [globalActionAdjunction, globalActionUnit, SuperNatTrans.ofNatTrans]),
    SCat.whiskerRight_app]
  erw [CategoryTheory.Pi.comp_apply]
  change globalWeightUnitApp D Sc a ha i Λ h₂ δ Z ≫ (blockRes D Sc a ha i Λ h₂ δ).map
      ((SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) m).app ((m : ZMod 2) * D.parity i) Z
        (blockSucc D Λ i h₂ δ)) = _
  rw [globalActionDotPow_app_blockSucc]
  simp only [globalWeightUnitApp, blockAdj, globalContentAdjunction, Adjunction.comp_unit_app,
    heightContentCastUnit_app]
  have hc := heightContentCast_symm_map_map D Sc a ha (card_of_add i (blockSucc_val D Λ i h₂ δ).symm)
    (blockSucc_val D Λ i h₂ δ).symm (contentDotPow D Sc a ha i δ.1 m (Z δ))
  simp only [Superfunctor.map] at hc
  simp only [blockRes, globalContentRestriction, Superfunctor.comp, Superfunctor.map,
    Functor.comp_map, Functor.map_comp, eqToHom_map, Category.assoc, hc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [eqToHom_trans, ← Category.assoc, contentUnit_dotPow, Linear.smul_comp]

end Weight
end OddMath.QuiverHecke.CyclotomicAction
