/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightSlides
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightMixedSlides

/-!
# Distinct-colour dot slides on the global weight factors

Brundan–Ellis, *Super Kac–Moody 2-categories* (arXiv:1701.04133v2), relation (1.8) for
`i ≠ j`: a dot slides through the crossing of two distinct colours, with the sign
`(-1)^{|i||j|}`. Here it is proved for the cyclotomic global action on weight factors.

* `heightContentMixedSlideLeft`, `heightContentMixedSlideRight`: the slides on content blocks,
  with arbitrary height and content transports, from the height-level slides
  `heightInduction_slide_left_ne`, `heightInduction_slide_right_ne`.
* `globalActionCross_slide_left_ne`, `globalActionCross_slide_right_ne`: the slides for the
  weight-level crossing, with the Koszul sign.
* `globalActionSignedCross_slide_left_ne`, `globalActionSignedCross_slide_right_ne`: the
  `slideLeft` and `slideRight` fields of `RouquierMulticolour` for the crossing of
  `globalRouquierData`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

omit [Fintype I] in
/-- An identity `a₁ ≫ b₁ = c • (a₂ ≫ b₂)` between homogeneous 2-morphisms in `𝔖ℭ𝔞𝔱`, with
`|a₁| + |b₁| = |a₂| + |b₂|`, holds once it holds for the components of those parities. -/
theorem scat_comp_eq_smul_comp_of_app {A B : SCat k} {F H H' G : A ⟶ B} {a₁ : F ⟶ H}
    {b₁ : H ⟶ G} {a₂ : F ⟶ H'} {b₂ : H' ⟶ G} {p₁ q₁ p₂ q₂ : ZMod 2} (c : ℤ)
    (ha₁ : a₁ ∈ parity (R := k) F H p₁) (hb₁ : b₁ ∈ parity (R := k) H G q₁)
    (ha₂ : a₂ ∈ parity (R := k) F H' p₂) (hb₂ : b₂ ∈ parity (R := k) H' G q₂)
    (hpq : p₁ + q₁ = p₂ + q₂)
    (h : ∀ M, a₁.app p₁ M ≫ b₁.app q₁ M = c • (a₂.app p₂ M ≫ b₂.app q₂ M)) :
    a₁ ≫ b₁ = c • (a₂ ≫ b₂) := by
  have hne : ∀ p : ZMod 2, p + 1 ≠ p := by decide
  have z : ∀ {F' G' : A ⟶ B} {x : F' ⟶ G'} {p : ZMod 2}, x ∈ parity (R := k) F' G' p →
      ∀ M, x.app (p + 1) M = 0 := fun hx M =>
    Superfunctor.app_eq_zero_of_mem hx (hne _) M
  have e₁ := z ha₁; have e₂ := z hb₁; have e₃ := z ha₂; have e₄ := z hb₂
  have t : (1 : ZMod 2) + 1 = 0 := by decide
  apply SCat.hom_ext <;> intro M <;> rw [scat_zsmul_app] <;>
    rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) p₁ with rfl | rfl <;>
    rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) q₁ with rfl | rfl <;>
    rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) p₂ with rfl | rfl <;>
    rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) q₂ with rfl | rfl <;>
    first
    | exact absurd hpq (by decide)
    | (simp only [zero_add, t] at e₁ e₂ e₃ e₄
       simp [e₁ M, e₂ M, e₃ M, e₄ M, h M])

theorem heightContentCast_obj_obj {m : ℕ} {γ γ' : Multiset I} (hγ : γ = γ')
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)) :
    ((heightContentCast D Sc a ha (rfl : m = m) hγ).obj N).obj = N.obj := by
  subst hγ
  rfl

theorem heightContentCast_map_hom {m : ℕ} {γ γ' : Multiset I} (hγ : γ = γ')
    {N N' : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)} (f : N ⟶ N') :
    ((heightContentCast D Sc a ha (rfl : m = m) hγ).map f).hom =
      eqToHom (heightContentCast_obj_obj D Sc a ha hγ N) ≫ f.hom ≫
        eqToHom (heightContentCast_obj_obj D Sc a ha hγ N').symm := by
  subst hγ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

theorem heightContentCastTrans_app_eq_map {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m') (hγ : γ = γ')
    {F : C ⥤ ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)}
    [F.Additive] [F.Linear k] [IsSuperfunctor k F] (η : SuperNatTrans k F F) (q : ZMod 2)
    (Y : C) :
    (heightContentCastTrans D Sc a ha hm hγ η).app q Y =
      (heightContentCast D Sc a ha hm hγ).map (η.app q Y) := by
  subst hm
  subst hγ
  rfl

section Content
variable {i j : I} (hij : i ≠ j)
include hij

attribute [local irreducible] ContentSupported

/-- **The distinct-colour left dot slide on content blocks**, with arbitrary height and
content transports. -/
theorem heightContentMixedSlideLeft (m₀ : ℕ) (γ₀ : Multiset I)
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₀ γ₀))
    {m₁ m₂ m₃ : ℕ} {γ₁ γ₂ γ₃ : Multiset I}
    (p₁ : m₀ + 1 = m₁) (q₁ : {j} + γ₀ = γ₁) (p₂ : m₁ + 1 = m₂) (q₂ : {i} + γ₁ = γ₂)
    (hc : {i} + ({j} + γ₀) = γ₂) (pX : m₀ + 1 + 1 = m₂)
    (p₃ : m₀ + 1 = m₃) (q₃ : {i} + γ₀ = γ₃) (p₄ : m₃ + 1 = m₂) (q₄ : {j} + γ₃ = γ₂)
    (O O' : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₂ γ₂)) :
    ∀ (a₁ : O = _) (a₂ : _ = _) (a₃ : _ = O') (b₁ : O = _) (b₂ : _ = _) (b₃ : _ = O'),
    eqToHom a₁ ≫ (heightContentCastTrans D Sc a ha p₂ q₂
          (heightContentDot D Sc i a ha m₁ γ₁)).app (D.parity i)
          ((heightContentCast D Sc a ha p₁ q₁).obj
            ((heightContentInduction D Sc j a ha m₀ γ₀).obj N)) ≫ eqToHom a₂ ≫
        (heightContentCast D Sc a ha pX rfl).map
          ((heightBlockCross D Sc a ha i j m₀ γ₀ γ₂ hc).app (D.parity i * D.parity j) N) ≫
          eqToHom a₃ =
      koszulSign (D.parity i) (D.parity j) •
        (eqToHom b₁ ≫ (heightContentCast D Sc a ha pX rfl).map
            ((heightBlockCross D Sc a ha i j m₀ γ₀ γ₂ hc).app (D.parity i * D.parity j) N) ≫
          eqToHom b₂ ≫ (heightContentCast D Sc a ha p₄ q₄).map
            ((heightContentInduction D Sc j a ha m₃ γ₃).map
              ((heightContentCastTrans D Sc a ha p₃ q₃
                (heightContentDot D Sc i a ha m₀ γ₀)).app (D.parity i) N)) ≫ eqToHom b₃) := by
  intro a₁ a₂ a₃ b₁ b₂ b₃
  subst p₁ q₁ p₂ q₂ p₃ q₃
  obtain rfl : hc = rfl := rfl
  obtain rfl : pX = rfl := rfl
  obtain rfl : p₄ = rfl := rfl
  subst a₁ a₃
  apply (fullHomEquiv (k := k) _ _ _).injective
  simp only [map_zsmul, fullHomEquiv_apply, ObjectProperty.FullSubcategory.comp_hom,
    fullSubcategory_eqToHom_hom, heightContentCast_map_hom]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, heightBlockCross_app,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  exact heightInduction_slide_left_ne D Sc a ha m₀ hij N.obj

/-- **The distinct-colour right dot slide on content blocks**, with arbitrary height and
content transports. -/
theorem heightContentMixedSlideRight (m₀ : ℕ) (γ₀ : Multiset I)
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₀ γ₀))
    {m₁ m₂ m₃ : ℕ} {γ₁ γ₂ γ₃ : Multiset I}
    (p₁ : m₀ + 1 = m₁) (q₁ : {j} + γ₀ = γ₁) (p₂ : m₁ + 1 = m₂) (q₂ : {i} + γ₁ = γ₂)
    (hc : {i} + ({j} + γ₀) = γ₂) (pX : m₀ + 1 + 1 = m₂)
    (p₃ : m₀ + 1 = m₃) (q₃ : {i} + γ₀ = γ₃) (p₄ : m₃ + 1 = m₂) (q₄ : {j} + γ₃ = γ₂)
    (O O' : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₂ γ₂)) :
    ∀ (a₁ : O = _) (a₂ : _ = _) (a₃ : _ = O') (b₁ : O = _) (b₂ : _ = _) (b₃ : _ = O'),
    eqToHom a₁ ≫ (heightContentCast D Sc a ha pX rfl).map
          ((heightBlockCross D Sc a ha i j m₀ γ₀ γ₂ hc).app (D.parity i * D.parity j) N) ≫
          eqToHom a₂ ≫
        (heightContentCastTrans D Sc a ha p₄ q₄
            (heightContentDot D Sc j a ha m₃ γ₃)).app (D.parity j)
            ((heightContentCast D Sc a ha p₃ q₃).obj
              ((heightContentInduction D Sc i a ha m₀ γ₀).obj N)) ≫ eqToHom a₃ =
      koszulSign (D.parity i) (D.parity j) •
        (eqToHom b₁ ≫ (heightContentCast D Sc a ha p₂ q₂).map
            ((heightContentInduction D Sc i a ha m₁ γ₁).map
              ((heightContentCastTrans D Sc a ha p₁ q₁
                (heightContentDot D Sc j a ha m₀ γ₀)).app (D.parity j) N)) ≫ eqToHom b₂ ≫
          (heightContentCast D Sc a ha pX rfl).map
            ((heightBlockCross D Sc a ha i j m₀ γ₀ γ₂ hc).app (D.parity i * D.parity j) N) ≫
            eqToHom b₃) := by
  intro a₁ a₂ a₃ b₁ b₂ b₃
  subst p₁ q₁ p₂ q₂ p₃ q₃
  obtain rfl : hc = rfl := rfl
  obtain rfl : pX = rfl := rfl
  obtain rfl : p₄ = rfl := rfl
  subst a₁ a₃
  rw [heightContentCastTrans_app_eq_map]
  apply (fullHomEquiv (k := k) _ _ _).injective
  simp only [map_zsmul, fullHomEquiv_apply, ObjectProperty.FullSubcategory.comp_hom,
    fullSubcategory_eqToHom_hom, heightContentCast_map_hom]
  simp only [eqToHom_trans_assoc, heightBlockCross_app, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  rw [← Category.assoc, ← Category.assoc, ← Preadditive.zsmul_comp]
  exact congrArg (· ≫ _) (heightInduction_slide_right_ne D Sc a ha m₀ hij N.obj)

end Content

section WeightTransport
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

theorem inductionComponent_obj_of_eq (γ : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y)
    (e : blockSucc D Λ i h γ = δ) (M : WeightProduct D Sc a ha Λ x) :
    (inductionComponent D Sc a ha i Λ h δ).obj M =
      (globalContentInduction D Sc i a ha (blockSucc_eq D Λ i e)).obj (M γ) := by
  subst e
  exact inductionComponent_obj_blockSucc D Sc a ha i Λ h γ M

theorem inductionComponent_map_of_eq (γ : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y)
    (e : blockSucc D Λ i h γ = δ) {M M' : WeightProduct D Sc a ha Λ x} (f : M ⟶ M') :
    (inductionComponent D Sc a ha i Λ h δ).map f =
      eqToHom (inductionComponent_obj_of_eq D Sc a ha i Λ h γ δ e M) ≫
        (globalContentInduction D Sc i a ha (blockSucc_eq D Λ i e)).map (f γ) ≫
          eqToHom (inductionComponent_obj_of_eq D Sc a ha i Λ h γ δ e M').symm := by
  subst e
  exact inductionComponent_map_blockSucc D Sc a ha i Λ h γ f

theorem globalWeightDotComponent_of_eq (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (γ : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (e : blockSucc D Λ i h γ = δ) :
    globalWeightDotComponent D Sc a ha i Λ h p M δ =
      eqToHom (inductionComponent_obj_of_eq D Sc a ha i Λ h γ δ e M) ≫
        (globalContentDot D Sc i a ha (blockSucc_eq D Λ i e)).app p (M γ) ≫
          eqToHom (inductionComponent_obj_of_eq D Sc a ha i Λ h γ δ e M).symm := by
  subst e
  exact globalWeightDotComponent_blockSucc D Sc a ha i Λ h p M γ

end WeightTransport

omit [Fintype I] in
theorem pi_comp_apply' {J : Type*} {C : J → Type*} [∀ j, Category (C j)]
    {P Q R : ∀ j, C j} (A : P ⟶ Q) (B : Q ⟶ R) (j : J) : (A ≫ B) j = A j ≫ B j := rfl

omit [Fintype I] in
theorem pi_zsmul_apply' {J : Type*} {C : J → Type*} [∀ j, Category (C j)]
    [∀ j, Preadditive (C j)] {P Q : ∀ j, C j} (A : P ⟶ Q) (c : ℤ) (j : J) :
    (c • A) j = c • A j := rfl

section Weight
variable {i j : I} (hij : i ≠ j) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃) (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)
include hij

/-- **The left dot slide (1.8) for distinct colours on the global factors**, with the Koszul
sign. -/
theorem globalActionCross_slide_left_ne :
    globalActionE D Sc a ha j Λ h₁ ◁ globalActionDot D Sc a ha i Λ h₂ ≫
        globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄ =
      koszulSign (D.parity i) (D.parity j) •
        (globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄ ≫
          globalActionDot D Sc a ha i Λ h₃ ▷ globalActionE D Sc a ha j Λ h₄) := by
  have m1 := TwoSupercategory.whiskerLeft_mem (R := k) (globalActionE D Sc a ha j Λ h₁)
    (globalActionDot_mem D Sc a ha i Λ h₂)
  have m2 := globalActionCross_mem D Sc a ha i j Λ h₁ h₂ h₃ h₄
  have m3 := TwoSupercategory.whiskerRight_mem (R := k) (globalActionE D Sc a ha j Λ h₄)
    (globalActionDot_mem D Sc a ha i Λ h₃)
  refine scat_comp_eq_smul_comp_of_app _ m1 m2 m2 m3 (add_comm _ _) fun M => ?_
  funext ζ
  rw [pi_comp_apply', pi_zsmul_apply', pi_comp_apply', SCat.whiskerLeft_app,
    SCat.whiskerRight_app]
  by_cases hζ : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ζ
  · obtain ⟨β, rfl⟩ := hζ
    have e₂ := blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ (rfl : blockSucc₂ D i j Λ h₁ h₂ β = _)
    have hX : (globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M (blockSucc₂ D i j Λ h₁ h₂ β) =
        globalWeightCrossVia D Sc a ha i j Λ h₁ h₂ h₃ h₄ (D.parity i * D.parity j) M β
          (blockSucc₂ D i j Λ h₁ h₂ β) rfl :=
      globalWeightCrossComponent_of D Sc a ha i j Λ h₁ h₂ h₃ h₄ _ M β _ rfl
    have hD₂ : (globalActionDot D Sc a ha i Λ h₂).app (D.parity i)
        (Superfunctor.obj (globalActionE D Sc a ha j Λ h₁) M)
        (blockSucc D Λ i h₂ (blockSucc D Λ j h₁ β)) =
        eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)
          ((globalEFunctor D Sc a ha j Λ h₁).obj M)) ≫
          (blockDot D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)).app (D.parity i)
            ((globalEFunctor D Sc a ha j Λ h₁).obj M (blockSucc D Λ j h₁ β)) ≫
            eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)
              ((globalEFunctor D Sc a ha j Λ h₁).obj M)).symm :=
      globalWeightDotComponent_blockSucc D Sc a ha i Λ h₂ _ _ (blockSucc D Λ j h₁ β)
    have hE : Superfunctor.map (globalActionE D Sc a ha j Λ h₄)
        ((globalActionDot D Sc a ha i Λ h₃).app (D.parity i) M)
        (blockSucc D Λ i h₂ (blockSucc D Λ j h₁ β)) =
        eqToHom (inductionComponent_obj_of_eq D Sc a ha j Λ h₄ (blockSucc D Λ i h₃ β) _ e₂
          ((globalEFunctor D Sc a ha i Λ h₃).obj M)) ≫
          (globalContentInduction D Sc j a ha (blockSucc_eq D Λ j e₂)).map
            ((globalActionDot D Sc a ha i Λ h₃).app (D.parity i) M (blockSucc D Λ i h₃ β)) ≫
            eqToHom (inductionComponent_obj_of_eq D Sc a ha j Λ h₄ (blockSucc D Λ i h₃ β) _ e₂
              ((globalEFunctor D Sc a ha i Λ h₃).obj M)).symm :=
      inductionComponent_map_of_eq D Sc a ha j Λ h₄ (blockSucc D Λ i h₃ β) _ e₂ _
    have hD₁ : (globalActionDot D Sc a ha i Λ h₃).app (D.parity i) M (blockSucc D Λ i h₃ β) =
        eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₃ β M) ≫
          (blockDot D Sc a ha i Λ h₃ β).app (D.parity i) (M β) ≫
            eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₃ β M).symm :=
      globalWeightDotComponent_blockSucc D Sc a ha i Λ h₃ _ M β
    rw [hX, hD₂, hE, hD₁]
    unfold globalWeightCrossVia
    rw [superNatTrans_app_of_eq (blockDot D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)) _
      (show (globalEFunctor D Sc a ha j Λ h₁).obj M (blockSucc D Λ j h₁ β) =
        (blockInd D Sc a ha j Λ h₁ β).obj (M β) from
        inductionComponent_obj_blockSucc D Sc a ha j Λ h₁ β M)]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    exact heightContentMixedSlideLeft D Sc a ha hij β.1.card β.1 (M β)
      (m₁ := (blockSucc D Λ j h₁ β).1.card) (γ₁ := (blockSucc D Λ j h₁ β).1)
      (m₂ := (blockSucc₂ D i j Λ h₁ h₂ β).1.card) (γ₂ := (blockSucc₂ D i j Λ h₁ h₂ β).1)
      (m₃ := (blockSucc D Λ i h₃ β).1.card) (γ₃ := (blockSucc D Λ i h₃ β).1)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact (globalEFunctor_comp_isZero D Sc a ha i j Λ h₁ h₂ ζ
      (fun ⟨β, hβ⟩ => hζ ⟨β, hβ⟩) M).eq_of_src _ _

/-- **The right dot slide (1.8) for distinct colours on the global factors**, with the Koszul
sign. -/
theorem globalActionCross_slide_right_ne :
    globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄ ≫
        globalActionE D Sc a ha i Λ h₃ ◁ globalActionDot D Sc a ha j Λ h₄ =
      koszulSign (D.parity i) (D.parity j) •
        (globalActionDot D Sc a ha j Λ h₁ ▷ globalActionE D Sc a ha i Λ h₂ ≫
          globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄) := by
  have m1 := TwoSupercategory.whiskerLeft_mem (R := k) (globalActionE D Sc a ha i Λ h₃)
    (globalActionDot_mem D Sc a ha j Λ h₄)
  have m2 := globalActionCross_mem D Sc a ha i j Λ h₁ h₂ h₃ h₄
  have m3 := TwoSupercategory.whiskerRight_mem (R := k) (globalActionE D Sc a ha i Λ h₂)
    (globalActionDot_mem D Sc a ha j Λ h₁)
  refine scat_comp_eq_smul_comp_of_app _ m2 m1 m3 m2 (add_comm _ _) fun M => ?_
  funext ζ
  rw [pi_comp_apply', pi_zsmul_apply', pi_comp_apply', SCat.whiskerLeft_app,
    SCat.whiskerRight_app]
  by_cases hζ : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ζ
  · obtain ⟨β, rfl⟩ := hζ
    have e₂ := blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ (rfl : blockSucc₂ D i j Λ h₁ h₂ β = _)
    have hX : (globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M (blockSucc₂ D i j Λ h₁ h₂ β) =
        globalWeightCrossVia D Sc a ha i j Λ h₁ h₂ h₃ h₄ (D.parity i * D.parity j) M β
          (blockSucc₂ D i j Λ h₁ h₂ β) rfl :=
      globalWeightCrossComponent_of D Sc a ha i j Λ h₁ h₂ h₃ h₄ _ M β _ rfl
    have hD₄ : (globalActionDot D Sc a ha j Λ h₄).app (D.parity j)
        (Superfunctor.obj (globalActionE D Sc a ha i Λ h₃) M)
        (blockSucc D Λ i h₂ (blockSucc D Λ j h₁ β)) =
        eqToHom (inductionComponent_obj_of_eq D Sc a ha j Λ h₄ (blockSucc D Λ i h₃ β) _ e₂
          ((globalEFunctor D Sc a ha i Λ h₃).obj M)) ≫
          (globalContentDot D Sc j a ha (blockSucc_eq D Λ j e₂)).app (D.parity j)
            ((globalEFunctor D Sc a ha i Λ h₃).obj M (blockSucc D Λ i h₃ β)) ≫
            eqToHom (inductionComponent_obj_of_eq D Sc a ha j Λ h₄ (blockSucc D Λ i h₃ β) _ e₂
              ((globalEFunctor D Sc a ha i Λ h₃).obj M)).symm :=
      globalWeightDotComponent_of_eq D Sc a ha j Λ h₄ _ _ (blockSucc D Λ i h₃ β) _ e₂
    have hE : Superfunctor.map (globalActionE D Sc a ha i Λ h₂)
        ((globalActionDot D Sc a ha j Λ h₁).app (D.parity j) M)
        (blockSucc D Λ i h₂ (blockSucc D Λ j h₁ β)) =
        eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)
          ((globalEFunctor D Sc a ha j Λ h₁).obj M)) ≫
          (blockInd D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)).map
            ((globalActionDot D Sc a ha j Λ h₁).app (D.parity j) M (blockSucc D Λ j h₁ β)) ≫
            eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)
              ((globalEFunctor D Sc a ha j Λ h₁).obj M)).symm :=
      inductionComponent_map_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β) _
    have hD₁ : (globalActionDot D Sc a ha j Λ h₁).app (D.parity j) M (blockSucc D Λ j h₁ β) =
        eqToHom (inductionComponent_obj_blockSucc D Sc a ha j Λ h₁ β M) ≫
          (blockDot D Sc a ha j Λ h₁ β).app (D.parity j) (M β) ≫
            eqToHom (inductionComponent_obj_blockSucc D Sc a ha j Λ h₁ β M).symm :=
      globalWeightDotComponent_blockSucc D Sc a ha j Λ h₁ _ M β
    rw [hX, hD₄, hE, hD₁]
    unfold globalWeightCrossVia
    rw [superNatTrans_app_of_eq (globalContentDot D Sc j a ha (blockSucc_eq D Λ j e₂)) _
      (show (globalEFunctor D Sc a ha i Λ h₃).obj M (blockSucc D Λ i h₃ β) =
        (blockInd D Sc a ha i Λ h₃ β).obj (M β) from
        inductionComponent_obj_blockSucc D Sc a ha i Λ h₃ β M)]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    exact heightContentMixedSlideRight D Sc a ha hij β.1.card β.1 (M β)
      (m₁ := (blockSucc D Λ j h₁ β).1.card) (γ₁ := (blockSucc D Λ j h₁ β).1)
      (m₂ := (blockSucc₂ D i j Λ h₁ h₂ β).1.card) (γ₂ := (blockSucc₂ D i j Λ h₁ h₂ β).1)
      (m₃ := (blockSucc D Λ i h₃ β).1.card) (γ₃ := (blockSucc D Λ i h₃ β).1)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact (globalEFunctor_comp_isZero D Sc a ha i j Λ h₁ h₂ ζ
      (fun ⟨β, hβ⟩ => hζ ⟨β, hβ⟩) M).eq_of_src _ _

variable [DecidableEq I]

/-- The `slideLeft` field of `RouquierMulticolour` for the signed global crossing. -/
theorem globalActionSignedCross_slide_left_ne :
    globalActionE D Sc a ha j Λ h₁ ◁ globalActionDot D Sc a ha i Λ h₂ ≫
        globalActionSignedCross D Sc a ha Λ i j h₁ h₂ h₃ h₄ =
      SKM.zsign k (D.parity i * D.parity j) •
        (globalActionSignedCross D Sc a ha Λ i j h₁ h₂ h₃ h₄ ≫
          globalActionDot D Sc a ha i Λ h₃ ▷ globalActionE D Sc a ha j Λ h₄) := by
  simp only [globalActionSignedCross, hij, ↓reduceIte]
  rw [← zsmul_koszulSign_eq_zsign_smul]
  exact globalActionCross_slide_left_ne D Sc a ha hij Λ h₁ h₂ h₃ h₄

/-- The `slideRight` field of `RouquierMulticolour` for the signed global crossing. -/
theorem globalActionSignedCross_slide_right_ne :
    globalActionSignedCross D Sc a ha Λ i j h₁ h₂ h₃ h₄ ≫
        globalActionE D Sc a ha i Λ h₃ ◁ globalActionDot D Sc a ha j Λ h₄ =
      SKM.zsign k (D.parity i * D.parity j) •
        (globalActionDot D Sc a ha j Λ h₁ ▷ globalActionE D Sc a ha i Λ h₂ ≫
          globalActionSignedCross D Sc a ha Λ i j h₁ h₂ h₃ h₄) := by
  simp only [globalActionSignedCross, hij, ↓reduceIte]
  rw [← zsmul_koszulSign_eq_zsign_smul]
  exact globalActionCross_slide_right_ne D Sc a ha hij Λ h₁ h₂ h₃ h₄

end Weight

end OddMath.QuiverHecke.CyclotomicAction
