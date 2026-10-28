/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightBraid
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightSlides

/-!
# The dot slides on weight spaces

Transports `heightInduction_slide_left/right` of `GlobalHeightSlides` through content blocks
and successor blocks to the weight spaces. With `t = -ψ` the Rouquier crossing,
`x₁` the dot of the inner and `x₂` the dot of the outer induction, and `s = (-1)^{|i|}`,

  `E₁ ◁ x₂ ≫ t - s (t ≫ x₁ ▷ E₂) = 1`,  `t ≫ E₁ ◁ x₂ - s (x₁ ▷ E₂ ≫ t) = 1`

(`globalActionSignedCross_slide_left/right`): the slide fields of `SuperRouquierLoc`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

omit [Fintype I] in
theorem scat_zsmul_app {A B : SCat k} {F G : A ⟶ B} (c : ℤ) (x : F ⟶ G) (p : ZMod 2)
    (M : A.carrier) : (c • x).app p M = c • x.app p M := rfl

omit [Fintype I] in
/-- An identity `a₁ b₁ - c a₂ b₂ = 1` between endotransformations of one parity in `𝔖ℭ𝔞𝔱`
holds once it holds for their components of that parity. -/
theorem scat_slide_of_app {A B : SCat k} {F : A ⟶ B} {a₁ b₁ a₂ b₂ : F ⟶ F} {p : ZMod 2}
    (c : ℤ) (ha₁ : a₁ ∈ parity (R := k) F F p) (hb₁ : b₁ ∈ parity (R := k) F F p)
    (ha₂ : a₂ ∈ parity (R := k) F F p) (hb₂ : b₂ ∈ parity (R := k) F F p)
    (h : ∀ M, a₁.app p M ≫ b₁.app p M - c • (a₂.app p M ≫ b₂.app p M) = 𝟙 _) :
    a₁ ≫ b₁ - c • (a₂ ≫ b₂) = 𝟙 F := by
  have z : ∀ {x : F ⟶ F}, x ∈ parity (R := k) F F p → ∀ q, q ≠ p → ∀ M, x.app q M = 0 :=
    fun hx q hq M => Superfunctor.app_eq_zero_of_mem hx hq M
  have e : ∀ q M, (a₁ ≫ b₁ - c • (a₂ ≫ b₂)).app q M =
      (a₁ ≫ b₁).app q M - c • (a₂ ≫ b₂).app q M := fun q M => by
    rw [sub_eq_add_neg, SCat.add_app, SCat.neg_app, scat_zsmul_app, sub_eq_add_neg]
  rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) p with rfl | rfl
  · have := z ha₁ 1 (by decide); have := z hb₁ 1 (by decide)
    have := z ha₂ 1 (by decide); have := z hb₂ 1 (by decide)
    apply SCat.hom_ext
    · intro M
      rw [e, SCat.comp_app_zero, SCat.comp_app_zero, SCat.id_app_zero]
      simp [*]
    · intro M
      rw [e, SCat.comp_app_one, SCat.comp_app_one, SCat.id_app_one]
      simp [*]
  · have := z ha₁ 0 (by decide); have := z hb₁ 0 (by decide)
    have := z ha₂ 0 (by decide); have := z hb₂ 0 (by decide)
    apply SCat.hom_ext
    · intro M
      rw [e, SCat.comp_app_zero, SCat.comp_app_zero, SCat.id_app_zero]
      simp [*]
    · intro M
      rw [e, SCat.comp_app_one, SCat.comp_app_one, SCat.id_app_one]
      simp [*]

omit [Fintype I] in
/-- Componentwise form of `A ≫ (-B) - c (-B ≫ C)` in a product of preadditive categories. -/
theorem pi_slide_apply {J : Type*} {C : J → Type*} [∀ j, Category (C j)]
    [∀ j, Preadditive (C j)] {P : ∀ j, C j} (A B C' : P ⟶ P) (c : ℤ) (j : J) :
    (A ≫ (-B) - c • ((-B) ≫ C')) j = c • (B j ≫ C' j) - A j ≫ B j := by
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, smul_neg, sub_neg_eq_add]
  rw [add_comm, ← sub_eq_add_neg]
  rfl

omit [Fintype I] in
/-- Componentwise form of `(-B) ≫ A - c (C ≫ -B)` in a product of preadditive categories. -/
theorem pi_slide_apply_right {J : Type*} {C : J → Type*} [∀ j, Category (C j)]
    [∀ j, Preadditive (C j)] {P : ∀ j, C j} (A B C' : P ⟶ P) (c : ℤ) (j : J) :
    ((-B) ≫ A - c • (C' ≫ (-B))) j = c • (C' j ≫ B j) - B j ≫ A j := by
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, smul_neg, sub_neg_eq_add]
  rw [add_comm, ← sub_eq_add_neg]
  rfl

omit [Fintype I] in
theorem zmod2_mul_self (p : ZMod 2) : p * p = p := by
  fin_cases p <;> rfl

section Content
variable (i : I)

attribute [local irreducible] ContentSupported

/-- The left slide on height modules, normalized: `s (ψ x₁) - x₂ ψ = 1`. -/
theorem heightInduction_slide_left_one (n : ℕ) (M : HeightModules D Sc a ha n) :
    koszulSign (D.parity i) (D.parity i) •
        ((heightSuperInductionCrossing D Sc i i a ha n).app (D.parity i) M ≫
          (heightSuperInduction D Sc i a ha (n + 1)).map
            ((heightSuperInductionDot D Sc i a ha n).app (D.parity i) M) :
          (heightSuperInduction D Sc i a ha (n + 1)).obj ((heightSuperInduction D Sc i a ha n).obj M) ⟶
            (heightSuperInduction D Sc i a ha (n + 1)).obj
              ((heightSuperInduction D Sc i a ha n).obj M)) -
      ((heightSuperInductionDot D Sc i a ha (n + 1)).app (D.parity i)
          ((heightSuperInduction D Sc i a ha n).obj M) ≫
        (heightSuperInductionCrossing D Sc i i a ha n).app (D.parity i) M :
          (heightSuperInduction D Sc i a ha (n + 1)).obj ((heightSuperInduction D Sc i a ha n).obj M) ⟶
            (heightSuperInduction D Sc i a ha (n + 1)).obj
              ((heightSuperInduction D Sc i a ha n).obj M)) = 𝟙 _ := by
  have H := heightInduction_slide_left D Sc i a ha n M
  rw [zmod2_mul_self] at H
  have H' := congrArg (koszulSign (D.parity i) (D.parity i) • ·) H
  simp only [smul_sub, smul_smul, koszulSign_mul_self, one_smul] at H'
  exact H'

/-- The right slide on height modules, normalized: `s (x₁ ψ) - ψ x₂ = 1`. -/
theorem heightInduction_slide_right_one (n : ℕ) (M : HeightModules D Sc a ha n) :
    koszulSign (D.parity i) (D.parity i) •
        ((heightSuperInduction D Sc i a ha (n + 1)).map
            ((heightSuperInductionDot D Sc i a ha n).app (D.parity i) M) ≫
          (heightSuperInductionCrossing D Sc i i a ha n).app (D.parity i) M :
          (heightSuperInduction D Sc i a ha (n + 1)).obj ((heightSuperInduction D Sc i a ha n).obj M) ⟶
            (heightSuperInduction D Sc i a ha (n + 1)).obj
              ((heightSuperInduction D Sc i a ha n).obj M)) -
      ((heightSuperInductionCrossing D Sc i i a ha n).app (D.parity i) M ≫
        (heightSuperInductionDot D Sc i a ha (n + 1)).app (D.parity i)
          ((heightSuperInduction D Sc i a ha n).obj M) :
          (heightSuperInduction D Sc i a ha (n + 1)).obj ((heightSuperInduction D Sc i a ha n).obj M) ⟶
            (heightSuperInduction D Sc i a ha (n + 1)).obj
              ((heightSuperInduction D Sc i a ha n).obj M)) = 𝟙 _ := by
  have H := heightInduction_slide_right D Sc i a ha n M
  rw [zmod2_mul_self] at H
  have H' := congrArg (koszulSign (D.parity i) (D.parity i) • ·) H
  simp only [smul_sub, smul_smul, koszulSign_mul_self, one_smul] at H'
  exact H'

omit [Fintype I] in
theorem fullHomEquiv_apply {C₀ : Type*} [Category C₀] [Preadditive C₀] [Linear k C₀]
    [Supercategory k C₀] (P : ObjectProperty C₀) {M N : P.FullSubcategory} (f : M ⟶ N) :
    fullHomEquiv (k := k) P M N f = f.hom := rfl

/-- **The left slide on content blocks**, cast-free form, with arbitrary identity transports. -/
theorem heightContentSlideLeftAux (m₀ : ℕ) (γ₀ : Multiset I)
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₀ γ₀))
    (O : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha (m₀ + 1 + 1)
      ({i} + ({i} + γ₀)))) :
    ∀ (a₁ : O = _) (a₂ : _ = _) (a₃ : _ = _) (b₁ : _ = _) (b₂ : _ = _) (b₃ : _ = _),
    koszulSign (D.parity i) (D.parity i) •
        (eqToHom a₁ ≫ (heightBlockCross D Sc a ha i i m₀ γ₀ ({i} + ({i} + γ₀)) rfl).app (D.parity i) N ≫
          eqToHom a₂ ≫ (heightContentInduction D Sc i a ha (m₀ + 1) ({i} + γ₀)).map
            ((heightContentDot D Sc i a ha m₀ γ₀).app (D.parity i) N) ≫ eqToHom a₃) -
      eqToHom b₁ ≫ (heightContentDot D Sc i a ha (m₀ + 1) ({i} + γ₀)).app (D.parity i)
          ((heightContentInduction D Sc i a ha m₀ γ₀).obj N) ≫ eqToHom b₂ ≫
        (heightBlockCross D Sc a ha i i m₀ γ₀ ({i} + ({i} + γ₀)) rfl).app (D.parity i) N ≫
          eqToHom b₃ = 𝟙 O := by
  intro a₁ a₂ a₃ b₁ b₂ b₃
  subst a₁
  apply (fullHomEquiv (k := k) _ _ _).injective
  simp only [map_sub, map_zsmul, fullHomEquiv_apply, ObjectProperty.FullSubcategory.comp_hom,
    fullSubcategory_eqToHom_hom, ObjectProperty.FullSubcategory.id_hom]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact heightInduction_slide_left_one D Sc a ha i m₀ N.obj

/-- **The left dot slide on content blocks, with height transports.** -/
theorem heightContentSlideLeft (m₀ : ℕ) (γ₀ : Multiset I)
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₀ γ₀))
    {m₁ m₂ : ℕ} {γ₁ γ₂ : Multiset I}
    (p₁ : m₀ + 1 = m₁) (q₁ : {i} + γ₀ = γ₁) (p₂ : m₁ + 1 = m₂) (q₂ : {i} + γ₁ = γ₂)
    (hc : {i} + ({i} + γ₀) = γ₂) (pX : m₀ + 1 + 1 = m₂)
    (O : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₂ γ₂)) :
    ∀ (a₁ : O = _) (a₂ : _ = _) (a₃ : _ = _) (b₁ : _ = _) (b₂ : _ = _) (b₃ : _ = _),
    koszulSign (D.parity i) (D.parity i) •
        (eqToHom a₁ ≫ (heightContentCast D Sc a ha pX rfl).map
            ((heightBlockCross D Sc a ha i i m₀ γ₀ γ₂ hc).app (D.parity i) N) ≫
          eqToHom a₂ ≫ (heightContentCast D Sc a ha p₂ q₂).map
            ((heightContentInduction D Sc i a ha m₁ γ₁).map
              ((heightContentCastTrans D Sc a ha p₁ q₁
                (heightContentDot D Sc i a ha m₀ γ₀)).app (D.parity i) N)) ≫ eqToHom a₃) -
      eqToHom b₁ ≫ (heightContentCastTrans D Sc a ha p₂ q₂
          (heightContentDot D Sc i a ha m₁ γ₁)).app (D.parity i)
          ((heightContentCast D Sc a ha p₁ q₁).obj
            ((heightContentInduction D Sc i a ha m₀ γ₀).obj N)) ≫ eqToHom b₂ ≫
        (heightContentCast D Sc a ha pX rfl).map
          ((heightBlockCross D Sc a ha i i m₀ γ₀ γ₂ hc).app (D.parity i) N) ≫
          eqToHom b₃ = 𝟙 O := by
  intro a₁ a₂ a₃ b₁ b₂ b₃
  subst p₁ q₁ p₂ q₂
  obtain rfl : hc = rfl := rfl
  obtain rfl : pX = rfl := rfl
  exact heightContentSlideLeftAux D Sc a ha i m₀ γ₀ N O a₁ a₂ a₃ b₁ b₂ b₃

/-- The right dot slide on content blocks, up to identity transports. -/
theorem heightContentSlideRightAux (m₀ : ℕ) (γ₀ : Multiset I)
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₀ γ₀))
    (O : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha (m₀ + 1 + 1)
      ({i} + ({i} + γ₀)))) :
    ∀ (a₁ : O = _) (a₂ : _ = _) (a₃ : _ = _) (b₁ : _ = _) (b₂ : _ = _) (b₃ : _ = _),
    koszulSign (D.parity i) (D.parity i) •
        (eqToHom a₁ ≫ (heightContentInduction D Sc i a ha (m₀ + 1) ({i} + γ₀)).map
            ((heightContentDot D Sc i a ha m₀ γ₀).app (D.parity i) N) ≫ eqToHom a₂ ≫
          (heightBlockCross D Sc a ha i i m₀ γ₀ ({i} + ({i} + γ₀)) rfl).app (D.parity i) N ≫
            eqToHom a₃) -
      eqToHom b₁ ≫ (heightBlockCross D Sc a ha i i m₀ γ₀ ({i} + ({i} + γ₀)) rfl).app
          (D.parity i) N ≫ eqToHom b₂ ≫
        (heightContentDot D Sc i a ha (m₀ + 1) ({i} + γ₀)).app (D.parity i)
          ((heightContentInduction D Sc i a ha m₀ γ₀).obj N) ≫ eqToHom b₃ = 𝟙 O := by
  intro a₁ a₂ a₃ b₁ b₂ b₃
  subst a₁
  apply (fullHomEquiv (k := k) _ _ _).injective
  simp only [map_sub, map_zsmul, fullHomEquiv_apply, ObjectProperty.FullSubcategory.comp_hom,
    fullSubcategory_eqToHom_hom, ObjectProperty.FullSubcategory.id_hom]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact heightInduction_slide_right_one D Sc a ha i m₀ N.obj

/-- **The right dot slide on content blocks, with height transports.** -/
theorem heightContentSlideRight (m₀ : ℕ) (γ₀ : Multiset I)
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₀ γ₀))
    {m₁ m₂ : ℕ} {γ₁ γ₂ : Multiset I}
    (p₁ : m₀ + 1 = m₁) (q₁ : {i} + γ₀ = γ₁) (p₂ : m₁ + 1 = m₂) (q₂ : {i} + γ₁ = γ₂)
    (hc : {i} + ({i} + γ₀) = γ₂) (pX : m₀ + 1 + 1 = m₂)
    (O : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₂ γ₂)) :
    ∀ (a₁ : O = _) (a₂ : _ = _) (a₃ : _ = _) (b₁ : _ = _) (b₂ : _ = _) (b₃ : _ = _),
    koszulSign (D.parity i) (D.parity i) •
        (eqToHom a₁ ≫ (heightContentCast D Sc a ha p₂ q₂).map
            ((heightContentInduction D Sc i a ha m₁ γ₁).map
              ((heightContentCastTrans D Sc a ha p₁ q₁
                (heightContentDot D Sc i a ha m₀ γ₀)).app (D.parity i) N)) ≫ eqToHom a₂ ≫
          (heightContentCast D Sc a ha pX rfl).map
            ((heightBlockCross D Sc a ha i i m₀ γ₀ γ₂ hc).app (D.parity i) N) ≫ eqToHom a₃) -
      eqToHom b₁ ≫ (heightContentCast D Sc a ha pX rfl).map
          ((heightBlockCross D Sc a ha i i m₀ γ₀ γ₂ hc).app (D.parity i) N) ≫ eqToHom b₂ ≫
        (heightContentCastTrans D Sc a ha p₂ q₂
          (heightContentDot D Sc i a ha m₁ γ₁)).app (D.parity i)
          ((heightContentCast D Sc a ha p₁ q₁).obj
            ((heightContentInduction D Sc i a ha m₀ γ₀).obj N)) ≫ eqToHom b₃ = 𝟙 O := by
  intro a₁ a₂ a₃ b₁ b₂ b₃
  subst p₁ q₁ p₂ q₂
  obtain rfl : hc = rfl := rfl
  obtain rfl : pX = rfl := rfl
  exact heightContentSlideRightAux D Sc a ha i m₀ γ₀ N O a₁ a₂ a₃ b₁ b₂ b₃

end Content

section Weight
variable [DecidableEq I] (i : I) (Λ : X) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁)
  (h₂ : x₁ + D.α i = x₂)

theorem globalActionSignedCross_mem_same :
    globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂ ∈ parity (R := k) _ _ (D.parity i) := by
  have h := globalActionSignedCross_mem D Sc a ha Λ i i h₁ h₂ h₁ h₂
  rwa [zmod2_mul_self] at h

theorem globalActionSignedCross_slide_left :
    globalActionE D Sc a ha i Λ h₁ ◁ globalActionDot D Sc a ha i Λ h₂ ≫
        globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂ -
      koszulSign (D.parity i) (D.parity i) •
        (globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂ ≫
          globalActionDot D Sc a ha i Λ h₁ ▷ globalActionE D Sc a ha i Λ h₂) = 𝟙 _ := by
  have m1 := TwoSupercategory.whiskerLeft_mem (R := k) (globalActionE D Sc a ha i Λ h₁) (globalActionDot_mem D Sc a ha i Λ h₂)
  have m2 := globalActionSignedCross_mem_same D Sc a ha i Λ h₁ h₂
  have m3 := TwoSupercategory.whiskerRight_mem (R := k) (globalActionE D Sc a ha i Λ h₂) (globalActionDot_mem D Sc a ha i Λ h₁)
  refine scat_slide_of_app _ m1 m2 m2 m3 fun M => ?_
  have hs : globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂ =
      -globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂ := by
    simp [globalActionSignedCross]
  rw [hs, SCat.neg_app]
  funext ζ
  rw [pi_slide_apply, SCat.whiskerLeft_app, SCat.whiskerRight_app]
  by_cases hζ : ∃ β, blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β) = ζ
  · obtain ⟨β, rfl⟩ := hζ
    have hX : (globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂).app (D.parity i) M
        (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) =
        globalWeightCrossVia D Sc a ha i i Λ h₁ h₂ h₁ h₂ (D.parity i) M β
          (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) rfl :=
      globalWeightCrossComponent_of D Sc a ha i i Λ h₁ h₂ h₁ h₂ _ M β
        (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) rfl
    have hD₂ : (globalActionDot D Sc a ha i Λ h₂).app (D.parity i)
        (Superfunctor.obj (globalActionE D Sc a ha i Λ h₁) M)
        (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) =
        eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)
          ((globalEFunctor D Sc a ha i Λ h₁).obj M)) ≫
          (blockDot D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)).app (D.parity i)
            ((globalEFunctor D Sc a ha i Λ h₁).obj M (blockSucc D Λ i h₁ β)) ≫
            eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)
              ((globalEFunctor D Sc a ha i Λ h₁).obj M)).symm :=
      globalWeightDotComponent_blockSucc D Sc a ha i Λ h₂ _ _ (blockSucc D Λ i h₁ β)
    have hE : Superfunctor.map (globalActionE D Sc a ha i Λ h₂)
        ((globalActionDot D Sc a ha i Λ h₁).app (D.parity i) M)
        (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) =
        eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)
          ((globalEFunctor D Sc a ha i Λ h₁).obj M)) ≫
          (blockInd D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)).map
            ((globalActionDot D Sc a ha i Λ h₁).app (D.parity i) M (blockSucc D Λ i h₁ β)) ≫
            eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)
              ((globalEFunctor D Sc a ha i Λ h₁).obj M)).symm :=
      inductionComponent_map_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β) _
    have hD₁ : (globalActionDot D Sc a ha i Λ h₁).app (D.parity i) M (blockSucc D Λ i h₁ β) =
        eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₁ β M) ≫
          (blockDot D Sc a ha i Λ h₁ β).app (D.parity i) (M β) ≫
            eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₁ β M).symm :=
      globalWeightDotComponent_blockSucc D Sc a ha i Λ h₁ _ M β
    rw [hX, hD₂, hE, hD₁]
    unfold globalWeightCrossVia
    rw [superNatTrans_app_of_eq (blockDot D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)) _
      (show (globalEFunctor D Sc a ha i Λ h₁).obj M (blockSucc D Λ i h₁ β) =
        (blockInd D Sc a ha i Λ h₁ β).obj (M β) from
        inductionComponent_obj_blockSucc D Sc a ha i Λ h₁ β M)]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    exact heightContentSlideLeft D Sc a ha i β.1.card β.1 (M β)
      (m₁ := (blockSucc D Λ i h₁ β).1.card) (γ₁ := (blockSucc D Λ i h₁ β).1)
      (m₂ := (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)).1.card)
      (γ₂ := (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)).1) _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact (globalEFunctor_comp_isZero D Sc a ha i i Λ h₁ h₂ ζ
      (fun ⟨β, hβ⟩ => hζ ⟨β, hβ⟩) M).eq_of_src _ _

theorem globalActionSignedCross_slide_right :
    globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂ ≫
        globalActionE D Sc a ha i Λ h₁ ◁ globalActionDot D Sc a ha i Λ h₂ -
      koszulSign (D.parity i) (D.parity i) •
        (globalActionDot D Sc a ha i Λ h₁ ▷ globalActionE D Sc a ha i Λ h₂ ≫
          globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂) = 𝟙 _ := by
  have m1 := TwoSupercategory.whiskerLeft_mem (R := k) (globalActionE D Sc a ha i Λ h₁) (globalActionDot_mem D Sc a ha i Λ h₂)
  have m2 := globalActionSignedCross_mem_same D Sc a ha i Λ h₁ h₂
  have m3 := TwoSupercategory.whiskerRight_mem (R := k) (globalActionE D Sc a ha i Λ h₂) (globalActionDot_mem D Sc a ha i Λ h₁)
  refine scat_slide_of_app _ m2 m1 m3 m2 fun M => ?_
  have hs : globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂ =
      -globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂ := by
    simp [globalActionSignedCross]
  rw [hs, SCat.neg_app]
  funext ζ
  rw [pi_slide_apply_right, SCat.whiskerLeft_app, SCat.whiskerRight_app]
  by_cases hζ : ∃ β, blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β) = ζ
  · obtain ⟨β, rfl⟩ := hζ
    have hX : (globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂).app (D.parity i) M
        (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) =
        globalWeightCrossVia D Sc a ha i i Λ h₁ h₂ h₁ h₂ (D.parity i) M β
          (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) rfl :=
      globalWeightCrossComponent_of D Sc a ha i i Λ h₁ h₂ h₁ h₂ _ M β
        (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) rfl
    have hD₂ : (globalActionDot D Sc a ha i Λ h₂).app (D.parity i)
        (Superfunctor.obj (globalActionE D Sc a ha i Λ h₁) M)
        (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) =
        eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)
          ((globalEFunctor D Sc a ha i Λ h₁).obj M)) ≫
          (blockDot D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)).app (D.parity i)
            ((globalEFunctor D Sc a ha i Λ h₁).obj M (blockSucc D Λ i h₁ β)) ≫
            eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)
              ((globalEFunctor D Sc a ha i Λ h₁).obj M)).symm :=
      globalWeightDotComponent_blockSucc D Sc a ha i Λ h₂ _ _ (blockSucc D Λ i h₁ β)
    have hE : Superfunctor.map (globalActionE D Sc a ha i Λ h₂)
        ((globalActionDot D Sc a ha i Λ h₁).app (D.parity i) M)
        (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) =
        eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)
          ((globalEFunctor D Sc a ha i Λ h₁).obj M)) ≫
          (blockInd D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)).map
            ((globalActionDot D Sc a ha i Λ h₁).app (D.parity i) M (blockSucc D Λ i h₁ β)) ≫
            eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)
              ((globalEFunctor D Sc a ha i Λ h₁).obj M)).symm :=
      inductionComponent_map_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β) _
    have hD₁ : (globalActionDot D Sc a ha i Λ h₁).app (D.parity i) M (blockSucc D Λ i h₁ β) =
        eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₁ β M) ≫
          (blockDot D Sc a ha i Λ h₁ β).app (D.parity i) (M β) ≫
            eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h₁ β M).symm :=
      globalWeightDotComponent_blockSucc D Sc a ha i Λ h₁ _ M β
    rw [hX, hD₂, hE, hD₁]
    unfold globalWeightCrossVia
    rw [superNatTrans_app_of_eq (blockDot D Sc a ha i Λ h₂ (blockSucc D Λ i h₁ β)) _
      (show (globalEFunctor D Sc a ha i Λ h₁).obj M (blockSucc D Λ i h₁ β) =
        (blockInd D Sc a ha i Λ h₁ β).obj (M β) from
        inductionComponent_obj_blockSucc D Sc a ha i Λ h₁ β M)]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    exact heightContentSlideRight D Sc a ha i β.1.card β.1 (M β)
      (m₁ := (blockSucc D Λ i h₁ β).1.card) (γ₁ := (blockSucc D Λ i h₁ β).1)
      (m₂ := (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)).1.card)
      (γ₂ := (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)).1) _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact (globalEFunctor_comp_isZero D Sc a ha i i Λ h₁ h₂ ζ
      (fun ⟨β, hβ⟩ => hζ ⟨β, hβ⟩) M).eq_of_src _ _

end Weight

end OddMath.QuiverHecke.CyclotomicAction
