/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightBraid
import OddMath.QuiverHecke.CyclotomicAction.GlobalRouquierData

/-!
# The equal-colour braid relation on weight spaces

Ports `globalCross_sameBraid` of `Categorification/KLR/CyclotomicAction/GlobalBraid.lean`
to the weight spaces. On content blocks the two crossings of three inductions are the
inner crossing `Ind(t)` and the outer crossing `t_{Ind}` of `GlobalHeightBraid`, conjugated
by identity transports of heights and contents (`heightContentBraid`). At a block that is
not a three-step successor the triple composite vanishes. Hence the weight crossing
satisfies `t₂ t₁ t₂ = t₁ t₂ t₁` with `t₁ = t ▷ E` and `t₂ = E ◁ t`
(`globalActionCross_braid`), and so does the signed Rouquier crossing `-t`
(`globalActionSignedCross_braid`): this is the `braid` field of `RouquierFamily`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

omit [Fintype I] in
/-- Two homogeneous endotransformations of the same parity satisfy the braid relation once
their components of that parity do. -/
theorem superTrans_braid_of_app {C₁ C₂ : Type*} [Category C₁] [Preadditive C₁] [Linear k C₁]
    [Supercategory k C₁] [Category C₂] [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
    {F : Superfunctor k C₁ C₂} {x y : F ⟶ F} {d : ZMod 2}
    (hx : SuperNatTrans.IsHomogeneous x d) (hy : SuperNatTrans.IsHomogeneous y d)
    (h : ∀ M, x.app d M ≫ y.app d M ≫ x.app d M = y.app d M ≫ x.app d M ≫ y.app d M) :
    x ≫ y ≫ x = y ≫ x ≫ y := by
  have hx' : ∀ q, q ≠ d → ∀ M, x.app q M = 0 := fun q hq M => congrFun (hx q hq) M
  have hy' : ∀ q, q ≠ d → ∀ M, y.app q M = 0 := fun q hq M => congrFun (hy q hq) M
  rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) d with rfl | rfl
  · have x1 := hx' 1 (by decide)
    have y1 := hy' 1 (by decide)
    apply Superfunctor.hom_ext_parity
    · intro M
      simp only [Superfunctor.comp_app_zero, x1, y1, Limits.comp_zero, Limits.zero_comp, add_zero]
      exact h M
    · intro M
      simp [Superfunctor.comp_app_one, Superfunctor.comp_app_zero, x1, y1]
  · have x0 := hx' 0 (by decide)
    have y0 := hy' 0 (by decide)
    apply Superfunctor.hom_ext_parity
    · intro M
      simp [Superfunctor.comp_app_one, Superfunctor.comp_app_zero, x0, y0]
    · intro M
      simp only [Superfunctor.comp_app_one, Superfunctor.comp_app_zero, x0, y0, Limits.comp_zero,
        Limits.zero_comp, add_zero, zero_add]
      exact h M

omit [Fintype I] in
/-- The underlying morphism of an identity transport in a full subcategory. -/
theorem fullSubcategory_eqToHom_hom {C₀ : Type*} [Category C₀] {P : ObjectProperty C₀}
    {X Y : P.FullSubcategory} (e : X = Y) :
    (eqToHom e).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj e) := by
  cases e; rfl

omit [Fintype I] in
/-- A homogeneous supernatural transformation at equal objects is conjugate by identity
transports. -/
theorem superNatTrans_app_of_eq {C₁ C₂ : Type*} [Category C₁] [Preadditive C₁] [Linear k C₁]
    [Supercategory k C₁] [Category C₂] [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
    {F G : Superfunctor k C₁ C₂} (x : F ⟶ G) (p : ZMod 2) {Z Z' : C₁} (e : Z = Z') :
    x.app p Z = eqToHom (congrArg F.obj e) ≫ x.app p Z' ≫ eqToHom (congrArg G.obj e).symm := by
  subst e
  simp

omit [Fintype I] in
/-- The braid relation survives conjugation by identity transports. -/
theorem braid_of_conj {C₀ : Type*} [Category C₀] {O P Q : C₀} (A : P ⟶ P) (B : Q ⟶ Q)
    (a₁ : O = P) (a₂ : P = O) (b₁ : O = Q) (b₂ : Q = O) (c : P = Q) (c' : Q = P)
    (h : ∀ e : Q = P, B ≫ eqToHom e ≫ A ≫ eqToHom e.symm ≫ B =
      eqToHom e ≫ A ≫ eqToHom e.symm ≫ B ≫ eqToHom e ≫ A ≫ eqToHom e.symm) :
    eqToHom a₁ ≫ A ≫ eqToHom c ≫ B ≫ eqToHom c' ≫ A ≫ eqToHom a₂ =
      eqToHom b₁ ≫ B ≫ eqToHom c' ≫ A ≫ eqToHom c ≫ B ≫ eqToHom b₂ := by
  subst a₁ b₁
  have := h rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at this ⊢
  exact this.symm

section Content
variable (i : I)

attribute [local irreducible] ContentSupported

local notation "d" => D.parity i * D.parity i

/-- **The equal-colour braid on content blocks.** The outer crossing `B` of the two outer
inductions and the inner crossing `A` under the outer induction satisfy the braid relation,
up to the identity transport `e` between the two presentations of the triple induction. -/
theorem heightContentBraidAux (m₀ : ℕ) (γ₀ : Multiset I)
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₀ γ₀))
    (e : (heightBlockInduction₂ D Sc a ha i i (m₀ + 1) ({i} + γ₀) ({i} + ({i} + ({i} + γ₀))) rfl).obj
          ((heightContentInduction D Sc i a ha m₀ γ₀).obj N) =
      (heightContentInduction D Sc i a ha (m₀ + 1 + 1) ({i} + ({i} + γ₀))).obj
          ((heightBlockInduction₂ D Sc a ha i i m₀ γ₀ ({i} + ({i} + γ₀)) rfl).obj N)) :
    let A := (heightContentInduction D Sc i a ha (m₀ + 1 + 1) ({i} + ({i} + γ₀))).map
      ((heightBlockCross D Sc a ha i i m₀ γ₀ ({i} + ({i} + γ₀)) rfl).app d N)
    let B := (heightBlockCross D Sc a ha i i (m₀ + 1) ({i} + γ₀) ({i} + ({i} + ({i} + γ₀))) rfl).app d
      ((heightContentInduction D Sc i a ha m₀ γ₀).obj N)
    B ≫ eqToHom e ≫ A ≫ eqToHom e.symm ≫ B =
      eqToHom e ≫ A ≫ eqToHom e.symm ≫ B ≫ eqToHom e ≫ A ≫ eqToHom e.symm := by
  intro A B
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, fullSubcategory_eqToHom_hom]
  generalize congrArg _ e = e'
  obtain rfl : e' = rfl := rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact heightSuperInduction_braid_same D Sc i a ha m₀ N.obj

/-- **The equal-colour braid on content blocks, with height transports.** The crossing of the two inner inductions
under the outer induction and the crossing of the two outer inductions, each followed by an
identity transport of heights and contents, satisfy the braid relation. -/
theorem heightContentBraid (m₀ : ℕ) (γ₀ : Multiset I)
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₀ γ₀))
    {m₁ m₂ m₃ : ℕ} {γ₁ γ₂ γ₃ δ : Multiset I}
    (p₁ : m₀ + 1 = m₁) (q₁ : {i} + γ₀ = γ₁) (hc₁ : {i} + ({i} + γ₀) = γ₂)
    (p₂ : m₀ + 1 + 1 = m₂) (p₃ : m₂ + 1 = m₃) (q₃ : {i} + γ₂ = γ₃)
    (hc₂ : {i} + ({i} + γ₁) = δ) (p₄ : m₁ + 1 + 1 = m₃) (q₄ : δ = γ₃)
    (e : (heightContentCast D Sc a ha p₄ q₄).obj
        ((heightBlockInduction₂ D Sc a ha i i m₁ γ₁ δ hc₂).obj
          ((heightContentCast D Sc a ha p₁ q₁).obj ((heightContentInduction D Sc i a ha m₀ γ₀).obj N))) =
      (heightContentCast D Sc a ha p₃ q₃).obj ((heightContentInduction D Sc i a ha m₂ γ₂).obj
        ((heightContentCast D Sc a ha p₂ rfl).obj
          ((heightBlockInduction₂ D Sc a ha i i m₀ γ₀ γ₂ hc₁).obj N)))) :
    let A := (heightContentCast D Sc a ha p₃ q₃).map ((heightContentInduction D Sc i a ha m₂ γ₂).map
      ((heightContentCast D Sc a ha p₂ rfl).map ((heightBlockCross D Sc a ha i i m₀ γ₀ γ₂ hc₁).app d N)))
    let B := (heightContentCast D Sc a ha p₄ q₄).map ((heightBlockCross D Sc a ha i i m₁ γ₁ δ hc₂).app d
      ((heightContentCast D Sc a ha p₁ q₁).obj ((heightContentInduction D Sc i a ha m₀ γ₀).obj N)))
    B ≫ eqToHom e ≫ A ≫ eqToHom e.symm ≫ B =
      eqToHom e ≫ A ≫ eqToHom e.symm ≫ B ≫ eqToHom e ≫ A ≫ eqToHom e.symm := by
  intro A B
  subst p₁ q₁ hc₁ p₂ p₃ q₃ hc₂
  obtain rfl : p₄ = rfl := rfl
  obtain rfl : q₄ = rfl := rfl
  exact heightContentBraidAux D Sc a ha i m₀ γ₀ N e

end Content

section Weight
variable (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (h₃ : x₂ + D.α i = x₃)

/-- Away from three-step successor blocks the triple induction vanishes. -/
theorem globalEFunctor_comp₃_isZero (ζ : WeightBlocks D Λ x₃)
    (hζ : ¬ ∃ β, blockSucc D Λ i h₃ (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) = ζ)
    (M : WeightProduct D Sc a ha Λ x₀) :
    Limits.IsZero ((inductionComponent D Sc a ha i Λ h₃ ζ).obj
      ((globalEFunctor D Sc a ha i Λ h₂).obj ((globalEFunctor D Sc a ha i Λ h₁).obj M))) := by
  by_cases hγ : ∃ γ, blockSucc D Λ i h₃ γ = ζ
  · obtain ⟨γ, rfl⟩ := hγ
    have hz : Limits.IsZero ((globalEFunctor D Sc a ha i Λ h₂).obj
        ((globalEFunctor D Sc a ha i Λ h₁).obj M) γ) :=
      globalEFunctor_comp_isZero D Sc a ha i i Λ h₁ h₂ γ
        (fun ⟨β, hβ⟩ => hζ ⟨β, by rw [← hβ]⟩) M
    exact Limits.IsZero.of_iso ((blockInd D Sc a ha i Λ h₃ γ).toFunctor.map_isZero hz)
      (eqToIso (inductionComponent_obj_blockSucc D Sc a ha i Λ h₃ γ _))
  · exact inductionComponent_isZero D Sc a ha i Λ h₃ ζ hγ _

local notation "d" => D.parity i * D.parity i

/-- **The equal-colour braid relation on weight spaces**, for the crossing of
`GlobalWeightCross`. -/
theorem globalActionCross_braid :
    let t₁ := (associator (globalActionE D Sc a ha i Λ h₁) (globalActionE D Sc a ha i Λ h₂)
        (globalActionE D Sc a ha i Λ h₃)).inv ≫
      globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂ ▷ globalActionE D Sc a ha i Λ h₃ ≫
      (associator (globalActionE D Sc a ha i Λ h₁) (globalActionE D Sc a ha i Λ h₂)
        (globalActionE D Sc a ha i Λ h₃)).hom
    let t₂ := globalActionE D Sc a ha i Λ h₁ ◁ globalActionCross D Sc a ha i i Λ h₂ h₃ h₂ h₃
    t₂ ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ t₁ := by
  intro t₁ t₂
  have ht₁ : t₁ = globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂ ▷
      globalActionE D Sc a ha i Λ h₃ := by
    simp only [t₁, SCat.associator_hom, SCat.associator_inv]
    erw [Category.id_comp, Category.comp_id]
  rw [ht₁]
  refine (superTrans_braid_of_app
    (Superfunctor.mem_parity_iff_isHomogeneous.1
      (TwoSupercategory.whiskerLeft_mem (R := k) _ (globalActionCross_mem D Sc a ha i i Λ h₂ h₃ h₂ h₃)))
    (Superfunctor.mem_parity_iff_isHomogeneous.1
      (TwoSupercategory.whiskerRight_mem (R := k) _ (globalActionCross_mem D Sc a ha i i Λ h₁ h₂ h₁ h₂)))
    fun M => ?_)
  funext ζ
  change globalWeightCrossComponent D Sc a ha i i Λ h₂ h₃ h₂ h₃ d
        ((globalEFunctor D Sc a ha i Λ h₁).obj M) ζ ≫
      (inductionComponent D Sc a ha i Λ h₃ ζ).map
        ((globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂).app d M) ≫
      globalWeightCrossComponent D Sc a ha i i Λ h₂ h₃ h₂ h₃ d
        ((globalEFunctor D Sc a ha i Λ h₁).obj M) ζ =
    (inductionComponent D Sc a ha i Λ h₃ ζ).map
        ((globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂).app d M) ≫
      globalWeightCrossComponent D Sc a ha i i Λ h₂ h₃ h₂ h₃ d
        ((globalEFunctor D Sc a ha i Λ h₁).obj M) ζ ≫
      (inductionComponent D Sc a ha i Λ h₃ ζ).map
        ((globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂).app d M)
  by_cases hζ : ∃ β, blockSucc D Λ i h₃ (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) = ζ
  · obtain ⟨β, rfl⟩ := hζ
    have hX : (globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂).app d M
        (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) =
        globalWeightCrossVia D Sc a ha i i Λ h₁ h₂ h₁ h₂ d M β
          (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) rfl :=
      globalWeightCrossComponent_of D Sc a ha i i Λ h₁ h₂ h₁ h₂ d M β
        (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)) rfl
    have hY := globalWeightCrossComponent_of D Sc a ha i i Λ h₂ h₃ h₂ h₃ d
      ((globalEFunctor D Sc a ha i Λ h₁).obj M) (blockSucc D Λ i h₁ β) _ rfl
    rw [inductionComponent_map_blockSucc, hX, hY]
    unfold globalWeightCrossVia
    rw [superNatTrans_app_of_eq (contentCross D Sc a ha i i Λ (blockSucc D Λ i h₁ β) _ _) d
      (show (globalEFunctor D Sc a ha i Λ h₁).obj M (blockSucc D Λ i h₁ β) =
        (blockInd D Sc a ha i Λ h₁ β).obj (M β) from
        inductionComponent_obj_blockSucc D Sc a ha i Λ h₁ β M)]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc,
      eqToHom_trans, eqToHom_trans_assoc]
    exact (braid_of_conj _ _ _ _ _ _ _ _ fun e =>
      heightContentBraid D Sc a ha i β.1.card β.1 (M β)
        (m₁ := (blockSucc D Λ i h₁ β).1.card) (γ₁ := (blockSucc D Λ i h₁ β).1)
        (γ₂ := (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)).1)
        (m₂ := (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)).1.card)
        (m₃ := (blockSucc D Λ i h₃ (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β))).1.card)
        (γ₃ := (blockSucc D Λ i h₃ (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β))).1)
        (δ := (blockSucc D Λ i h₃ (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β))).1)
        _ _ _ _ _ _ _ _ rfl e).symm
  · exact (globalEFunctor_comp₃_isZero D Sc a ha i Λ h₁ h₂ h₃ ζ hζ M).eq_of_src _ _

/-- **The braid relation for the Rouquier crossing** `-ψ` on weight spaces: the signs of
the three crossings on each side cancel. -/
theorem globalActionSignedCross_braid [DecidableEq I] :
    let t₁ := (associator (globalActionE D Sc a ha i Λ h₁) (globalActionE D Sc a ha i Λ h₂)
        (globalActionE D Sc a ha i Λ h₃)).inv ≫
      globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂ ▷ globalActionE D Sc a ha i Λ h₃ ≫
      (associator (globalActionE D Sc a ha i Λ h₁) (globalActionE D Sc a ha i Λ h₂)
        (globalActionE D Sc a ha i Λ h₃)).hom
    let t₂ := globalActionE D Sc a ha i Λ h₁ ◁ globalActionSignedCross D Sc a ha Λ i i h₂ h₃ h₂ h₃
    t₂ ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ t₁ := by
  intro t₁ t₂
  have h := globalActionCross_braid D Sc a ha i Λ h₁ h₂ h₃
  simp only at h
  simp only [t₁, t₂, globalActionSignedCross, ite_true,
    TwoSupercategory.neg_whiskerRight (R := k), TwoSupercategory.whiskerLeft_neg (R := k),
    Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  rw [h]

/-- The braid field of `RouquierFamily` for `globalRouquierData`. -/
theorem globalRouquierData_braid [DecidableEq I] :
    let R := globalRouquierData D Sc a ha Λ
    let t₁ := (associator (R.E i h₁) (R.E i h₂) (R.E i h₃)).inv ≫
      R.cross i i h₁ h₂ h₁ h₂ ▷ R.E i h₃ ≫ (associator (R.E i h₁) (R.E i h₂) (R.E i h₃)).hom
    let t₂ := R.E i h₁ ◁ R.cross i i h₂ h₃ h₂ h₃
    t₂ ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ t₁ :=
  globalActionSignedCross_braid D Sc a ha i Λ h₁ h₂ h₃

end Weight


end OddMath.QuiverHecke.CyclotomicAction
