import OddMath.SKM.RouquierMulticolour
import OddMath.SKM.RouquierHomAdjunction

/-!
# The distinct-colour post/post mate of the swapped Hom action

Formalizes the core of the post/post entry of
`docs/Nondegeneracy/SwappedActionAssembly.md` §5: the literal mate (A8) of a
postcomposed factor crossing, taken along the two postcomposition adjunctions,
is postcomposition by the factor mate `crossMate` (`homPostCrossMate_eq`).
No interchange of the crossing with a unit or counit occurs, so the crossing
may have either parity; all remaining identities are even coherence.

Consequently the inverse of the post/post mate is postcomposition by the
inverse of the factor mate (`homPostCrossMateInv`), and for distinct colours
of a `RouquierMulticolour` the latter is supplied by `invNe`
(`homPostCrossMate_isIso`). The content parity shifts and the comparisons
`E_src`, `E_tar` of the assembly note are not treated here.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

theorem homPostUnit_app {a b c : B} {E : b ⟶ c} {F : c ⟶ b}
    (A : SuperAdjunction (k := k) E F) (X : a ⟶ b) :
    (homPostUnit A).app X =
      (rightUnitor X).inv ≫ X ◁ A.unit ≫ (associator X E F).inv := by
  simp [homPostUnit, homPostId, homPostComp, homPostTransform, SuperNatTrans.toNatTrans]

theorem homPostCounit_app {a b c : B} {E : b ⟶ c} {F : c ⟶ b}
    (A : SuperAdjunction (k := k) E F) (X : a ⟶ c) :
    (homPostCounit A).app X =
      (associator X F E).hom ≫ X ◁ A.counit ≫ (rightUnitor X).hom := by
  simp [homPostCounit, homPostId, homPostComp, homPostTransform, SuperNatTrans.toNatTrans]

variable {a b c d x : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : d ⟶ c} {F₂ : c ⟶ d}
  {E₃ : a ⟶ d} {E₄ : b ⟶ c}
  (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)

/-- The literal mate (A8) of the postcomposed crossing `t`: the target post unit,
the crossing postcomposed on the word, and the source post counit. -/
def homPostCrossMate (t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄) (Z : x ⟶ b) :
    (Z ≫ F₁) ≫ E₃ ⟶ (Z ≫ E₄) ≫ F₂ :=
  (homPostUnit A₂).app ((Z ≫ F₁) ≫ E₃) ≫
    ((associator (Z ≫ F₁) E₃ E₂).hom ≫ (Z ≫ F₁) ◁ t ≫
      (associator (Z ≫ F₁) E₁ E₄).inv ≫ (homPostCounit A₁).app Z ▷ E₄) ▷ F₂

/-- The even part of the mate before the crossing. -/
private theorem pre_part (Z : x ⟶ b) :
    (rightUnitor ((Z ≫ F₁) ≫ E₃)).inv ≫ ((Z ≫ F₁) ≫ E₃) ◁ A₂.unit ≫
      (associator ((Z ≫ F₁) ≫ E₃) E₂ F₂).inv ≫
      (associator (Z ≫ F₁) E₃ E₂).hom ▷ F₂ ≫
      (associator (Z ≫ F₁) (E₃ ≫ E₂) F₂).hom ≫
      (associator Z F₁ ((E₃ ≫ E₂) ≫ F₂)).hom =
    (associator Z F₁ E₃).hom ≫ Z ◁ (rightUnitor (F₁ ≫ E₃)).inv ≫
      Z ◁ ((F₁ ≫ E₃) ◁ A₂.unit) ≫ Z ◁ (associator F₁ E₃ (E₂ ≫ F₂)).hom ≫
      Z ◁ (F₁ ◁ (associator E₃ E₂ F₂).inv) := by
  let η : 𝟙 (⟨d⟩ : Underlying2 k B) ⟶
      Underlying2.hom1 (R := k) E₂ ≫ Underlying2.hom1 (R := k) F₂ := ⟨A₂.unit, A₂.unit_mem⟩
  let Z' := Underlying2.hom1 (R := k) Z
  let F₁' := Underlying2.hom1 (R := k) F₁
  let E₂' := Underlying2.hom1 (R := k) E₂
  let F₂' := Underlying2.hom1 (R := k) F₂
  let E₃' := Underlying2.hom1 (R := k) E₃
  have hb : (Bicategory.rightUnitor ((Z' ≫ F₁') ≫ E₃')).inv ≫
      Bicategory.whiskerLeft ((Z' ≫ F₁') ≫ E₃') η ≫
      (Bicategory.associator ((Z' ≫ F₁') ≫ E₃') E₂' F₂').inv ≫
      Bicategory.whiskerRight (Bicategory.associator (Z' ≫ F₁') E₃' E₂').hom F₂' ≫
      (Bicategory.associator (Z' ≫ F₁') (E₃' ≫ E₂') F₂').hom ≫
      (Bicategory.associator Z' F₁' ((E₃' ≫ E₂') ≫ F₂')).hom =
    (Bicategory.associator Z' F₁' E₃').hom ≫
      Bicategory.whiskerLeft Z' (Bicategory.rightUnitor (F₁' ≫ E₃')).inv ≫
      Bicategory.whiskerLeft Z' (Bicategory.whiskerLeft (F₁' ≫ E₃') η) ≫
      Bicategory.whiskerLeft Z' (Bicategory.associator F₁' E₃' (E₂' ≫ F₂')).hom ≫
      Bicategory.whiskerLeft Z'
        (Bicategory.whiskerLeft F₁' (Bicategory.associator E₃' E₂' F₂').inv) := by
    bicategory
  exact congrArg Subtype.val hb

/-- The even part of the mate after the crossing. -/
private theorem post_part (Z : x ⟶ b) :
    (associator Z F₁ ((E₁ ≫ E₄) ≫ F₂)).inv ≫
      (associator (Z ≫ F₁) (E₁ ≫ E₄) F₂).inv ≫
      (associator (Z ≫ F₁) E₁ E₄).inv ▷ F₂ ≫
      (((associator Z F₁ E₁).hom ≫ Z ◁ A₁.counit ≫ (rightUnitor Z).hom) ▷ E₄) ▷ F₂ =
    Z ◁ (associator F₁ (E₁ ≫ E₄) F₂).inv ≫
      Z ◁ ((associator F₁ E₁ E₄).inv ▷ F₂) ≫ Z ◁ ((A₁.counit ▷ E₄) ▷ F₂) ≫
      Z ◁ ((leftUnitor E₄).hom ▷ F₂) ≫ (associator Z E₄ F₂).inv := by
  let ε : Underlying2.hom1 (R := k) F₁ ≫ Underlying2.hom1 (R := k) E₁ ⟶
      𝟙 (⟨b⟩ : Underlying2 k B) := ⟨A₁.counit, A₁.counit_mem⟩
  let Z' := Underlying2.hom1 (R := k) Z
  let F₁' := Underlying2.hom1 (R := k) F₁
  let E₁' := Underlying2.hom1 (R := k) E₁
  let F₂' := Underlying2.hom1 (R := k) F₂
  let E₄' := Underlying2.hom1 (R := k) E₄
  have hb : (Bicategory.associator Z' F₁' ((E₁' ≫ E₄') ≫ F₂')).inv ≫
      (Bicategory.associator (Z' ≫ F₁') (E₁' ≫ E₄') F₂').inv ≫
      Bicategory.whiskerRight (Bicategory.associator (Z' ≫ F₁') E₁' E₄').inv F₂' ≫
      Bicategory.whiskerRight (Bicategory.whiskerRight
        ((Bicategory.associator Z' F₁' E₁').hom ≫ Bicategory.whiskerLeft Z' ε ≫
          (Bicategory.rightUnitor Z').hom) E₄') F₂' =
    Bicategory.whiskerLeft Z' (Bicategory.associator F₁' (E₁' ≫ E₄') F₂').inv ≫
      Bicategory.whiskerLeft Z'
        (Bicategory.whiskerRight (Bicategory.associator F₁' E₁' E₄').inv F₂') ≫
      Bicategory.whiskerLeft Z' (Bicategory.whiskerRight (Bicategory.whiskerRight ε E₄') F₂') ≫
      Bicategory.whiskerLeft Z'
        (Bicategory.whiskerRight (Bicategory.leftUnitor E₄').hom F₂') ≫
      (Bicategory.associator Z' E₄' F₂').inv := by
    bicategory
  exact congrArg Subtype.val hb

/-- The post/post mate is postcomposition by the factor mate `crossMate`,
for a crossing `t` of any parity. -/
theorem homPostCrossMate_eq (t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄) (Z : x ⟶ b) :
    homPostCrossMate A₁ A₂ t Z =
      (associator Z F₁ E₃).hom ≫ Z ◁ crossMate A₁ A₂ t ≫ (associator Z E₄ F₂).inv := by
  have hP := pre_part A₂ (F₁ := F₁) (E₃ := E₃) Z
  have hQ := post_part A₁ (F₂ := F₂) (E₄ := E₄) Z
  -- the crossing piece, conjugated by even associators
  have ht : ((Z ≫ F₁) ◁ t) ▷ F₂ =
      (associator (Z ≫ F₁) (E₃ ≫ E₂) F₂).hom ≫ (associator Z F₁ ((E₃ ≫ E₂) ≫ F₂)).hom ≫
        Z ◁ (F₁ ◁ (t ▷ F₂)) ≫ (associator Z F₁ ((E₁ ≫ E₄) ≫ F₂)).inv ≫
        (associator (Z ≫ F₁) (E₁ ≫ E₄) F₂).inv := by
    rw [TwoSupercategory.whisker_assoc (R := k), TwoSupercategory.comp_whiskerLeft (R := k)]
    simp only [Category.assoc]
  have e : homPostCrossMate A₁ A₂ t Z =
      (rightUnitor ((Z ≫ F₁) ≫ E₃)).inv ≫ ((Z ≫ F₁) ≫ E₃) ◁ A₂.unit ≫
        (associator ((Z ≫ F₁) ≫ E₃) E₂ F₂).inv ≫
        ((associator (Z ≫ F₁) E₃ E₂).hom ≫ (Z ≫ F₁) ◁ t ≫
          (associator (Z ≫ F₁) E₁ E₄).inv ≫
          ((associator Z F₁ E₁).hom ≫ Z ◁ A₁.counit ≫ (rightUnitor Z).hom) ▷ E₄) ▷ F₂ := by
    unfold homPostCrossMate
    erw [homPostUnit_app, homPostCounit_app]
    simp only [Category.assoc]
  rw [e]
  simp only [crossMate, TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.comp_whiskerRight (R := k), Category.assoc, ht]
  rw [← reassoc_of% hP]
  simp only [TwoSupercategory.comp_whiskerRight (R := k)] at hQ
  rw [hQ]

/-- The inverse of the post/post mate, from an inverse of the factor mate. -/
def homPostCrossMateInv (t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄) [IsIso (crossMate A₁ A₂ t)] (Z : x ⟶ b) :
    (Z ≫ E₄) ≫ F₂ ⟶ (Z ≫ F₁) ≫ E₃ :=
  (associator Z E₄ F₂).hom ≫ Z ◁ inv (crossMate A₁ A₂ t) ≫ (associator Z F₁ E₃).inv

theorem homPostCrossMate_inv_products {t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄}
    [IsIso (crossMate A₁ A₂ t)] (Z : x ⟶ b) :
    homPostCrossMate A₁ A₂ t Z ≫ homPostCrossMateInv A₁ A₂ t Z = 𝟙 _ ∧
      homPostCrossMateInv A₁ A₂ t Z ≫ homPostCrossMate A₁ A₂ t Z = 𝟙 _ := by
  rw [homPostCrossMate_eq]
  have h₁ : Z ◁ crossMate A₁ A₂ t ≫ Z ◁ inv (crossMate A₁ A₂ t) = 𝟙 _ := by
    rw [← TwoSupercategory.whiskerLeft_comp (R := k), IsIso.hom_inv_id,
      TwoSupercategory.whiskerLeft_id (R := k)]
  have h₂ : Z ◁ inv (crossMate A₁ A₂ t) ≫ Z ◁ crossMate A₁ A₂ t = 𝟙 _ := by
    rw [← TwoSupercategory.whiskerLeft_comp (R := k), IsIso.inv_hom_id,
      TwoSupercategory.whiskerLeft_id (R := k)]
  constructor
  · simp [homPostCrossMateInv, Category.assoc, reassoc_of% h₁]
  · simp [homPostCrossMateInv, Category.assoc, reassoc_of% h₂]

theorem homPostCrossMate_isIso_of {t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄}
    [IsIso (crossMate A₁ A₂ t)] (Z : x ⟶ b) : IsIso (homPostCrossMate A₁ A₂ t Z) :=
  ⟨⟨homPostCrossMateInv A₁ A₂ t Z, homPostCrossMate_inv_products A₁ A₂ Z⟩⟩

section Multicolour
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}

/-- For distinct colours of a `RouquierMulticolour`, the post/post mate of the
factor crossing is invertible, by `invNe`. -/
theorem homPostCrossMate_isIso (T : RouquierFamily (k := k) (B := B) D)
    {Sc : Scalars D k} (M : RouquierMulticolour T Sc) (i j : I) (hij : i ≠ j)
    {y ν c' d' : X} (h₁ : y + D.α j = d') (h₂ : d' + D.α i = c') (h₃ : y + D.α i = ν)
    (h₄ : ν + D.α j = c') {z : B} (Z : z ⟶ T.obj ν) :
    IsIso (homPostCrossMate (T.adj i h₃) (T.adj i h₂) (T.cross i j h₁ h₂ h₃ h₄) Z) := by
  have := M.invNe i j hij h₁ h₂ h₃ h₄
  exact homPostCrossMate_isIso_of _ _ Z

end Multicolour

end OddMath.SKM
