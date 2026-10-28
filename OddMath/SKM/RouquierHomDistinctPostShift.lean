import OddMath.SKM.RouquierHomDistinctPost
import OddMath.SKM.RouquierHomPostCoordinates
import OddMath.SKM.RouquierNormalizedHomAdjunction

/-!
# The distinct-colour post/post mate with content parity shifts

Formalizes the post/post entry of `docs/Nondegeneracy/SwappedActionAssembly.md` §5
with the content parity shifts. Raising postcomposition by the colour of `E₁, E₂`
carries the shift `S_p`, and by the colour of `E₃, E₄` the shift `S_q`; the shifted
adjunctions are the composites of the postcomposition adjunctions with the
self-adjunctions of the shifts, as in `homContentPostAdjunction`.

The shifted crossing `homShiftedPostCrossing` of a factor crossing
`t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄` is the transport of `Y ◁ t` along the two removals
`Θ = S_p(z_q ▷ E₂) ; z_p` of `MixedColourBlockCompletion.md` (4), with
coefficient `1`. Its literal mate along the shifted adjunctions,
`homShiftedPostCrossMate`, is the unshifted post/post mate `homPostCrossMate`
conjugated by the even-or-odd removals of the source and target words
(`homShiftedPostCrossMate_eq`), with **no** residual sign: the sign from moving
the source removal through the crossing cancels the signs from the two shift
squares. Hence it is invertible whenever the factor mate is, in particular for
distinct colours by `invNe` (`homShiftedPostCrossMate_isIso`).
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]

variable {a b c d x : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : d ⟶ c} {F₂ : c ⟶ d}
  {E₃ : a ⟶ d} {E₄ : b ⟶ c}
  (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)

/-- The shifted postcomposition adjunction: postcomposition followed by `S_p`. -/
abbrev homShiftedPostAdjunction {E : b ⟶ c} {F : c ⟶ b} (A : SuperAdjunction (k := k) E F)
    (p : ZMod 2) :
    homPost (k := k) (a := x) E ⋙ homParityShift (k := k) p ⊣
      homParityShift (k := k) p ⋙ homPost (k := k) F :=
  (homPostAdjunction A).comp (homParityShiftAdjunction p)

/-- The shifted factor crossing: `Y ◁ t` transported along the two parity removals
of the source and target words, with coefficient one. -/
def homShiftedPostCrossing (p q : ZMod 2) (t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄) (Y : x ⟶ a) :
    (homParityShift (k := k) p).obj ((homParityShift (k := k) q).obj (Y ≫ E₃) ≫ E₂) ⟶
      (homParityShift (k := k) q).obj ((homParityShift (k := k) p).obj (Y ≫ E₁) ≫ E₄) :=
  (homParityShift (k := k) p).map
      (((homParityShiftDatum (k := k) q).iso (Y ≫ E₃)).hom ▷ E₂) ≫
    ((homParityShiftDatum (k := k) p).iso ((Y ≫ E₃) ≫ E₂)).hom ≫
    (associator Y E₃ E₂).hom ≫ Y ◁ t ≫ (associator Y E₁ E₄).inv ≫
    ((homParityShiftDatum (k := k) q).iso ((Y ≫ E₁) ≫ E₄)).inv ≫
    (homParityShift (k := k) q).map
      (((homParityShiftDatum (k := k) p).iso (Y ≫ E₁)).inv ▷ E₄)

/-- The literal mate (A8) of the shifted crossing along the shifted adjunctions. -/
def homShiftedPostCrossMate (p q : ZMod 2) (t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄) (Z : x ⟶ b) :
    (homParityShift (k := k) q).obj (((homParityShift (k := k) p).obj Z ≫ F₁) ≫ E₃) ⟶
      (homParityShift (k := k) p).obj ((homParityShift (k := k) q).obj (Z ≫ E₄)) ≫ F₂ :=
  (homShiftedPostAdjunction A₂ p).unit.app _ ≫
    (homParityShift (k := k) p ⋙ homPost (k := k) F₂).map
      (homShiftedPostCrossing p q t ((homParityShift (k := k) p).obj Z ≫ F₁) ≫
        (homPost (k := k) E₄ ⋙ homParityShift (k := k) q).map
          ((homShiftedPostAdjunction A₁ p).counit.app Z))

/-- The shifted counit, with both shift removals made explicit. -/
theorem homShiftedPostAdjunction_counit_app {E : b ⟶ c} {F : c ⟶ b}
    (A : SuperAdjunction (k := k) E F) (p : ZMod 2) (Z : x ⟶ c) :
    (homShiftedPostAdjunction A p).counit.app Z = sign k (p * p) •
      (((homParityShiftDatum (k := k) p).iso (((homParityShift (k := k) p).obj Z ≫ F) ≫ E)).hom ≫
        (homPostCounit (a := x) A).app ((homParityShift (k := k) p).obj Z) ≫
        ((homParityShiftDatum (k := k) p).iso Z).hom) := by
  have hc := (homParityShiftDatum (k := k) p).hom_naturality_even
    (homPostCounit_mem (a := x) A ((homParityShift (k := k) p).obj Z))
  simp only [Functor.id_obj] at hc
  rw [Adjunction.comp_counit_app, homParityShiftAdjunction_counit_app,
    homParityShiftSquare_hom_app_map,
    (homParityShiftDatum (k := k) p).hom_naturality ((homParityShiftDatum (k := k) p).hom_mem Z),
    Linear.comp_smul, ← Category.assoc]
  change sign k (p * p) • (((homParityShift (k := k) p).map
      ((homPostCounit (a := x) A).app ((homParityShift (k := k) p).obj Z)) ≫ _) ≫ _) = _
  rw [hc, Category.assoc]
  rfl

/-- The shifted unit, with the shift square made explicit. -/
theorem homShiftedPostAdjunction_unit_app {E : b ⟶ c} {F : c ⟶ b}
    (A : SuperAdjunction (k := k) E F) (p : ZMod 2) (X : x ⟶ b) :
    (homShiftedPostAdjunction A p).unit.app X =
      (homPostUnit A).app X ≫ (homParityShiftSquare (k := k) p).inv.app (X ≫ E) ▷ F := by
  rw [Adjunction.comp_unit_app, homParityShiftAdjunction_unit_app]
  rfl

omit [TwoSupercategory k B] in
/-- The inverse of the shift square through the comparison isomorphisms. -/
theorem homParityShiftSquare_inv_app_eq (p : ZMod 2) (V : x ⟶ c) :
    (homParityShiftSquare (k := k) p).inv.app V =
      ((homParityShiftDatum (k := k) p).iso V).inv ≫
        (homParityShift (k := k) p).map ((homParityShiftDatum (k := k) p).iso V).inv := by
  apply (cancel_epi ((homParityShiftSquare (k := k) p).hom.app V)).mp
  rw [Iso.hom_inv_id_app, homParityShiftSquare_hom_app_map]
  simp only [Functor.id_obj, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rfl

/-- Sliding the inverse comparison of a parity shift past a homogeneous map. -/
theorem ParityShiftDatum.inv_comp_map {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {S : C ⥤ C} {σ : ZMod 2} (P : ParityShiftDatum (k := k) S σ)
    {X Y : C} {q : ZMod 2} {g : X ⟶ Y} (hg : g ∈ parity (R := k) X Y q) :
    (P.iso X).inv ≫ S.map g = sign k (σ * q) • (g ≫ (P.iso Y).inv) := by
  rw [P.inv_naturality hg, smul_smul, sign_mul_self, one_smul]

/-- The source comparison of the shifted post/post mate: both parity removals. -/
def homShiftedPostSource (p q : ZMod 2) (Z : x ⟶ b) :
    (homParityShift (k := k) q).obj (((homParityShift (k := k) p).obj Z ≫ F₁) ≫ E₃) ⟶
      (Z ≫ F₁) ≫ E₃ :=
  ((homParityShiftDatum (k := k) q).iso _).hom ≫
    (((homParityShiftDatum (k := k) p).iso Z).hom ▷ F₁) ▷ E₃

/-- The target comparison of the shifted post/post mate: both parity insertions. -/
def homShiftedPostTarget (p q : ZMod 2) (Z : x ⟶ b) :
    (Z ≫ E₄) ≫ F₂ ⟶
      (homParityShift (k := k) p).obj ((homParityShift (k := k) q).obj (Z ≫ E₄)) ≫ F₂ :=
  ((homParityShiftDatum (k := k) q).iso (Z ≫ E₄)).inv ▷ F₂ ≫
    ((homParityShiftDatum (k := k) p).iso ((homParityShift (k := k) q).obj (Z ≫ E₄))).inv ▷ F₂

/-- The middle of the post/post mate: the crossing followed by the counit. -/
private def midPart (t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄) (Z : x ⟶ b) :
    ((Z ≫ F₁) ≫ E₃) ≫ E₂ ⟶ Z ≫ E₄ :=
  (associator (Z ≫ F₁) E₃ E₂).hom ≫ (Z ≫ F₁) ◁ t ≫
    (associator (Z ≫ F₁) E₁ E₄).inv ≫ (homPostCounit A₁).app Z ▷ E₄

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem midPart_mem {r : ZMod 2} {t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄}
    (ht : t ∈ parity (R := k) _ _ r) (Z : x ⟶ b) :
    midPart A₁ t Z ∈ parity (R := k) _ _ r := by
  have h := comp_mem (comp_mem (comp_mem
    (TwoSupercategory.associator_hom_mem (R := k) (Z ≫ F₁) E₃ E₂)
    (TwoSupercategory.whiskerLeft_mem (Z ≫ F₁) ht))
    (inv_mem (associator (Z ≫ F₁) E₁ E₄)
      (TwoSupercategory.associator_hom_mem (R := k) (Z ≫ F₁) E₁ E₄)))
    (TwoSupercategory.whiskerRight_mem E₄ (homPostCounit_mem (a := x) A₁ Z))
  simp only [zero_add, add_zero] at h
  simpa only [midPart, Category.assoc, Functor.id_obj] using h

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
theorem homPostCrossMate_eq_mid (t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄) (Z : x ⟶ b) :
    homPostCrossMate A₁ A₂ t Z =
      (homPostUnit A₂).app ((Z ≫ F₁) ≫ E₃) ≫ midPart A₁ t Z ▷ F₂ := rfl

/-- The counit of the shifted adjunction after the inverse removal, through the
unshifted counit. -/
private theorem inv_counit (p : ZMod 2) (Z : x ⟶ b) :
    ((homParityShiftDatum (k := k) p).iso
        (((homParityShift (k := k) p).obj Z ≫ F₁) ≫ E₁)).inv ≫
      (homShiftedPostAdjunction A₁ p).counit.app Z =
      sign k (p * p) • ((((homParityShiftDatum (k := k) p).iso Z).hom ▷ F₁) ▷ E₁ ≫
        (homPostCounit A₁).app Z) := by
  have hn := ((homPostCounit (a := x) A₁).naturality
    ((homParityShiftDatum (k := k) p).iso Z).hom).symm
  rw [homShiftedPostAdjunction_counit_app, Linear.comp_smul, Iso.inv_hom_id_assoc]
  exact congrArg _ hn

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- The super interchange law, read from right to left. -/
private theorem interchange_back {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} {p q : ZMod 2}
    {η : f ⟶ g} {θ : h ⟶ i} (hη : η ∈ parity (R := k) f g p)
    (hθ : θ ∈ parity (R := k) h i q) :
    f ◁ θ ≫ η ▷ i = sign k (p * q) • (η ▷ h ≫ g ◁ θ) := by
  rw [TwoSupercategory.super_interchange (R := k) hη hθ, koszulSign_smul (R := k), smul_smul,
    sign_mul_self, one_smul]

/-- The inner computation of the shifted post/post mate. -/
private theorem inner {r : ZMod 2} (p q : ZMod 2) {t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄}
    (ht : t ∈ parity (R := k) _ _ r) (Z : x ⟶ b) :
    ((homParityShiftDatum (k := k) p).iso ((homParityShift (k := k) q).obj
        (((homParityShift (k := k) p).obj Z ≫ F₁) ≫ E₃) ≫ E₂)).inv ≫
      homShiftedPostCrossing p q t ((homParityShift (k := k) p).obj Z ≫ F₁) ≫
        (homParityShift (k := k) q).map ((homShiftedPostAdjunction A₁ p).counit.app Z ▷ E₄) =
      sign k (p * p + p * r) • (homShiftedPostSource p q Z ▷ E₂ ≫ midPart A₁ t Z ≫
        ((homParityShiftDatum (k := k) q).iso (Z ≫ E₄)).inv) := by
  unfold homShiftedPostCrossing
  simp only [Category.assoc]
  set u := ((homParityShiftDatum (k := k) p).iso Z).hom ▷ F₁ with hu
  have huM : u ∈ parity (R := k) _ _ p :=
    TwoSupercategory.whiskerRight_mem F₁ ((homParityShiftDatum (k := k) p).hom_mem Z)
  have h1 := (homParityShiftDatum (k := k) (C := x ⟶ c) p).inv_comp_map (TwoSupercategory.whiskerRight_mem E₂
    ((homParityShiftDatum (k := k) (C := x ⟶ d) q).hom_mem
      (((homParityShift (k := k) p).obj Z ≫ F₁) ≫ E₃)))
  have h2 : ((homParityShiftDatum (k := k) (C := x ⟶ b) p).iso
      (((homParityShift (k := k) p).obj Z ≫ F₁) ≫ E₁)).inv ▷ E₄ ≫
      (homShiftedPostAdjunction A₁ p).counit.app Z ▷ E₄ =
      sign k (p * p) • ((u ▷ E₁) ▷ E₄ ≫ (homPostCounit A₁).app Z ▷ E₄) := by
    rw [← TwoSupercategory.comp_whiskerRight (R := k), inv_counit,
      TwoSupercategory.smul_whiskerRight (R := k), TwoSupercategory.comp_whiskerRight (R := k)]
  have h3 := (homParityShiftDatum (k := k) (C := x ⟶ c) q).inv_comp_map (TwoSupercategory.whiskerRight_mem E₄
    (TwoSupercategory.whiskerRight_mem E₁ huM))
  have h4 : ((homParityShiftDatum (k := k) (C := x ⟶ c) q).iso (((Z ≫ F₁) ≫ E₁) ≫ E₄)).inv ≫
      (homParityShift (k := k) q).map ((homPostCounit A₁).app Z ▷ E₄) =
      sign k (q * 0) • ((homPostCounit A₁).app Z ▷ E₄ ≫
        ((homParityShiftDatum (k := k) (C := x ⟶ c) q).iso (Z ≫ E₄)).inv) :=
    (homParityShiftDatum (k := k) (C := x ⟶ c) q).inv_comp_map
      (TwoSupercategory.whiskerRight_mem E₄ (homPostCounit_mem (a := x) A₁ Z))
  have h5 := interchange_back (k := k) huM ht
  rw [reassoc_of% h1, Linear.smul_comp, Category.assoc, Iso.inv_hom_id_assoc,
    ← Functor.map_comp, h2, Functor.map_smul, Functor.map_comp, Linear.comp_smul,
    reassoc_of% h3]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
  rw [h4]
  simp only [Linear.comp_smul]
  rw [← TwoSupercategory.associator_inv_naturality_left_assoc (R := k) u E₁ E₄,
    reassoc_of% h5]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
  rw [← TwoSupercategory.associator_naturality_left_assoc (R := k) u E₃ E₂]
  simp only [smul_smul, homShiftedPostSource, midPart, TwoSupercategory.comp_whiskerRight (R := k),
    Category.assoc]
  congr 1
  simp only [← sign_add]
  congr 1
  generalize p = p' at *
  generalize q = q' at *
  fin_cases p' <;> fin_cases q' <;> fin_cases r <;> rfl

private theorem source_mem (p q : ZMod 2) (Z : x ⟶ b) :
    homShiftedPostSource (k := k) (F₁ := F₁) (E₃ := E₃) p q Z ∈ parity (R := k) _ _ (q + p) :=
  comp_mem ((homParityShiftDatum (k := k) q).hom_mem _)
    (TwoSupercategory.whiskerRight_mem E₃ (TwoSupercategory.whiskerRight_mem F₁
      ((homParityShiftDatum (k := k) p).hom_mem Z)))

/-- **The shifted post/post mate (A8)**: conjugate to the unshifted post/post mate by the
source and target parity comparisons, with no residual sign. -/
theorem homShiftedPostCrossMate_eq {r : ZMod 2} (p q : ZMod 2) {t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄}
    (ht : t ∈ parity (R := k) _ _ r) (Z : x ⟶ b) :
    homShiftedPostCrossMate A₁ A₂ p q t Z =
      homShiftedPostSource p q Z ≫ homPostCrossMate A₁ A₂ t Z ≫
        homShiftedPostTarget p q Z := by
  have hK := comp_mem (comp_mem (TwoSupercategory.whiskerRight_mem E₂ (source_mem p q Z))
    (midPart_mem A₁ ht Z)) ((homParityShiftDatum (k := k) q).inv_mem (Z ≫ E₄))
  have hK' : homShiftedPostSource (k := k) p q Z ▷ E₂ ≫ midPart A₁ t Z ≫
      ((homParityShiftDatum (k := k) q).iso (Z ≫ E₄)).inv ∈ parity (R := k) _ _ (p + r) := by
    rw [← Category.assoc]
    convert hK using 2
    generalize p = p' at *
    generalize q = q' at *
    fin_cases p' <;> fin_cases q' <;> fin_cases r <;> rfl
  have hs := (homParityShiftDatum (k := k) (C := x ⟶ c) p).inv_comp_map hK'
  have hn := ((homPostUnit (a := x) A₂).naturality (homShiftedPostSource (k := k) (F₁ := F₁) (E₃ := E₃) p q Z)).symm
  unfold homShiftedPostCrossMate
  rw [homShiftedPostAdjunction_unit_app, homParityShiftSquare_inv_app_eq]
  change (_ ≫ _ ▷ F₂) ≫ (homParityShift (k := k) p).map (_ ≫
    (homParityShift (k := k) q).map ((homShiftedPostAdjunction A₁ p).counit.app Z ▷ E₄)) ▷ F₂ = _
  rw [Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k), Category.assoc, ← Functor.map_comp,
    inner A₁ p q ht Z, Functor.map_smul, Linear.comp_smul, hs, smul_smul, ← sign_add]
  have hsign : p * p + p * r + p * (p + r) = 0 := by
    generalize p = p' at *
    fin_cases p' <;> fin_cases r <;> rfl
  rw [hsign, sign_zero, one_smul]
  simp only [TwoSupercategory.comp_whiskerRight (R := k), homPostCrossMate_eq_mid,
    homShiftedPostTarget, Category.assoc]
  exact (reassoc_of% hn) _

/-- The shifted post/post mate is invertible whenever the factor mate is. -/
theorem homShiftedPostCrossMate_isIso_of {r : ZMod 2} (p q : ZMod 2) {t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄}
    (ht : t ∈ parity (R := k) _ _ r) [IsIso (crossMate A₁ A₂ t)] (Z : x ⟶ b) :
    IsIso (homShiftedPostCrossMate A₁ A₂ p q t Z) := by
  rw [homShiftedPostCrossMate_eq A₁ A₂ p q ht Z]
  have : IsIso (homPostCrossMate A₁ A₂ t Z) := homPostCrossMate_isIso_of A₁ A₂ Z
  have : IsIso ((((homParityShiftDatum (k := k) p).iso Z).hom ▷ F₁) ▷ E₃) :=
    (TwoSupercategory.whiskerRightIso (R := k)
      (TwoSupercategory.whiskerRightIso (R := k) ((homParityShiftDatum (k := k) p).iso Z) F₁)
      E₃).isIso_hom
  have : IsIso (((homParityShiftDatum (k := k) q).iso (Z ≫ E₄)).inv ▷ F₂) :=
    (TwoSupercategory.whiskerRightIso (R := k)
      ((homParityShiftDatum (k := k) q).iso (Z ≫ E₄)).symm F₂).isIso_hom
  have : IsIso (((homParityShiftDatum (k := k) p).iso
      ((homParityShift (k := k) q).obj (Z ≫ E₄))).inv ▷ F₂) :=
    (TwoSupercategory.whiskerRightIso (R := k) ((homParityShiftDatum (k := k) p).iso
      ((homParityShift (k := k) q).obj (Z ≫ E₄))).symm F₂).isIso_hom
  unfold homShiftedPostSource homShiftedPostTarget
  infer_instance

section Multicolour
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}

/-- For distinct colours of a `RouquierMulticolour`, the shifted post/post mate of the
factor crossing is invertible for all parity shifts, by `invNe`. -/
theorem homShiftedPostCrossMate_isIso (T : RouquierFamily (k := k) (B := B) D)
    {Sc : Scalars D k} (M : RouquierMulticolour T Sc) (i j : I) (hij : i ≠ j)
    {y ν c' d' : X} (h₁ : y + D.α j = d') (h₂ : d' + D.α i = c') (h₃ : y + D.α i = ν)
    (h₄ : ν + D.α j = c') (p q : ZMod 2) {z : B} (Z : z ⟶ T.obj ν) :
    IsIso (homShiftedPostCrossMate (T.adj i h₃) (T.adj i h₂) p q
      (T.cross i j h₁ h₂ h₃ h₄) Z) := by
  have := M.invNe i j hij h₁ h₂ h₃ h₄
  exact homShiftedPostCrossMate_isIso_of _ _ p q (T.cross_mem i j h₁ h₂ h₃ h₄) Z

end Multicolour

end OddMath.SKM
