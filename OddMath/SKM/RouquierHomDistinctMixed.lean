import OddMath.SKM.RouquierHomMixedInterchange
import OddMath.SKM.RouquierHomPostCoordinates

/-!
# The distinct-colour mixed mate `U` of the swapped Hom action

Formalizes `docs/Nondegeneracy/SwappedDistinctMixedMates.md` (1), (7), (8)
and the `U` half of (15), i.e. the `U_ji` entry of
`SwappedActionAssembly.md` (A13). Precomposition by a pre edge `E` is fixed;
postcomposition uses an arbitrary even right adjunction `E' ⊣ F'`, shifted
by `κ` on the source side and by `τ` on the target side. The prescribed
comparison `J` is `homMixedInterchange E E' κ τ`, of parity `κ + τ`.

The mate of `J⁻¹` with respect to the two shifted post adjunctions is the
literal unit–`J⁻¹`–counit word (`homDistinctMixedMate`). Its coordinate
formula (8) is `homDistinctMixedMate_eq`: up to the sign `(-1)^(κ(κ+τ))` it is
the even associator between the two shift removals. Hence it has the
explicit two-sided inverse (15) (`homDistinctMixedMateInv`).
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Generic
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B}

/-- The shifted postcomposition adjunction, shift on the input of the right adjoint.
For a content-shifted reservoir edge this is `homContentPostAdjunction`. -/
def homShiftPostAdjunction {E' : c ⟶ d} {F' : d ⟶ c}
    (A : SuperAdjunction (k := k) E' F') (x : B) (κ : ZMod 2) :
    homPost (k := k) (a := x) E' ⋙ homParityShift (k := k) κ ⊣
      homParityShift (k := k) κ ⋙ homPost (k := k) F' :=
  (homPostAdjunction (a := x) A).comp (homParityShiftAdjunction κ)

theorem homShiftPostAdjunction_unit_app {E' : c ⟶ d} {F' : d ⟶ c}
    (A : SuperAdjunction (k := k) E' F') {x : B} (κ : ZMod 2) (X : x ⟶ c) :
    (homShiftPostAdjunction A x κ).unit.app X =
      (homPostUnit A).app X ≫
        (homParityShiftSquare (k := k) κ).inv.app (X ≫ E') ▷ F' := by
  change ((homPostAdjunction A).comp (homParityShiftAdjunction κ)).unit.app X = _
  rw [Adjunction.comp_unit_app, homParityShiftAdjunction_unit_app]
  rfl

theorem homShiftPostAdjunction_counit_app {E' : c ⟶ d} {F' : d ⟶ c}
    (A : SuperAdjunction (k := k) E' F') {x : B} (κ : ZMod 2) (H : x ⟶ d) :
    (homShiftPostAdjunction A x κ).counit.app H =
      (homShiftConjugationIso (homPost (k := k) F' ⋙ homPost (k := k) E') κ H).hom ≫
        (homPostCounit A).app H := by
  change ((homPostAdjunction A).comp (homParityShiftAdjunction κ)).counit.app H = _
  rw [Adjunction.comp_counit_app, homParityShiftAdjunction_counit_app]
  have hc := homShiftConjugationIso_supernatural
    (homPost (k := k) (a := x) F' ⋙ homPost (k := k) E')
    (𝟭 _) κ 0 (homPostCounit A).app
    (isSupernatural_of_natTrans (homPostCounit A) (homPostCounit_mem A)) H
  rw [homShiftConjugationIso_id] at hc
  exact hc

theorem homShiftPostAdjunction_counit_mem {E' : c ⟶ d} {F' : d ⟶ c}
    (A : SuperAdjunction (k := k) E' F') {x : B} (κ : ZMod 2) (H : x ⟶ d) :
    (homShiftPostAdjunction A x κ).counit.app H ∈ parity (R := k) _ _ 0 := by
  rw [homShiftPostAdjunction_counit_app]
  have h := comp_mem
    (homShiftConjugationIso_mem (homPost (k := k) F' ⋙ homPost (k := k) E') κ H)
    (homPostCounit_mem A H)
  rw [add_zero] at h
  exact h

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Precomposition by `E` of the post counit, through the associator, is the post
counit at `E ≫ H` after reassociation. Even bicategorical coherence. -/
private theorem pre_postCounit {E' : c ⟶ d} {F' : d ⟶ c}
    (A : SuperAdjunction (k := k) E' F') (E : a ⟶ b) (H : b ⟶ d) :
    (associator E (H ≫ F') E').hom ≫ E ◁ (homPostCounit A).app H =
      (associator E H F').inv ▷ E' ≫ (homPostCounit A).app (E ≫ H) := by
  let η : (Underlying2.hom1 (R := k) F' ≫ Underlying2.hom1 (R := k) E') ⟶ 𝟙 _ :=
    ⟨A.counit, A.counit_mem⟩
  have hb : (Bicategory.associator (Underlying2.hom1 (R := k) E)
        (Underlying2.hom1 (R := k) H ≫ Underlying2.hom1 (R := k) F')
        (Underlying2.hom1 (R := k) E')).hom ≫
      Bicategory.whiskerLeft (Underlying2.hom1 (R := k) E)
        ((Bicategory.associator (Underlying2.hom1 (R := k) H)
          (Underlying2.hom1 (R := k) F') (Underlying2.hom1 (R := k) E')).hom ≫
          Bicategory.whiskerLeft (Underlying2.hom1 (R := k) H) η ≫
          (Bicategory.rightUnitor (Underlying2.hom1 (R := k) H)).hom) =
      Bicategory.whiskerRight (Bicategory.associator (Underlying2.hom1 (R := k) E)
          (Underlying2.hom1 (R := k) H) (Underlying2.hom1 (R := k) F')).inv
          (Underlying2.hom1 (R := k) E') ≫
        (Bicategory.associator (Underlying2.hom1 (R := k) E ≫ Underlying2.hom1 (R := k) H)
          (Underlying2.hom1 (R := k) F') (Underlying2.hom1 (R := k) E')).hom ≫
        Bicategory.whiskerLeft (Underlying2.hom1 (R := k) E ≫ Underlying2.hom1 (R := k) H) η ≫
        (Bicategory.rightUnitor
          (Underlying2.hom1 (R := k) E ≫ Underlying2.hom1 (R := k) H)).hom := by
    bicategory
  have hv := congrArg Subtype.val hb
  dsimp [homPostCounit, homPostComp, homPostId, homPostTransform,
    SuperNatTrans.toNatTrans]
  exact hv

variable (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2)

/-- The mate `U = M(J⁻¹)` of (7): the target unit, `J⁻¹`, and the pre-whiskered
source counit, each with its own shift. -/
def homDistinctMixedMate (H : b ⟶ d) :
    E ≫ ((homParityShift (k := k) κ).obj H ≫ F') ⟶
      (homParityShift (k := k) τ).obj (E ≫ H) ≫ F' :=
  (homShiftPostAdjunction A a τ).unit.app (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫
    (homParityShift (k := k) τ).map
      ((homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv ≫
        E ◁ (homShiftPostAdjunction A b κ).counit.app H) ▷ F'

/-- The coordinate formula (8), solved for `U`: the two endpoint shift removals
around the even associator, with the residual sign `(-1)^(κ(κ+τ))`. -/
theorem homDistinctMixedMate_eq (H : b ⟶ d) :
    homDistinctMixedMate E A κ τ H = sign k (κ * (κ + τ)) •
      (E ◁ (((homParityShiftDatum (k := k) κ).iso H).hom ▷ F') ≫
        (associator E H F').inv ≫
        ((homParityShiftDatum (k := k) τ).iso (E ≫ H)).inv ▷ F') := by
  set S := homParityShift (k := k) (C := b ⟶ d) κ
  set Y := S.obj H ≫ F' with hY
  set Q := (E ≫ Y) ≫ E' with hQ
  set δτ := (homParityShiftDatum (k := k) (C := a ⟶ d) τ)
  set δκ := (homParityShiftDatum (k := k) (C := b ⟶ d) κ)
  -- the counit word, after removing the source shift of `J⁻¹`
  have hε : (δκ.iso (Y ≫ E')).inv ≫ (homShiftPostAdjunction A b κ).counit.app H =
      sign k (κ * κ) • ((δκ.iso H).hom ▷ F' ▷ E' ≫ (homPostCounit A).app H) := by
    rw [homShiftPostAdjunction_counit_app, homShiftConjugationIso_hom_signed,
      Linear.smul_comp, Linear.comp_smul, Category.assoc]
    congr 1
    exact Iso.inv_hom_id_assoc _ _
  set f : Q ⟶ E ≫ H := (associator E Y E').hom ≫ E ◁ (δκ.iso (Y ≫ E')).inv ≫
      E ◁ (homShiftPostAdjunction A b κ).counit.app H with hf
  have hfm : f ∈ parity (R := k) _ _ κ := by
    have := comp_mem (TwoSupercategory.associator_hom_mem (R := k) E Y E')
      (comp_mem (TwoSupercategory.whiskerLeft_mem E (δκ.inv_mem (Y ≫ E')))
        (TwoSupercategory.whiskerLeft_mem E
          (homShiftPostAdjunction_counit_mem A κ H)))
    rw [zero_add, add_zero] at this
    exact this
  have hJ : (homMixedInterchange (k := k) E E' κ τ Y).inv ≫
      E ◁ (homShiftPostAdjunction A b κ).counit.app H = (δτ.iso Q).hom ≫ f := by
    simp [homMixedInterchange, hf, homPre, δτ, δκ, Category.assoc]
    rfl
  have hf' : f = sign k (κ * κ) • ((E ◁ ((δκ.iso H).hom ▷ F')) ▷ E' ≫
      (associator E (H ≫ F') E').hom ≫ E ◁ (homPostCounit A).app H) := by
    rw [hf, ← TwoSupercategory.whiskerLeft_comp (R := k), hε,
      TwoSupercategory.whiskerLeft_smul, TwoSupercategory.whiskerLeft_comp (R := k),
      Linear.comp_smul, ← Category.assoc,
      ← TwoSupercategory.associator_naturality_middle (R := k), Category.assoc]
  -- the square inverse cancels the shifted target removal
  have hsq : (homParityShiftSquare (k := k) τ).inv.app Q ≫
      (homParityShift (k := k) τ).map (δτ.iso Q).hom = (δτ.iso Q).inv := by
    have h0 := homParityShiftSquare_hom_app_map (k := k) τ Q
    have h1 : (homParityShift (k := k) τ).map (δτ.iso Q).hom =
        (homParityShiftSquare (k := k) τ).hom.app Q ≫ (δτ.iso Q).inv := by
      rw [h0]; simp [δτ]
    rw [h1, Iso.inv_hom_id_app_assoc]
  have hnat : (δτ.iso Q).inv ≫ (homParityShift (k := k) τ).map f =
      sign k (τ * κ) • (f ≫ (δτ.iso (E ≫ H)).inv) := by
    rw [δτ.inv_naturality hfm, smul_smul, sign_mul_self, one_smul]
  -- the remaining word is the post right triangle, after pre coherence
  have htri : (homPostUnit A).app (E ≫ (H ≫ F')) ≫
      (associator E (H ≫ F') E').hom ▷ F' ≫ (E ◁ (homPostCounit A).app H) ▷ F' =
      (associator E H F').inv := by
    rw [← TwoSupercategory.comp_whiskerRight (R := k), pre_postCounit,
      TwoSupercategory.comp_whiskerRight (R := k)]
    have hn := (homPostUnit (a := a) A).naturality (associator E H F').inv
    simp only [Functor.id_map, Functor.comp_map] at hn
    change _ ≫ ((homPost (k := k) F').map ((homPost (k := k) E').map
      (associator E H F').inv)) ≫ (homPost (k := k) F').map ((homPostCounit A).app (E ≫ H)) = _
    rw [← Category.assoc, ← hn, Category.assoc]
    have ht := (homPostAdjunction (a := a) A).right_triangle_components (E ≫ H)
    change _ ≫ (homPostUnit A).app ((E ≫ H) ≫ F') ≫
      (homPost (k := k) F').map ((homPostCounit A).app (E ≫ H)) = _
    rw [show (homPostUnit A).app ((E ≫ H) ≫ F') ≫
      (homPost (k := k) F').map ((homPostCounit A).app (E ≫ H)) = 𝟙 _ from ht,
      Category.comp_id]
  unfold homDistinctMixedMate
  rw [homShiftPostAdjunction_unit_app, hJ, Functor.map_comp,
    TwoSupercategory.comp_whiskerRight (R := k), Category.assoc,
    ← Category.assoc ((homParityShiftSquare (k := k) τ).inv.app _ ▷ F'),
    ← TwoSupercategory.comp_whiskerRight (R := k), hsq,
    ← TwoSupercategory.comp_whiskerRight (R := k), hnat, hf']
  simp only [TwoSupercategory.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul, smul_smul]
  congr 1
  · rw [← sign_add]; congr 1; ring
  simp only [TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]
  have hn := (homPostUnit (a := a) A).naturality (E ◁ ((δκ.iso H).hom ▷ F'))
  simp only [Functor.id_map, Functor.comp_map] at hn
  change (homPostUnit A).app _ ≫ (homPost (k := k) F').map ((homPost (k := k) E').map
      (E ◁ ((δκ.iso H).hom ▷ F'))) ≫ _ = _
  rw [← Category.assoc, ← hn, Category.assoc]
  congr 1
  rw [reassoc_of% htri]

/-- The explicit inverse (15): `β C_t ; h_B⁻¹ ; C_s⁻¹`. -/
def homDistinctMixedMateInv (H : b ⟶ d) :
    (homParityShift (k := k) τ).obj (E ≫ H) ≫ F' ⟶
      E ≫ ((homParityShift (k := k) κ).obj H ≫ F') :=
  sign k (κ * (κ + τ)) •
    (((homParityShiftDatum (k := k) τ).iso (E ≫ H)).hom ▷ F' ≫
      (associator E H F').hom ≫
      E ◁ (((homParityShiftDatum (k := k) κ).iso H).inv ▷ F'))

/-- Both inverse products of (15) are adjacent cancellations; the scalar is a square. -/
theorem homDistinctMixedMate_inv_products (H : b ⟶ d) :
    homDistinctMixedMate E A κ τ H ≫ homDistinctMixedMateInv E κ τ H = 𝟙 _ ∧
    homDistinctMixedMateInv E κ τ H ≫ homDistinctMixedMate E A κ τ H = 𝟙 _ := by
  rw [homDistinctMixedMate_eq, homDistinctMixedMateInv]
  have h1 : ((homParityShiftDatum (k := k) τ).iso (E ≫ H)).inv ▷ F' ≫
      ((homParityShiftDatum (k := k) τ).iso (E ≫ H)).hom ▷ F' = 𝟙 _ := by
    rw [← TwoSupercategory.comp_whiskerRight (R := k), Iso.inv_hom_id,
      TwoSupercategory.id_whiskerRight (R := k)]
  have h2 : ((homParityShiftDatum (k := k) τ).iso (E ≫ H)).hom ▷ F' ≫
      ((homParityShiftDatum (k := k) τ).iso (E ≫ H)).inv ▷ F' = 𝟙 _ := by
    rw [← TwoSupercategory.comp_whiskerRight (R := k), Iso.hom_inv_id,
      TwoSupercategory.id_whiskerRight (R := k)]
  have h3 : E ◁ (((homParityShiftDatum (k := k) κ).iso H).inv ▷ F') ≫
      E ◁ (((homParityShiftDatum (k := k) κ).iso H).hom ▷ F') = 𝟙 _ := by
    rw [← TwoSupercategory.whiskerLeft_comp (R := k), ← TwoSupercategory.comp_whiskerRight (R := k),
      Iso.inv_hom_id, TwoSupercategory.id_whiskerRight (R := k),
      TwoSupercategory.whiskerLeft_id (R := k)]
  have h4 : E ◁ (((homParityShiftDatum (k := k) κ).iso H).hom ▷ F') ≫
      E ◁ (((homParityShiftDatum (k := k) κ).iso H).inv ▷ F') = 𝟙 _ := by
    rw [← TwoSupercategory.whiskerLeft_comp (R := k), ← TwoSupercategory.comp_whiskerRight (R := k),
      Iso.hom_inv_id, TwoSupercategory.id_whiskerRight (R := k),
      TwoSupercategory.whiskerLeft_id (R := k)]
  constructor
  · rw [Linear.smul_comp, Linear.comp_smul, smul_smul, sign_mul_self, one_smul]
    simp only [Category.assoc]
    rw [reassoc_of% h1, Iso.inv_hom_id_assoc, h4]
  · rw [Linear.smul_comp, Linear.comp_smul, smul_smul, sign_mul_self, one_smul]
    simp only [Category.assoc]
    rw [reassoc_of% h3, Iso.hom_inv_id_assoc, h2]

instance homDistinctMixedMate_isIso (H : b ⟶ d) : IsIso (homDistinctMixedMate E A κ τ H) :=
  ⟨⟨homDistinctMixedMateInv E κ τ H, homDistinctMixedMate_inv_products E A κ τ H⟩⟩

/-- `U` has the crossing parity `κ + τ`. -/
theorem homDistinctMixedMate_mem (H : b ⟶ d) :
    homDistinctMixedMate E A κ τ H ∈ parity (R := k) _ _ (κ + τ) := by
  rw [homDistinctMixedMate_eq]
  apply Submodule.smul_mem
  have := comp_mem (TwoSupercategory.whiskerLeft_mem E
      (TwoSupercategory.whiskerRight_mem F' ((homParityShiftDatum (k := k) κ).hom_mem H)))
    (comp_mem (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E H F'))
      (TwoSupercategory.whiskerRight_mem F'
        ((homParityShiftDatum (k := k) τ).inv_mem (E ≫ H))))
  simpa only [zero_add] using this

end Generic
end OddMath.SKM
