import OddMath.SKM.RouquierHomContentCoherence

/-!
# Shifted left adjunctions and raising precomposition

This ports the reverse-adjunction input of `Categorification/TwoRep/RouqReverse.lean`
(there `RouqFamily.adjL`, from `RouqModel.lean`) to the super setting, in the form
used by the content-shifted Hom family of `RouquierHomContent.lean`. Its downstream
consumer is the raising/lowering precomposition pair of that Hom family.

In a 2-supercategory the leftward cup and cap of a colour `i` at weight `λ` have
parity `|i|(⟨hᵢ, λ⟩ + 1)`, which may be odd. `ShiftedSuperAdjunction F E σ` records a
left adjunction `F ⊣ E` whose unit and counit have parity `σ`. With odd unit and counit
the two zigzags cannot both be the identity in general: the convention here is that the
zigzag on `F` is the identity and the zigzag on `E` is `(-1)^σ`. This is precisely the
convention for which the transported Hom-sector triangles below are exact.

`homPreShiftAdjunction` proves that precomposition by `E`, followed by any parity-`σ`
shift of the target Hom supercategory, is left adjoint to precomposition by `F`, on the
full Hom supercategories (odd 2-morphisms included). For `σ = 0` this is the reversal
of the even precomposition adjunction.

The construction of the shifted left adjunction from Rouquier's local inverses (the
super analogue of Brundan's Theorem 4.3, `RouqLoc.leftAdjunction`) is not proved here.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

theorem zmod2_add_self (s : ZMod 2) : s + s = 0 := by
  fin_cases s <;> rfl

section ShiftDatum
variable {k : Type r} [CommRing k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [Supercategory k C]

/-- A parity-`σ` shift functor with a supernatural comparison to the identity. -/
structure ParityShiftDatum (S : C ⥤ C) (σ : ZMod 2) where
  /-- The comparison isomorphisms, of parity `σ`. -/
  iso : ∀ X : C, S.obj X ≅ X
  /-- Signed naturality of the comparison. -/
  supernatural : IsSupernatural k σ (F := S) (G := 𝟭 C) fun X => (iso X).hom

namespace ParityShiftDatum
variable {S : C ⥤ C} {σ : ZMod 2} (P : ParityShiftDatum (k := k) S σ)

theorem hom_mem (X : C) : (P.iso X).hom ∈ parity (R := k) _ _ σ := P.supernatural.mem X

theorem inv_mem (X : C) : (P.iso X).inv ∈ parity (R := k) _ _ σ :=
  Supercategory.inv_mem _ (P.hom_mem X)

theorem hom_naturality {X Y : C} {q : ZMod 2} {g : X ⟶ Y}
    (hg : g ∈ parity (R := k) X Y q) :
    S.map g ≫ (P.iso Y).hom = sign k (σ * q) • ((P.iso X).hom ≫ g) :=
  P.supernatural.naturality hg

theorem inv_naturality {X Y : C} {q : ZMod 2} {g : X ⟶ Y}
    (hg : g ∈ parity (R := k) X Y q) :
    g ≫ (P.iso Y).inv = sign k (σ * q) • ((P.iso X).inv ≫ S.map g) := by
  have h2 : (P.iso X).inv ≫ S.map g = sign k (σ * q) • (g ≫ (P.iso Y).inv) := by
    rw [← cancel_mono (P.iso Y).hom, Category.assoc, P.hom_naturality hg,
      Linear.comp_smul, Iso.inv_hom_id_assoc, Linear.smul_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [h2, smul_smul, sign_mul_self, one_smul]

/-- Even maps commute with the comparison. -/
theorem hom_naturality_even {X Y : C} {g : X ⟶ Y} (hg : g ∈ parity (R := k) X Y 0) :
    S.map g ≫ (P.iso Y).hom = (P.iso X).hom ≫ g := by
  rw [P.hom_naturality hg, mul_zero, sign_zero, one_smul]

/-- The trivial shift. -/
def id : ParityShiftDatum (k := k) (𝟭 C) 0 where
  iso X := Iso.refl X
  supernatural := isSupernatural_id

/-- The Π shift, with `ζ` as comparison. -/
def pi [PiSupercategory k C] :
    ParityShiftDatum (k := k) (PiSupercategory.pi (R := k) (C := C)) 1 where
  iso := PiSupercategory.ζ
  supernatural := PiSupercategory.ζ_isSupernatural

end ParityShiftDatum

/-- The parity shift used by the content-shifted Hom family carries its comparison. -/
def homParityShiftDatum [PiSupercategory k C] (p : ZMod 2) :
    ParityShiftDatum (k := k) (homParityShift (k := k) (C := C) p) p := by
  unfold homParityShift
  split_ifs with h
  · subst h
    exact ParityShiftDatum.id
  · have h1 : p = 1 := by
      fin_cases p
      · exact absurd rfl h
      · rfl
    subst h1
    exact ParityShiftDatum.pi

end ShiftDatum

section Adjunction
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- A left adjunction `F ⊣ E` whose unit and counit have parity `σ`. The zigzag on `F`
is the identity and the zigzag on `E` is `(-1)^σ`. -/
structure ShiftedSuperAdjunction {a b : B} (F : b ⟶ a) (E : a ⟶ b) (σ : ZMod 2) where
  unit : 𝟙 b ⟶ F ≫ E
  counit : E ≫ F ⟶ 𝟙 a
  unit_mem : unit ∈ parity (R := k) _ _ σ
  counit_mem : counit ∈ parity (R := k) _ _ σ
  left_triangle : (leftUnitor F).inv ≫ unit ▷ F ≫ (associator F E F).hom ≫
    F ◁ counit ≫ (rightUnitor F).hom = 𝟙 F
  right_triangle : (rightUnitor E).inv ≫ E ◁ unit ≫ (associator E F E).inv ≫
    counit ▷ E ≫ (leftUnitor E).hom = koszulSign σ σ • 𝟙 E

/-- An even adjunction is a shifted adjunction with `σ = 0`. -/
def ShiftedSuperAdjunction.ofSuperAdjunction {a b : B} {F : b ⟶ a} {E : a ⟶ b}
    (A : SuperAdjunction (k := k) F E) : ShiftedSuperAdjunction (k := k) F E 0 where
  unit := A.unit
  counit := A.counit
  unit_mem := A.unit_mem
  counit_mem := A.counit_mem
  left_triangle := A.left_triangle
  right_triangle := by rw [A.right_triangle, koszulSign_zero_left, one_smul]

section Coherence
variable {a b c : B}
include k

private theorem coh_rho_assoc (E : a ⟶ b) (X : b ⟶ c) :
    (rightUnitor E).inv ▷ X ≫ (associator E (𝟙 b) X).hom = E ◁ (leftUnitor X).inv := by
  have h : Bicategory.whiskerRight (Bicategory.rightUnitor (Underlying2.hom1 (R := k) E)).inv
      (Underlying2.hom1 (R := k) X) ≫
      (Bicategory.associator (Underlying2.hom1 (R := k) E) (𝟙 _)
        (Underlying2.hom1 (R := k) X)).hom =
      Bicategory.whiskerLeft (Underlying2.hom1 (R := k) E)
        (Bicategory.leftUnitor (Underlying2.hom1 (R := k) X)).inv := by
    bicategory
  exact congrArg Subtype.val h

private theorem coh_assoc_mid {d e : B} (E : a ⟶ b) (F : b ⟶ e) (E' : e ⟶ d) (X : d ⟶ c) :
    (associator E (F ≫ E') X).inv ≫ (associator E F E').inv ▷ X ≫
      (associator (E ≫ F) E' X).hom =
    E ◁ (associator F E' X).hom ≫ (associator E F (E' ≫ X)).inv := by
  have h : (Bicategory.associator (Underlying2.hom1 (R := k) E)
        (Underlying2.hom1 (R := k) F ≫ Underlying2.hom1 (R := k) E')
        (Underlying2.hom1 (R := k) X)).inv ≫
      Bicategory.whiskerRight (Bicategory.associator (Underlying2.hom1 (R := k) E)
        (Underlying2.hom1 (R := k) F) (Underlying2.hom1 (R := k) E')).inv
        (Underlying2.hom1 (R := k) X) ≫
      (Bicategory.associator (Underlying2.hom1 (R := k) E ≫ Underlying2.hom1 (R := k) F)
        (Underlying2.hom1 (R := k) E') (Underlying2.hom1 (R := k) X)).hom =
      Bicategory.whiskerLeft (Underlying2.hom1 (R := k) E)
        (Bicategory.associator (Underlying2.hom1 (R := k) F)
          (Underlying2.hom1 (R := k) E') (Underlying2.hom1 (R := k) X)).hom ≫
      (Bicategory.associator (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) F)
        (Underlying2.hom1 (R := k) E' ≫ Underlying2.hom1 (R := k) X)).inv := by
    bicategory
  exact congrArg Subtype.val h

private theorem coh_lambda_assoc (E : a ⟶ b) (X : b ⟶ c) :
    (associator (𝟙 a) E X).inv ≫ (leftUnitor E).hom ▷ X = (leftUnitor (E ≫ X)).hom := by
  have h : (Bicategory.associator (𝟙 _) (Underlying2.hom1 (R := k) E)
        (Underlying2.hom1 (R := k) X)).inv ≫
      Bicategory.whiskerRight (Bicategory.leftUnitor (Underlying2.hom1 (R := k) E)).hom
        (Underlying2.hom1 (R := k) X) =
      (Bicategory.leftUnitor (Underlying2.hom1 (R := k) E ≫
        Underlying2.hom1 (R := k) X)).hom := by
    bicategory
  exact congrArg Subtype.val h

private theorem coh_lambda_inv_assoc (F : b ⟶ a) (Y : a ⟶ c) :
    (leftUnitor F).inv ▷ Y ≫ (associator (𝟙 b) F Y).hom = (leftUnitor (F ≫ Y)).inv := by
  have h : Bicategory.whiskerRight (Bicategory.leftUnitor (Underlying2.hom1 (R := k) F)).inv
        (Underlying2.hom1 (R := k) Y) ≫
      (Bicategory.associator (𝟙 _) (Underlying2.hom1 (R := k) F)
        (Underlying2.hom1 (R := k) Y)).hom =
      (Bicategory.leftUnitor (Underlying2.hom1 (R := k) F ≫
        Underlying2.hom1 (R := k) Y)).inv := by
    bicategory
  exact congrArg Subtype.val h

private theorem coh_assoc_mid' {d e : B} (F : b ⟶ a) (E : a ⟶ d) (F' : d ⟶ e) (Y : e ⟶ c) :
    (associator (F ≫ E) F' Y).inv ≫ (associator F E F').hom ▷ Y ≫
      (associator F (E ≫ F') Y).hom =
    (associator F E (F' ≫ Y)).hom ≫ F ◁ (associator E F' Y).inv := by
  have h : (Bicategory.associator
        (Underlying2.hom1 (R := k) F ≫ Underlying2.hom1 (R := k) E)
        (Underlying2.hom1 (R := k) F') (Underlying2.hom1 (R := k) Y)).inv ≫
      Bicategory.whiskerRight (Bicategory.associator (Underlying2.hom1 (R := k) F)
        (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) F')).hom
        (Underlying2.hom1 (R := k) Y) ≫
      (Bicategory.associator (Underlying2.hom1 (R := k) F)
        (Underlying2.hom1 (R := k) E ≫ Underlying2.hom1 (R := k) F')
        (Underlying2.hom1 (R := k) Y)).hom =
      (Bicategory.associator (Underlying2.hom1 (R := k) F) (Underlying2.hom1 (R := k) E)
        (Underlying2.hom1 (R := k) F' ≫ Underlying2.hom1 (R := k) Y)).hom ≫
      Bicategory.whiskerLeft (Underlying2.hom1 (R := k) F)
        (Bicategory.associator (Underlying2.hom1 (R := k) E)
          (Underlying2.hom1 (R := k) F') (Underlying2.hom1 (R := k) Y)).inv := by
    bicategory
  exact congrArg Subtype.val h

private theorem coh_rho_assoc' (F : b ⟶ a) (Y : a ⟶ c) :
    (associator F (𝟙 a) Y).hom ≫ F ◁ (leftUnitor Y).hom = (rightUnitor F).hom ▷ Y :=
  TwoSupercategory.triangle (R := k) F Y

end Coherence

variable {a b c : B} {F : b ⟶ a} {E : a ⟶ b} {σ : ZMod 2}
  (A : ShiftedSuperAdjunction (k := k) F E σ)

/-- The zigzag on `E`, whiskered by a Hom-sector object. -/
theorem ShiftedSuperAdjunction.right_triangle_whiskerRight (X : b ⟶ c) :
    E ◁ (leftUnitor X).inv ≫ E ◁ (A.unit ▷ X) ≫ E ◁ (associator F E X).hom ≫
      (associator E F (E ≫ X)).inv ≫ A.counit ▷ (E ≫ X) ≫ (leftUnitor (E ≫ X)).hom =
    koszulSign σ σ • 𝟙 (E ≫ X) := by
  have h := congrArg (fun t => t ▷ X) A.right_triangle
  simp only [TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.zsmul_whiskerRight (R := k),
    TwoSupercategory.id_whiskerRight (R := k)] at h
  rw [← h]
  rw [← coh_rho_assoc (k := k), ← coh_lambda_assoc (k := k)]
  have hm : E ◁ (A.unit ▷ X) =
      (associator E (𝟙 b) X).inv ≫ (E ◁ A.unit) ▷ X ≫ (associator E (F ≫ E) X).hom := by
    rw [TwoSupercategory.whisker_assoc (R := k)]
    simp
  have hc : A.counit ▷ (E ≫ X) =
      (associator (E ≫ F) E X).inv ≫ (A.counit ▷ E) ▷ X ≫ (associator (𝟙 a) E X).hom := by
    rw [TwoSupercategory.whiskerRight_comp (R := k)]
  rw [hm, hc]
  have hmid := coh_assoc_mid (k := k) E F E X
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% hmid]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]

/-- The zigzag on `F`, whiskered by a Hom-sector object. -/
theorem ShiftedSuperAdjunction.left_triangle_whiskerRight (Y : a ⟶ c) :
    (leftUnitor (F ≫ Y)).inv ≫ A.unit ▷ (F ≫ Y) ≫ (associator F E (F ≫ Y)).hom ≫
      F ◁ (associator E F Y).inv ≫ F ◁ (A.counit ▷ Y) ≫ F ◁ (leftUnitor Y).hom =
    𝟙 (F ≫ Y) := by
  have h := congrArg (fun t => t ▷ Y) A.left_triangle
  simp only [TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.id_whiskerRight (R := k)] at h
  rw [← h]
  rw [← coh_lambda_inv_assoc (k := k), ← coh_rho_assoc' (k := k)]
  have hu : A.unit ▷ (F ≫ Y) =
      (associator (𝟙 b) F Y).inv ≫ (A.unit ▷ F) ▷ Y ≫ (associator (F ≫ E) F Y).hom := by
    rw [TwoSupercategory.whiskerRight_comp (R := k)]
  have hm : F ◁ (A.counit ▷ Y) =
      (associator F (E ≫ F) Y).inv ≫ (F ◁ A.counit) ▷ Y ≫ (associator F (𝟙 a) Y).hom := by
    rw [TwoSupercategory.whisker_assoc (R := k)]
    simp
  rw [hu, hm]
  have hmid := coh_assoc_mid' (k := k) F E F Y
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% hmid]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]

variable {S : (a ⟶ c) ⥤ (a ⟶ c)} [S.Additive] [S.Linear k] [IsSuperfunctor k S]
  (P : ParityShiftDatum (k := k) S σ)

/-- Unit components of the shifted precomposition adjunction. -/
def homPreShiftUnitApp (X : b ⟶ c) : X ⟶ F ≫ S.obj (E ≫ X) :=
  (leftUnitor X).inv ≫ A.unit ▷ X ≫ (associator F E X).hom ≫ F ◁ (P.iso (E ≫ X)).inv

/-- Counit components of the shifted precomposition adjunction. -/
def homPreShiftCounitApp (Y : a ⟶ c) : S.obj (E ≫ (F ≫ Y)) ⟶ Y :=
  (P.iso (E ≫ F ≫ Y)).hom ≫ (associator E F Y).inv ≫ A.counit ▷ Y ≫ (leftUnitor Y).hom

omit [S.Additive] [S.Linear k] [IsSuperfunctor k S] in
theorem homPreShiftUnitApp_mem (X : b ⟶ c) :
    homPreShiftUnitApp A P X ∈ parity (R := k) _ _ 0 := by
  have h := comp_mem (comp_mem (comp_mem
    (inv_mem (leftUnitor X) (TwoSupercategory.leftUnitor_hom_mem (R := k) X))
    (TwoSupercategory.whiskerRight_mem X A.unit_mem))
    (TwoSupercategory.associator_hom_mem (R := k) F E X))
    (TwoSupercategory.whiskerLeft_mem F (P.inv_mem (E ≫ X)))
  rw [zero_add, add_zero, zmod2_add_self] at h
  unfold homPreShiftUnitApp
  simpa only [Category.assoc] using h

omit [S.Additive] [S.Linear k] [IsSuperfunctor k S] in
theorem homPreShiftCounitApp_mem (Y : a ⟶ c) :
    homPreShiftCounitApp A P Y ∈ parity (R := k) _ _ 0 := by
  have h := comp_mem (comp_mem (comp_mem (P.hom_mem (E ≫ F ≫ Y))
    (inv_mem (associator E F Y) (TwoSupercategory.associator_hom_mem (R := k) E F Y)))
    (TwoSupercategory.whiskerRight_mem Y A.counit_mem))
    (TwoSupercategory.leftUnitor_hom_mem (R := k) Y)
  rw [add_zero, add_zero, zmod2_add_self] at h
  unfold homPreShiftCounitApp
  simpa only [Category.assoc] using h

omit [S.Additive] [S.Linear k] [IsSuperfunctor k S] in
theorem homPreShiftUnit_supernatural :
    IsSupernatural k 0 (F := 𝟭 (b ⟶ c)) (G := (homPre (k := k) E ⋙ S) ⋙ homPre (k := k) F)
      (homPreShiftUnitApp A P) where
  mem := homPreShiftUnitApp_mem A P
  naturality {X X'} {q} {g} hg := by
    change g ≫ homPreShiftUnitApp A P X' =
      sign k (0 * q) • (homPreShiftUnitApp A P X ≫ F ◁ S.map (E ◁ g))
    rw [zero_mul, sign_zero, one_smul]
    unfold homPreShiftUnitApp
    have hi := TwoSupercategory.super_interchange A.unit_mem hg
    have hi' : 𝟙 b ◁ g ≫ A.unit ▷ X' =
        sign k (σ * q) • (A.unit ▷ X ≫ (F ≫ E) ◁ g) := by
      rw [hi, koszulSign_smul (R := k), smul_smul, sign_mul_self, one_smul]
    have hθ := P.inv_naturality (TwoSupercategory.whiskerLeft_mem E hg)
    rw [TwoSupercategory.leftUnitor_inv_naturality_assoc (R := k), reassoc_of% hi',
      Linear.smul_comp, Linear.comp_smul]
    simp only [Category.assoc]
    rw [TwoSupercategory.associator_naturality_right_assoc (R := k),
      ← TwoSupercategory.whiskerLeft_comp (R := k) F (E ◁ g), hθ,
      TwoSupercategory.whiskerLeft_smul, TwoSupercategory.whiskerLeft_comp (R := k),
      Linear.comp_smul, Linear.comp_smul, Linear.comp_smul,
      smul_smul, sign_mul_self, one_smul]

omit [S.Additive] [S.Linear k] [IsSuperfunctor k S] in
theorem homPreShiftCounit_supernatural :
    IsSupernatural k 0 (F := (homPre (k := k) F ⋙ homPre (k := k) E) ⋙ S)
      (G := 𝟭 (a ⟶ c)) (homPreShiftCounitApp A P) where
  mem := homPreShiftCounitApp_mem A P
  naturality {Y Y'} {q} {g} hg := by
    change S.map (E ◁ F ◁ g) ≫ homPreShiftCounitApp A P Y' =
      sign k (0 * q) • (homPreShiftCounitApp A P Y ≫ g)
    rw [zero_mul, sign_zero, one_smul]
    unfold homPreShiftCounitApp
    have hθ := P.hom_naturality
      (TwoSupercategory.whiskerLeft_mem E (TwoSupercategory.whiskerLeft_mem F hg))
    rw [reassoc_of% hθ, Linear.smul_comp]
    simp only [Category.assoc]
    rw [TwoSupercategory.associator_inv_naturality_right_assoc (R := k)]
    have hi := TwoSupercategory.super_interchange A.counit_mem hg
    have hi' : (E ≫ F) ◁ g ≫ A.counit ▷ Y' =
        sign k (σ * q) • (A.counit ▷ Y ≫ 𝟙 a ◁ g) := by
      rw [hi, koszulSign_smul (R := k), smul_smul, sign_mul_self, one_smul]
    rw [reassoc_of% hi', Linear.smul_comp, Linear.comp_smul, Linear.comp_smul,
      smul_smul, sign_mul_self, one_smul]
    simp only [Category.assoc]
    rw [TwoSupercategory.leftUnitor_naturality (R := k)]

/-- The unit of the shifted precomposition adjunction. -/
def homPreShiftUnit :
    𝟭 (b ⟶ c) ⟶ (homPre (k := k) E ⋙ S) ⋙ homPre (k := k) F :=
  (homPreShiftUnit_supernatural A P).toNatTrans

/-- The counit of the shifted precomposition adjunction. -/
def homPreShiftCounit :
    homPre (k := k) F ⋙ (homPre (k := k) E ⋙ S) ⟶ 𝟭 (a ⟶ c) :=
  (homPreShiftCounit_supernatural A P).toNatTrans

/-- Raising precomposition followed by a parity-`σ` shift is left adjoint to lowering
precomposition, for a left adjunction `F ⊣ E` with unit and counit of parity `σ`.
The adjunction is on the full Hom supercategories. -/
def homPreShiftAdjunction :
    homPre (k := k) (c := c) E ⋙ S ⊣ homPre (k := k) F where
  unit := homPreShiftUnit A P
  counit := homPreShiftCounit A P
  left_triangle_components X := by
    change S.map (E ◁ homPreShiftUnitApp A P X) ≫ homPreShiftCounitApp A P (S.obj (E ≫ X)) =
      𝟙 _
    unfold homPreShiftCounitApp
    rw [← Category.assoc, P.hom_naturality_even
      (TwoSupercategory.whiskerLeft_mem E (homPreShiftUnitApp_mem A P X))]
    unfold homPreShiftUnitApp
    simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
    rw [TwoSupercategory.associator_inv_naturality_right_assoc (R := k)]
    have hi := TwoSupercategory.super_interchange A.counit_mem (P.inv_mem (E ≫ X))
    have hi' : (E ≫ F) ◁ (P.iso (E ≫ X)).inv ≫ A.counit ▷ S.obj (E ≫ X) =
        sign k (σ * σ) • (A.counit ▷ (E ≫ X) ≫ 𝟙 a ◁ (P.iso (E ≫ X)).inv) := by
      rw [hi, koszulSign_smul (R := k), smul_smul, sign_mul_self, one_smul]
    rw [reassoc_of% hi', Linear.smul_comp, Category.assoc,
      TwoSupercategory.leftUnitor_naturality (R := k)]
    simp only [Linear.comp_smul]
    have hz := A.right_triangle_whiskerRight X
    rw [koszulSign_smul (R := k)] at hz
    rw [reassoc_of% hz, Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.hom_inv_id,
      smul_smul, sign_mul_self, one_smul]
  right_triangle_components Y := by
    change homPreShiftUnitApp A P (F ≫ Y) ≫ F ◁ homPreShiftCounitApp A P Y = 𝟙 _
    unfold homPreShiftUnitApp homPreShiftCounitApp
    simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
    rw [TwoSupercategory.whiskerLeft_inv_hom_assoc (R := k)]
    exact A.left_triangle_whiskerRight Y

end Adjunction

section Content
variable {I X : Type*} [AddCommGroup X] (D : Datum I X)

/-- The parity `|i|(⟨hᵢ, x⟩ + 1)` of the leftward cup and cap of colour `i` at `x`.
It agrees with `ipar` of `MoreGenerators.lean`. -/
def leftAdjParity (i : I) (x : X) : ZMod 2 := D.parity i * ((D.h i x : ZMod 2) + 1)

/-- The leftward parity is the same at both ends of an `i`-edge. -/
theorem leftAdjParity_edge (i : I) {x y : X} (h : x + D.α i = y) :
    leftAdjParity D i y = leftAdjParity D i x := by
  subst h
  simp only [leftAdjParity, Datum.h, map_add, D.cd.coroot_root_self]
  push_cast
  rw [show (2 : ZMod 2) = 0 from rfl, add_zero]

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {D}

/-- Shifted left adjunctions `Fᵢ ⊣ Eᵢ` of a factor family, at the leftward parity.
For an actual factor these are to be constructed from Rouquier's local inverses
(the super analogue of `RouqLoc.leftAdjunction`); here they are an explicit input. -/
structure RouquierLeftAdjoints (T : RouquierFamily (k := k) (B := B) D) where
  adjL : ∀ (i : I) {x y : X} (h : x + D.α i = y),
    ShiftedSuperAdjunction (k := k) (T.F i h) (T.E i h) (leftAdjParity D i x)

variable [∀ a b : B, PiSupercategory k (a ⟶ b)]

/-- Lowering precomposition, shifted by the leftward parity on its output side. -/
def homContentPreF (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
    (i : I) (muM : X) {muP nuP : X} (h : -nuP + D.α i = -muP) :
    homWeightSector T.obj W nuP muM ⥤ homWeightSector T.obj W muP muM :=
  homPre (k := k) (T.F i h) ⋙ homParityShift (k := k) (leftAdjParity D i (-nuP))

/-- The parity shift squares to the identity. -/
def homParityShiftSquare {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [Supercategory k C] [PiSupercategory k C] (p : ZMod 2) :
    homParityShift (k := k) (C := C) p ⋙ homParityShift (k := k) p ≅ 𝟭 C :=
  homParityShiftAdd p p ≪≫ eqToIso (by rw [zmod2_add_self, homParityShift_zero])

/-- Raising precomposition is left adjoint to the shifted lowering precomposition,
given the factor's shifted left adjunction. The raising functor is unshifted, as in
the asymmetric content convention of `RouquierHomContent.lean`. -/
def homContentPreAdjunction (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
    (L : RouquierLeftAdjoints (k := k) T)
    (i : I) (muM : X) {muP nuP : X} (h : -nuP + D.α i = -muP) :
    homContentPreE T W i muM h ⊣ homContentPreF T W i muM h :=
  let σ := leftAdjParity D i (-nuP)
  let S := homParityShift (k := k) (C := homWeightSector T.obj W nuP muM) σ
  let adj : (homPre (k := k) (T.E i h) ⋙ S) ⋙ S ⊣ S ⋙ homPre (k := k) (T.F i h) :=
    (homPreShiftAdjunction (L.adjL i h) (homParityShiftDatum σ)).comp
      (homParityShiftAdjunction σ)
  let eL : (homPre (k := k) (T.E i h) ⋙ S) ⋙ S ≅ homContentPreE T W i muM h :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (homParityShiftSquare σ) ≪≫
      Functor.rightUnitor _
  (adj.ofNatIsoLeft eL).ofNatIsoRight (homParityShiftCommute (homPre (k := k) (T.F i h)) σ).symm

end Content
end OddMath.SKM
