import OddMath.SKM.RouquierDistinctLeftRotation

/-!
# Left rotation from the distinct cup pitchfork

Brundan–Ellis, Lemma 7.1, (7.2), followed by Proposition 6.2, (6.6):
closing the cup pitchfork computes the prescribed left mate. Sliding
its homogeneous sideways crossing across the counit retains the Koszul
sign. The cup pitchfork is an explicit intermediate premise; the
canonical factor action must supply it before this criterion is used.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
section Coherence
variable {a b c d e : B}
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

private theorem coh_lambda_post (V : b ⟶ c) (E' : c ⟶ d) :
    (leftUnitor (V ≫ E')).inv ≫ (associator (𝟙 b) V E').inv = (leftUnitor V).inv ▷ E' := by
  have h : (Bicategory.leftUnitor (Underlying2.hom1 (R := k) V ≫
        Underlying2.hom1 (R := k) E')).inv ≫
      (Bicategory.associator (𝟙 _) (Underlying2.hom1 (R := k) V)
        (Underlying2.hom1 (R := k) E')).inv =
      Bicategory.whiskerRight (Bicategory.leftUnitor (Underlying2.hom1 (R := k) V)).inv
        (Underlying2.hom1 (R := k) E') := by
    bicategory
  exact congrArg Subtype.val h

private theorem coh_pentagon_post {e : B} (F : b ⟶ a) (E : a ⟶ b) (V : b ⟶ c) (E' : c ⟶ e) :
    (associator (F ≫ E) V E').hom ≫ (associator F E (V ≫ E')).hom ≫
      F ◁ (associator E V E').inv =
    (associator F E V).hom ▷ E' ≫ (associator F (E ≫ V) E').hom := by
  have h : (Bicategory.associator (Underlying2.hom1 (R := k) F ≫ Underlying2.hom1 (R := k) E)
        (Underlying2.hom1 (R := k) V) (Underlying2.hom1 (R := k) E')).hom ≫
      (Bicategory.associator (Underlying2.hom1 (R := k) F) (Underlying2.hom1 (R := k) E)
        (Underlying2.hom1 (R := k) V ≫ Underlying2.hom1 (R := k) E')).hom ≫
      Bicategory.whiskerLeft (Underlying2.hom1 (R := k) F)
        (Bicategory.associator (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) V)
          (Underlying2.hom1 (R := k) E')).inv =
      Bicategory.whiskerRight (Bicategory.associator (Underlying2.hom1 (R := k) F)
          (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) V)).hom
          (Underlying2.hom1 (R := k) E') ≫
        (Bicategory.associator (Underlying2.hom1 (R := k) F)
          (Underlying2.hom1 (R := k) E ≫ Underlying2.hom1 (R := k) V)
          (Underlying2.hom1 (R := k) E')).hom := by
    bicategory
  exact congrArg Subtype.val h

private theorem coh_cup_finish (F : a ⟶ b) (G : b ⟶ c) (H : c ⟶ d) (V : d ⟶ e) :
    (associator F (G ≫ H) V).hom ≫ F ◁ (associator G H V).hom =
      (associator F G H).inv ▷ V ≫ (associator (F ≫ G) H V).hom ≫
        (associator F G (H ≫ V)).hom := by
  have h : (Bicategory.associator (Underlying2.hom1 (R := k) F)
        (Underlying2.hom1 (R := k) G ≫ Underlying2.hom1 (R := k) H)
        (Underlying2.hom1 (R := k) V)).hom ≫
      Bicategory.whiskerLeft (Underlying2.hom1 (R := k) F)
        (Bicategory.associator (Underlying2.hom1 (R := k) G)
          (Underlying2.hom1 (R := k) H) (Underlying2.hom1 (R := k) V)).hom =
    Bicategory.whiskerRight (Bicategory.associator (Underlying2.hom1 (R := k) F)
      (Underlying2.hom1 (R := k) G) (Underlying2.hom1 (R := k) H)).inv
      (Underlying2.hom1 (R := k) V) ≫
      (Bicategory.associator (Underlying2.hom1 (R := k) F ≫ Underlying2.hom1 (R := k) G)
        (Underlying2.hom1 (R := k) H) (Underlying2.hom1 (R := k) V)).hom ≫
      (Bicategory.associator (Underlying2.hom1 (R := k) F)
        (Underlying2.hom1 (R := k) G)
        (Underlying2.hom1 (R := k) H ≫ Underlying2.hom1 (R := k) V)).hom := by
    bicategory
  exact congrArg Subtype.val h

private theorem coh_rho_pre (F : a ⟶ b) (G : b ⟶ c) :
    (associator F G (𝟙 c)).hom ≫ F ◁ (rightUnitor G).hom =
      (rightUnitor (F ≫ G)).hom := by
  have h : (Bicategory.associator (Underlying2.hom1 (R := k) F)
        (Underlying2.hom1 (R := k) G) (𝟙 _)).hom ≫
      Bicategory.whiskerLeft (Underlying2.hom1 (R := k) F)
        (Bicategory.rightUnitor (Underlying2.hom1 (R := k) G)).hom =
    (Bicategory.rightUnitor (Underlying2.hom1 (R := k) F ≫
      Underlying2.hom1 (R := k) G)).hom := by
    bicategory
  exact congrArg Subtype.val h
end Coherence

variable {c₀ m a₁ b₁ : B} {E_d : c₀ ⟶ m} {F_d : m ⟶ c₀} {E_c : m ⟶ b₁}
  {E_b : c₀ ⟶ a₁} {E_a : a₁ ⟶ b₁} {F_a : b₁ ⟶ a₁} {σd σa p : ZMod 2}

private theorem leftCrossMate_cup_close
    (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa)
    (T : E_d ≫ E_c ⟶ E_b ≫ E_a) :
    leftCrossMate A_d A_a T =
      ((leftUnitor E_c).inv ≫ A_d.unit ▷ E_c ≫ (associator F_d E_d E_c).hom ≫
        F_d ◁ T ≫ (associator F_d E_b E_a).inv) ▷ F_a ≫
        (associator (F_d ≫ E_b) E_a F_a).hom ≫
        (F_d ≫ E_b) ◁ A_a.counit ≫ (rightUnitor (F_d ≫ E_b)).hom := by
  unfold leftCrossMate
  rw [TwoSupercategory.whiskerRight_comp (R := k) A_d.unit E_c F_a]
  simp only [Category.assoc]
  rw [reassoc_of% (coh_lambda_post (k := k) E_c F_a),
    reassoc_of% (coh_pentagon_post (k := k) F_d E_d E_c F_a)]
  rw [← TwoSupercategory.associator_naturality_middle_assoc (R := k) F_d T F_a]
  rw [reassoc_of% (coh_cup_finish (k := k) F_d E_b E_a F_a)]
  rw [← TwoSupercategory.associator_naturality_right_assoc (R := k) F_d E_b A_a.counit]
  rw [coh_rho_pre (k := k) F_d E_b]
  simp only [TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]

private theorem cup_close_triangle
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa) :
    (rightUnitor E_c).inv ▷ F_a ≫ (E_c ◁ A_a.unit) ▷ F_a ≫
      (associator E_c F_a E_a).inv ▷ F_a ≫ (associator (E_c ≫ F_a) E_a F_a).hom ≫
      (E_c ≫ F_a) ◁ A_a.counit ≫ (rightUnitor (E_c ≫ F_a)).hom = 𝟙 (E_c ≫ F_a) := by
  have h := congrArg (fun f => E_c ◁ f) A_a.left_triangle
  simp only [TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.whiskerLeft_id (R := k)] at h
  rw [TwoSupercategory.whisker_assoc (R := k) E_c A_a.unit F_a]
  simp only [Category.assoc]
  rw [reassoc_of% (coh_rho_assoc (k := k) E_c F_a),
    reassoc_of% (coh_assoc_mid (k := k) E_c F_a E_a F_a)]
  rw [TwoSupercategory.comp_whiskerLeft (R := k) E_c F_a A_a.counit]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← coh_rho_pre (k := k) E_c F_a]
  simp only [Iso.inv_hom_id_assoc]
  exact h

/-- Closing the cup pitchfork evaluates the left mate. Only the
homogeneous crossing moves across the counit, with sign `(-1)^(σa p)`;
the contracted F triangle contributes no further sign. -/
theorem leftCrossMate_eq_of_cup_pitchfork
    (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa)
    (T : E_d ≫ E_c ⟶ E_b ≫ E_a) (l : E_c ≫ F_a ⟶ F_d ≫ E_b)
    (hl : l ∈ parity (R := k) _ _ p) (q : k)
    (hcup : (leftUnitor E_c).inv ≫ A_d.unit ▷ E_c ≫ (associator F_d E_d E_c).hom ≫
      F_d ◁ T ≫ (associator F_d E_b E_a).inv =
      q • ((rightUnitor E_c).inv ≫ E_c ◁ A_a.unit ≫
        (associator E_c F_a E_a).inv ≫ l ▷ E_a)) :
    leftCrossMate A_d A_a T = (q * sign k (σa * p)) • l := by
  rw [leftCrossMate_cup_close A_d A_a T, hcup]
  simp only [TwoSupercategory.smul_whiskerRight (R := k),
    TwoSupercategory.comp_whiskerRight (R := k), Linear.smul_comp, Category.assoc]
  rw [TwoSupercategory.associator_naturality_left_assoc (R := k) l E_a F_a,
    TwoSupercategory.super_interchange_assoc hl A_a.counit_mem,
    koszulSign_smul (R := k)]
  simp only [Linear.comp_smul]
  rw [TwoSupercategory.rightUnitor_naturality (R := k) l,
    reassoc_of% (cup_close_triangle A_a), smul_smul, mul_comm p σa]

/-- The inverse of the rotated crossing has the reciprocal parameter,
and the same Koszul sign. Both products follow without exchanging odd maps. -/
theorem leftCrossMate_inv_products_of_cup_pitchfork
    (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa)
    (T : E_d ≫ E_c ⟶ E_b ≫ E_a) (l : E_c ≫ F_a ⟶ F_d ≫ E_b)
    (s : F_d ≫ E_b ⟶ E_c ≫ F_a)
    (hl : l ∈ parity (R := k) _ _ p) (q : kˣ)
    (hls : l ≫ s = 𝟙 _) (hsl : s ≫ l = 𝟙 _)
    (hcup : (leftUnitor E_c).inv ≫ A_d.unit ▷ E_c ≫ (associator F_d E_d E_c).hom ≫
      F_d ◁ T ≫ (associator F_d E_b E_a).inv =
      (q : k) • ((rightUnitor E_c).inv ≫ E_c ◁ A_a.unit ≫
        (associator E_c F_a E_a).inv ≫ l ▷ E_a)) :
    leftCrossMate A_d A_a T ≫ ((↑q⁻¹ * sign k (σa * p)) • s) = 𝟙 _ ∧
      ((↑q⁻¹ * sign k (σa * p)) • s) ≫ leftCrossMate A_d A_a T = 𝟙 _ := by
  rw [leftCrossMate_eq_of_cup_pitchfork A_d A_a T l hl (q : k) hcup]
  constructor
  · rw [Linear.smul_comp, Linear.comp_smul, smul_smul, hls,
      mul_mul_mul_comm (q : k), Units.mul_inv, sign_mul_self, mul_one, one_smul]
  · rw [Linear.smul_comp, Linear.comp_smul, smul_smul, hsl,
      mul_mul_mul_comm (↑q⁻¹ : k), Units.inv_mul, sign_mul_self, mul_one, one_smul]

/-- Cup cyclicity with a unit parameter and an invertible sideways map
makes the specified left mate invertible. The cup identity remains an
explicit intermediate premise. -/
theorem leftCrossMate_isIso_of_cup_pitchfork
    (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa)
    (T : E_d ≫ E_c ⟶ E_b ≫ E_a) (l : E_c ≫ F_a ⟶ F_d ≫ E_b)
    [IsIso l] (hl : l ∈ parity (R := k) _ _ p) (q : kˣ)
    (hcup : (leftUnitor E_c).inv ≫ A_d.unit ▷ E_c ≫ (associator F_d E_d E_c).hom ≫
      F_d ◁ T ≫ (associator F_d E_b E_a).inv =
      (q : k) • ((rightUnitor E_c).inv ≫ E_c ◁ A_a.unit ≫
        (associator E_c F_a E_a).inv ≫ l ▷ E_a)) :
    IsIso (leftCrossMate A_d A_a T) :=
  let h := leftCrossMate_inv_products_of_cup_pitchfork A_d A_a T l (inv l) hl q
    (IsIso.hom_inv_id l) (IsIso.inv_hom_id l) hcup
  ⟨⟨_, h.1, h.2⟩⟩

end OddMath.SKM
