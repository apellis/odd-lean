import OddMath.SKM.RouquierHomDistinctPreMate

/-!
# Left rotation from the distinct cap pitchfork

Brundan–Ellis, Proposition 7.2 (7.5), followed by Proposition 6.2 (6.6):
the cap pitchfork evaluates the prescribed left mate, including the Koszul
factor from exchanging the left cup and sideways crossing. This is the
bicategorical contraction in `SwappedDistinctPreMate.md` §4. The cap
pitchfork remains an explicit intermediate hypothesis; its derivation for
the canonical Rouquier left adjunctions is not asserted here.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {c₀ m a₁ b₁ : B} {E_d : c₀ ⟶ m} {F_d : m ⟶ c₀} {E_c : m ⟶ b₁}
  {E_b : c₀ ⟶ a₁} {E_a : a₁ ⟶ b₁} {F_a : b₁ ⟶ a₁} {σd σa p : ZMod 2}

/-- The cap pitchfork closes the prescribed crossing into the specified
sideways map. The remaining cup contracts by the F triangle, retaining
the sign from moving it across that map. -/
theorem leftCrossMate_eq_of_cap_pitchfork
    (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa)
    (T : E_d ≫ E_c ⟶ E_b ≫ E_a) (l : E_c ≫ F_a ⟶ F_d ≫ E_b)
    (hl : l ∈ parity (R := k) _ _ p) (q : k)
    (hcap : (associator E_d E_c F_a).inv ≫ T ▷ F_a ≫
      (associator E_b E_a F_a).hom ≫ E_b ◁ A_a.counit ≫ (rightUnitor E_b).hom =
      q • (E_d ◁ l ≫ (associator E_d F_d E_b).inv ≫
        A_d.counit ▷ E_b ≫ (leftUnitor E_b).hom)) :
    leftCrossMate A_d A_a T = (q * sign k (σd * p)) • l := by
  have h := congrArg (fun f =>
    (leftUnitor (E_c ≫ F_a)).inv ≫ A_d.unit ▷ (E_c ≫ F_a) ≫
      (associator F_d E_d (E_c ≫ F_a)).hom ≫ F_d ◁ f) hcap
  simp only [TwoSupercategory.whiskerLeft_comp (R := k),
    TwoSupercategory.whiskerLeft_smul (R := k), Linear.comp_smul] at h
  change leftCrossMate A_d A_a T = _ at h
  rw [A_d.unit_slide hl,
    A_d.left_triangle_whiskerRight E_b, Category.comp_id, smul_smul] at h
  exact h

/-- The inverse of the rotated crossing has the reciprocal parameter,
and the same Koszul sign. Both products follow without exchanging odd maps. -/
theorem leftCrossMate_inv_products_of_cap_pitchfork
    (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa)
    (T : E_d ≫ E_c ⟶ E_b ≫ E_a) (l : E_c ≫ F_a ⟶ F_d ≫ E_b)
    (s : F_d ≫ E_b ⟶ E_c ≫ F_a)
    (hl : l ∈ parity (R := k) _ _ p) (q : kˣ)
    (hls : l ≫ s = 𝟙 _) (hsl : s ≫ l = 𝟙 _)
    (hcap : (associator E_d E_c F_a).inv ≫ T ▷ F_a ≫
      (associator E_b E_a F_a).hom ≫ E_b ◁ A_a.counit ≫ (rightUnitor E_b).hom =
      (q : k) • (E_d ◁ l ≫ (associator E_d F_d E_b).inv ≫
        A_d.counit ▷ E_b ≫ (leftUnitor E_b).hom)) :
    leftCrossMate A_d A_a T ≫ ((↑q⁻¹ * sign k (σd * p)) • s) = 𝟙 _ ∧
      ((↑q⁻¹ * sign k (σd * p)) • s) ≫ leftCrossMate A_d A_a T = 𝟙 _ := by
  rw [leftCrossMate_eq_of_cap_pitchfork A_d A_a T l hl (q : k) hcap]
  constructor
  · rw [Linear.smul_comp, Linear.comp_smul, smul_smul, hls,
      mul_mul_mul_comm (q : k), Units.mul_inv, sign_mul_self, mul_one, one_smul]
  · rw [Linear.smul_comp, Linear.comp_smul, smul_smul, hsl,
      mul_mul_mul_comm (↑q⁻¹ : k), Units.inv_mul, sign_mul_self, mul_one, one_smul]

/-- Cap cyclicity and the distinct right-crossing inverse relations suffice
for invertibility of the specified left mate. This is an intermediate
criterion; no cap cyclicity premise is discharged by this theorem. -/
theorem leftCrossMate_isIso_of_cap_pitchfork
    (A_d : ShiftedSuperAdjunction (k := k) F_d E_d σd)
    (A_a : ShiftedSuperAdjunction (k := k) F_a E_a σa)
    (T : E_d ≫ E_c ⟶ E_b ≫ E_a) (l : E_c ≫ F_a ⟶ F_d ≫ E_b)
    (s : F_d ≫ E_b ⟶ E_c ≫ F_a)
    (hl : l ∈ parity (R := k) _ _ p) (q : kˣ)
    (hls : l ≫ s = 𝟙 _) (hsl : s ≫ l = 𝟙 _)
    (hcap : (associator E_d E_c F_a).inv ≫ T ▷ F_a ≫
      (associator E_b E_a F_a).hom ≫ E_b ◁ A_a.counit ≫ (rightUnitor E_b).hom =
      (q : k) • (E_d ◁ l ≫ (associator E_d F_d E_b).inv ≫
        A_d.counit ▷ E_b ≫ (leftUnitor E_b).hom)) :
    IsIso (leftCrossMate A_d A_a T) :=
  let h := leftCrossMate_inv_products_of_cap_pitchfork A_d A_a T l s hl q hls hsl hcap
  ⟨⟨_, h.1, h.2⟩⟩

end OddMath.SKM
