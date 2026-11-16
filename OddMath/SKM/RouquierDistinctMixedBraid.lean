import OddMath.SKM.RouquierRectangularComposition

/-!
# The rectangular mate of the corrected distinct braid

Brundan–Ellis, Lemma 3.3 (3.8): the two mixed braid words are obtained by
bending the outer equal-colour strands in the quiver Hecke braid. The
correction is retained as the linear mate of the explicit dotted terms.
This is the input before the cap evaluations in Lemma 7.1, `pf_a`.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r
private theorem parity_square (p : ZMod 2) : p * p = p := by fin_cases p <;> rfl

private theorem correction_sign {k : Type*} [CommRing k] (p q s : ZMod 2) :
    sign k (p * (p * q)) * zsign k (p * (q + s)) = zsign k (p * s) := by
  fin_cases p <;> fin_cases q <;> fin_cases s <;>
    simp [sign, zsign, show (1 : ZMod 2) + 1 = 0 by decide]

private theorem correction_scalar {k : Type*} [CommRing k] (p q s : ZMod 2) (a : k) :
    sign k (p * (p * q)) * (zsign k (p * (q + s)) * a) = zsign k (p * s) * a := by
  rw [← mul_assoc, correction_sign]

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- The linear outer mate with the three-strand source and target
associators retained. -/
def rectangularTripleMateLinearMap {a b c d e f : B}
    {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₃ : e ⟶ f} {F₃ : f ⟶ e}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₃ : SuperAdjunction (k := k) E₃ F₃)
    (G₁ : a ⟶ c) (G₂ : c ⟶ e) (H₁ : b ⟶ d) (H₂ : d ⟶ f) :
    (G₁ ≫ (G₂ ≫ E₃) ⟶ E₁ ≫ (H₁ ≫ H₂)) →ₗ[k]
      ((F₁ ≫ G₁) ≫ G₂ ⟶ H₁ ≫ (H₂ ≫ F₃)) where
  toFun z := (associator F₁ G₁ G₂).hom ≫
    rectangularMateLinearMap A₁ A₃ (G₁ ≫ G₂) (H₁ ≫ H₂)
      ((associator G₁ G₂ E₃).hom ≫ z) ≫ (associator H₁ H₂ F₃).hom
  map_add' x y := by
    simp only [Preadditive.comp_add, map_add, Preadditive.add_comp]
  map_smul' z x := by
    simp only [Linear.comp_smul, map_smul, Linear.smul_comp, RingHom.id_apply]

namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (i j : I)
  {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)

local notation "Eab" => T.E i hab
local notation "Eaf" => T.E j haf
local notation "Ebc" => T.E j hbc
local notation "Ebe" => T.E i hbe
local notation "Efc" => T.E i hfc
local notation "Ecd" => T.E i hcd
local notation "Eed" => T.E j hed
local notation "Fab" => T.F i hab
local notation "Fbe" => T.F i hbe
local notation "Ffc" => T.F i hfc
local notation "Fcd" => T.F i hcd

/-- The first mixed braid word, with the two actual right mates followed
by the inherited upward crossing. -/
def distinctMixedBraidLeft : (Fab ≫ Eab) ≫ Ebc ⟶ Ebc ≫ (Ecd ≫ Fcd) :=
  crossMate (T.adj i hab) (T.adj i hbe) (T.cross i i hab hbe hab hbe) ▷ Ebc ≫
    (associator Ebe Fbe Ebc).hom ≫
    Ebe ◁ crossMate (T.adj i hbe) (T.adj i hcd) (T.cross i j hbc hcd hbe hed) ≫
    (associator Ebe Eed Fcd).inv ≫ T.cross j i hbe hed hbc hcd ▷ Fcd ≫
    (associator Ebc Ecd Fcd).hom

/-- The second mixed braid word, with the inherited upward crossing
followed by the two actual right mates. -/
def distinctMixedBraidRight : (Fab ≫ Eab) ≫ Ebc ⟶ Ebc ≫ (Ecd ≫ Fcd) :=
  (associator Fab Eab Ebc).hom ≫ Fab ◁ T.cross j i hab hbc haf hfc ≫
    (associator Fab Eaf Efc).inv ≫
    crossMate (T.adj i hab) (T.adj i hfc) (T.cross i j haf hfc hab hbc) ▷ Efc ≫
    (associator Ebc Ffc Efc).hom ≫
    Ebc ◁ crossMate (T.adj i hfc) (T.adj i hcd) (T.cross i i hfc hcd hfc hcd)

/-- The prescribed outer transpose for the corrected `i,j,i` braid. -/
def distinctMixedBraidOuterMate :
    (Eab ≫ (Ebc ≫ Ecd) ⟶ Eab ≫ (Ebc ≫ Ecd)) →ₗ[k]
      ((Fab ≫ Eab) ≫ Ebc ⟶ Ebc ≫ (Ecd ≫ Fcd)) :=
  rectangularTripleMateLinearMap (T.adj i hab) (T.adj i hcd) Eab Ebc Ebc Ecd

/-- Evaluate the outer linear map without unfolding its proof fields. -/
theorem distinctMixedBraidOuterMate_apply (z : Eab ≫ (Ebc ≫ Ecd) ⟶ Eab ≫ (Ebc ≫ Ecd)) :
    T.distinctMixedBraidOuterMate i j hab hbc hcd z =
    (associator Fab Eab Ebc).hom ≫
      rectangularMate (T.adj i hab) (T.adj i hcd) (Eab ≫ Ebc) (Ebc ≫ Ecd)
        ((associator Eab Ebc Ecd).hom ≫ z) ≫ (associator Ebc Ecd Fcd).hom := rfl

/-- The first mixed word is the mate of the first upward braid word. -/
theorem distinctMixedBraidLeft_eq :
    T.distinctMixedBraidLeft i j hab hbc hbe hcd hed =
    koszulSign (D.parity i) (D.parity i * D.parity j) •
      T.distinctMixedBraidOuterMate i j hab hbc hcd
        (Eab ◁ T.cross i j hbc hcd hbe hed ≫
          (associator Eab Ebe Eed).inv ≫ T.cross i i hab hbe hab hbe ▷ Eed ≫
          (associator Eab Ebe Eed).hom ≫ Eab ◁ T.cross j i hbe hed hbc hcd) := by
  have hc := crossMate_comp_crossMate (T.adj i hab) (T.adj i hbe) (T.adj i hcd)
    (T.cross_mem i i hab hbe hab hbe) (T.cross_mem i j hbc hcd hbe hed)
  simp only [parity_square] at hc
  unfold distinctMixedBraidLeft
  rw [reassoc_of% hc]
  simp only [Preadditive.zsmul_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% (rectangularMate_right (T.adj i hab) (T.adj i hcd) (Eab ≫ Ebc)
    (T.cross j i hbe hed hbc hcd)
    ((associator Eab Ebc Ecd).hom ≫ Eab ◁ T.cross i j hbc hcd hbe hed ≫
      (associator Eab Ebe Eed).inv ≫ T.cross i i hab hbe hab hbe ▷ Eed ≫
      (associator Eab Ebe Eed).hom))]
  rw [distinctMixedBraidOuterMate_apply]

/-- The second mixed word is the mate of the second upward braid word.
The two different crossing degrees give the same Koszul coefficient. -/
theorem distinctMixedBraidRight_eq :
    T.distinctMixedBraidRight i j hab haf hbc hfc hcd =
    koszulSign (D.parity i) (D.parity i * D.parity j) •
      T.distinctMixedBraidOuterMate i j hab hbc hcd
        ((associator Eab Ebc Ecd).inv ≫ T.cross j i hab hbc haf hfc ▷ Ecd ≫
          (associator Eaf Efc Ecd).hom ≫ Eaf ◁ T.cross i i hfc hcd hfc hcd ≫
          (associator Eaf Efc Ecd).inv ≫ T.cross i j haf hfc hab hbc ▷ Ecd ≫
          (associator Eab Ebc Ecd).hom) := by
  have hc := crossMate_comp_crossMate (T.adj i hab) (T.adj i hfc) (T.adj i hcd)
    (T.cross_mem i j haf hfc hab hbc) (T.cross_mem i i hfc hcd hfc hcd)
  simp only [parity_square, koszulSign_comm (D.parity i * D.parity j) (D.parity i)] at hc
  unfold distinctMixedBraidRight
  rw [hc]
  simp only [Preadditive.comp_zsmul, Iso.inv_hom_id_assoc]
  rw [← reassoc_of% (rectangularMate_left (T.adj i hab) (T.adj i hcd) (Ebc ≫ Ecd)
    (T.cross j i hab hbc haf hfc)
    ((associator Eaf Efc Ecd).hom ≫ Eaf ◁ T.cross i i hfc hcd hfc hcd ≫
      (associator Eaf Efc Ecd).inv ≫ T.cross i j haf hfc hab hbc ▷ Ecd ≫
      (associator Eab Ebc Ecd).hom))]
  rw [distinctMixedBraidOuterMate_apply]
  simp only [Iso.hom_inv_id_assoc]

variable {Sc : Scalars D k}

/-- The mixed braid correction follows from the actual multicolour
braid field, with every polynomial term passed through the prescribed
outer mate. No mixed braid or cap cyclicity hypothesis is added. -/
private theorem distinctMixedBraid_correction_mate (M : RouquierMulticolour T Sc) (hne : i ≠ j) :
    T.distinctMixedBraidLeft i j hab hbc hbe hcd hed -
      T.distinctMixedBraidRight i j hab haf hbc hfc hcd =
    koszulSign (D.parity i) (D.parity i * D.parity j) •
      T.distinctMixedBraidOuterMate i j hab hbc hcd
        (∑ s ∈ Finset.range (D.dn i j),
          (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
            (rouquierPower (T.dot i hab) s ▷ (Ebc ≫ Ecd) ≫
              Eab ◁ Ebc ◁ rouquierPower (T.dot i hcd) (D.dn i j - 1 - s)) +
        ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), ∑ s ∈ Finset.range p,
          (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
            (rouquierPower (T.dot i hab) s ▷ (Ebc ≫ Ecd) ≫
              Eab ◁ (rouquierPower (T.dot j hbc) q ▷ Ecd) ≫
              Eab ◁ Ebc ◁ rouquierPower (T.dot i hcd) (p - 1 - s))) := by
  rw [T.distinctMixedBraidLeft_eq i j hab hbc hbe hcd hed,
    T.distinctMixedBraidRight_eq i j hab haf hbc hfc hcd,
    ← smul_sub, ← map_sub]
  congr 2
  simpa only [Category.assoc] using M.braidEq i j hne hab haf hbc hbe hfc hcd hed

/-- The explicit bent correction of Lemma 3.3 (3.8). The crossing-degree
sign cancels the mixed-colour part of the upward coefficient, leaving
`(-1)^(p_i s)` on each dotted term. The `s = 0` boundary coefficient is
therefore exactly `t_ij`. -/
theorem distinctMixedBraid_correction (M : RouquierMulticolour T Sc) (hne : i ≠ j) :
    T.distinctMixedBraidLeft i j hab hbc hbe hcd hed -
      T.distinctMixedBraidRight i j hab haf hbc hfc hcd =
    (∑ s ∈ Finset.range (D.dn i j),
      (zsign k (D.parity i * s) * (Sc.t i j : k)) •
        T.distinctMixedBraidOuterMate i j hab hbc hcd
          (rouquierPower (T.dot i hab) s ▷ (Ebc ≫ Ecd) ≫
            Eab ◁ Ebc ◁ rouquierPower (T.dot i hcd) (D.dn i j - 1 - s))) +
    ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), ∑ s ∈ Finset.range p,
      (zsign k (D.parity i * s) * Sc.s i j p q) •
        T.distinctMixedBraidOuterMate i j hab hbc hcd
          (rouquierPower (T.dot i hab) s ▷ (Ebc ≫ Ecd) ≫
            Eab ◁ (rouquierPower (T.dot j hbc) q ▷ Ecd) ≫
            Eab ◁ Ebc ◁ rouquierPower (T.dot i hcd) (p - 1 - s)) := by
  rw [T.distinctMixedBraid_correction_mate i j hab haf hbc hbe hfc hcd hed M hne,
    koszulSign_smul (R := k)]
  simp only [map_add, map_sum, map_smul, smul_add, Finset.smul_sum, smul_smul,
    correction_scalar]

end RouquierFamily
end OddMath.SKM
