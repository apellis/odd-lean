import OddMath.SKM.RouquierMulticolour
import OddMath.SKM.RouquierDotSlide

/-! # Finite rows of the distinct quadratic cup word

Brundan–Ellis Lemma 7.1, `Lemma71Cup.pcu_b`, in the strict positive
range. The actual lower inverse-defined cup, upward double crossing
and dotted right cap give the leading quadratic parameter times the
shifted boundary Kronecker coefficient.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

private def cupCapRowLinear {a b c : B} (E : a ⟶ b) (F : b ⟶ a) (G : b ⟶ c)
    (cup : 𝟙 b ⟶ F ≫ E) (cap : F ≫ E ⟶ 𝟙 b) :
    End (E ≫ G) →ₗ[k] End G where
  toFun z := (leftUnitor G).inv ≫ cup ▷ G ≫ (associator F E G).hom ≫ F ◁ z ≫
    (associator F E G).inv ≫ cap ▷ G ≫ (leftUnitor G).hom
  map_add' z z' := by
    simp only [TwoSupercategory.whiskerLeft_add (R := k), Preadditive.comp_add,
      Preadditive.add_comp]
  map_smul' r z := by
    simp only [TwoSupercategory.whiskerLeft_smul (R := k), Linear.comp_smul,
      Linear.smul_comp, RingHom.id_apply]

private theorem cupCapRowLinear_left {a b c : B} (E : a ⟶ b) (F : b ⟶ a) (G : b ⟶ c)
    (cup : 𝟙 b ⟶ F ≫ E) (cap : F ≫ E ⟶ 𝟙 b) (x : End E) :
    cupCapRowLinear (k := k) E F G cup cap (x ▷ G) =
      (leftUnitor G).inv ≫ (cup ≫ F ◁ x ≫ cap) ▷ G ≫ (leftUnitor G).hom := by
  change (leftUnitor G).inv ≫ cup ▷ G ≫ (associator F E G).hom ≫ F ◁ (x ▷ G) ≫
    (associator F E G).inv ≫ cap ▷ G ≫ (leftUnitor G).hom = _
  rw [← TwoSupercategory.associator_naturality_middle_assoc (R := k) F x G]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, TwoSupercategory.comp_whiskerRight (R := k)]

private theorem cupCapRowLinear_right {a b c : B} (E : a ⟶ b) (F : b ⟶ a) (G : b ⟶ c)
    (cup : 𝟙 b ⟶ F ≫ E) (cap : F ≫ E ⟶ 𝟙 b) {p q : ZMod 2}
    (hcap : cap ∈ parity (R := k) _ _ p) (f : End G)
    (hf : f ∈ parity (R := k) _ _ q) (x : End E) :
    cupCapRowLinear (k := k) E F G cup cap (x ▷ G ≫ E ◁ f) =
      sign k (p * q) • (cupCapRowLinear (k := k) E F G cup cap (x ▷ G) ≫ f) := by
  have hs : (F ≫ E) ◁ f ≫ cap ▷ G =
      sign k (p * q) • (cap ▷ G ≫ 𝟙 b ◁ f) := by
    rw [TwoSupercategory.super_interchange (R := k) hcap hf, koszulSign_smul (R := k),
      smul_smul, sign_mul_self, one_smul]
  change (leftUnitor G).inv ≫ cup ▷ G ≫ (associator F E G).hom ≫
    F ◁ (x ▷ G ≫ E ◁ f) ≫ (associator F E G).inv ≫ cap ▷ G ≫
      (leftUnitor G).hom = _
  rw [TwoSupercategory.whiskerLeft_comp (R := k)]
  simp only [Category.assoc]
  rw [TwoSupercategory.associator_inv_naturality_right_assoc (R := k) F E f,
    ← TwoSupercategory.associator_naturality_middle_assoc (R := k) F x G]
  simp only [Iso.hom_inv_id_assoc]
  rw [reassoc_of% hs]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
  rw [TwoSupercategory.leftUnitor_naturality (R := k) f,
    cupCapRowLinear_left (k := k)]
  simp only [TwoSupercategory.comp_whiskerRight (R := k), Category.assoc]

namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) {i j : I} {a b d e : X}
  (hi : a + D.α i = b) (hij : b + D.α j = d) (hupper : b + D.α i = e)
local notation "Ei" => T.E i hi
local notation "Fi" => T.F i hi
local notation "Ej" => T.E j hij
local notation "L" => T.loc i hi hupper

/-- Close an endomorphism of the original upward pair by the prescribed
lower left cup and the given dotted right cap. -/
def distinctCupRowLinear (n : ℕ) : End (Ei ≫ Ej) →ₗ[k] End Ej :=
  cupCapRowLinear (k := k) Ei Fi Ej (L).cupL ((L).capD n)

/-- Left `i` dots add to the original cap exponent at the lower weight. -/
theorem distinctCupRow_leftDot (hh : 0 < D.h i b) (n p : ℕ)
    (hpn : p + n < (D.h i b).toNat) :
    T.distinctCupRowLinear hi hij hupper n (rouquierPower (T.dot i hi) p ▷ Ej) =
      if (D.h i b - 1).toNat = p + n then 𝟙 Ej else 0 := by
  unfold distinctCupRowLinear
  rw [cupCapRowLinear_left (k := k), (L).whiskerLeft_powComp_capD,
    (L).cupL_capD hh hpn]
  split_ifs
  · simp only [TwoSupercategory.id_whiskerRight (R := k), Category.id_comp, Iso.inv_hom_id]
  · simp only [TwoSupercategory.zero_whiskerRight (R := k), Limits.comp_zero, Limits.zero_comp]

/-- Every right-strand monomial below the lower positive cap boundary
vanishes after its prescribed homogeneous interchange sign. -/
theorem distinctCupRow_monomial_zero (hh : 0 < D.h i b) (n p q : ℕ)
    (hpn : p + n < (D.h i b - 1).toNat) :
    T.distinctCupRowLinear hi hij hupper n
      (rouquierPower (T.dot i hi) p ▷ Ej ≫ Ei ◁ rouquierPower (T.dot j hij) q) = 0 := by
  unfold distinctCupRowLinear
  rw [cupCapRowLinear_right (k := k) Ei Fi Ej (L).cupL ((L).capD n) ((L).capD_mem n)
    (rouquierPower (T.dot j hij) q) (rouquierPower_mem (T.dot_mem j hij) q)]
  change sign k _ • (T.distinctCupRowLinear hi hij hupper n
    (rouquierPower (T.dot i hi) p ▷ Ej) ≫ rouquierPower (T.dot j hij) q) = 0
  rw [T.distinctCupRow_leftDot hi hij hupper hh n p (by omega),
    ite_eq_right (by omega), Limits.zero_comp, smul_zero]
end RouquierFamily

namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) {Sc : Scalars D k}
  (M : RouquierMulticolour T Sc) {i j : I} (hne : i ≠ j)
  {a b c d e : X} (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d) (hupper : b + D.α i = e)

include M hne in
/-- The strict positive finite row test of Brundan–Ellis Lemma 7.1:
the actual quadratic cup word has coefficient exactly `t_ij` at the
shifted top boundary, and vanishes on every earlier finite row. -/
theorem distinctCupQuadraticRow_of_gt (hh : D.d i j < D.h i b) (n : ℕ)
    (hn : n < (D.h i d).toNat) :
    (leftUnitor (T.E j hij)).inv ≫ (T.loc i hi hupper).cupL ▷ T.E j hij ≫
      (associator (T.F i hi) (T.E i hi) (T.E j hij)).hom ≫
      T.F i hi ◁ (T.cross j i hi hij hj hji ≫ T.cross i j hj hji hi hij) ≫
      (associator (T.F i hi) (T.E i hi) (T.E j hij)).inv ≫
      (T.loc i hi hupper).capD n ▷ T.E j hij ≫ (leftUnitor (T.E j hij)).hom =
    (Sc.t i j : k) • (if n = (D.h i d - 1).toNat then 𝟙 (T.E j hij) else 0) := by
  change T.distinctCupRowLinear hi hij hupper n
    (T.cross j i hi hij hj hji ≫ T.cross i j hj hji hi hij) = _
  have hcast := D.dn_cast hne
  have hc : D.h i d = D.h i b - (D.dn i j : ℤ) := by
    rw [← hij, Datum.h, map_add]
    change D.h i b + D.h i (D.α j) = _
    rw [hcast, Datum.d]
    ring
  have hbpos : 0 < D.h i b := by have := D.d_nonneg hne; omega
  have hdpos : 0 < D.h i d := by omega
  have hlast : (D.h i b - 1).toNat = D.dn i j + (D.h i d - 1).toNat := by omega
  by_cases hd : D.d i j = 0
  · have hdji : D.d j i = 0 := (D.d_eq_zero_iff i j).mp hd
    have hd0 : D.dn i j = 0 := by omega
    rw [M.quadZero j i hne.symm hdji hi hij hj hji, map_smul]
    have hv := T.distinctCupRow_leftDot hi hij hupper hbpos n 0 (by omega)
    simp only [Nat.zero_add, rouquierPower_zero,
      TwoSupercategory.id_whiskerRight (R := k)] at hv
    have heq : (D.h i b - 1).toNat = n ↔ n = (D.h i d - 1).toNat := by omega
    rw [hv, Sc.t_symm_of_d_eq_zero j i hdji]
    simp only [heq]
  · have hdji : D.d j i ≠ 0 := fun h => hd ((D.d_eq_zero_iff j i).mp h)
    have hdpos' : 0 < D.dn i j := by have := D.d_nonneg hne; omega
    have hleading : T.distinctCupRowLinear hi hij hupper n
        (rouquierPower (T.dot i hi) (D.dn i j) ▷ T.E j hij) =
        if n = (D.h i d - 1).toNat then 𝟙 (T.E j hij) else 0 := by
      have hv := T.distinctCupRow_leftDot hi hij hupper hbpos n (D.dn i j) (by omega)
      have heq : (D.h i b - 1).toNat = D.dn i j + n ↔
          n = (D.h i d - 1).toNat := by omega
      simpa only [heq] using hv
    have hmiddle : T.distinctCupRowLinear hi hij hupper n
        (T.E i hi ◁ rouquierPower (T.dot j hij) (D.dn j i)) = 0 := by
      have hz := T.distinctCupRow_monomial_zero hi hij hupper hbpos n 0
        (D.dn j i) (by omega)
      simpa only [rouquierPower_zero, TwoSupercategory.id_whiskerRight (R := k),
        Category.id_comp] using hz
    rw [M.quadNe j i hne.symm hdji hi hij hj hji]
    simp only [map_add, map_smul, map_sum]
    rw [hmiddle, smul_zero, zero_add, hleading]
    have hinterior : (∑ p ∈ Finset.range (D.dn j i), ∑ q ∈ Finset.range (D.dn i j),
        Sc.s j i p q • T.distinctCupRowLinear hi hij hupper n
          (rouquierPower (T.dot i hi) q ▷ T.E j hij ≫
            T.E i hi ◁ rouquierPower (T.dot j hij) p)) = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      apply Finset.sum_eq_zero
      intro q hq
      have hq' := Finset.mem_Ioo.mp hq
      rw [T.distinctCupRow_monomial_zero hi hij hupper hbpos n q p (by omega), smul_zero]
    rw [hinterior, add_zero]
end RouquierFamily
end OddMath.SKM
