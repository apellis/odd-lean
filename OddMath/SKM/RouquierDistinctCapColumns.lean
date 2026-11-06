import OddMath.SKM.RouquierMulticolour
import OddMath.SKM.RouquierDotSlide

/-! # Finite columns of the distinct quadratic cap word

Brundan–Ellis Lemma 7.1, `pfL_b`: evaluate the actual upper dotted cup,
the two upward crossings and the inverse-defined upper cap. The
quadratic relations supply the leading coefficient; all middle-dot
terms below the shifted cap boundary vanish.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

private def cupCapLinear {a b c : B} (E : a ⟶ b) (H : b ⟶ c) (F : c ⟶ b)
    (cup : 𝟙 b ⟶ H ≫ F) (cap : H ≫ F ⟶ 𝟙 b) :
    End (E ≫ H) →ₗ[k] End E where
  toFun z := (rightUnitor E).inv ≫ E ◁ cup ≫ (associator E H F).inv ≫ z ▷ F ≫
    (associator E H F).hom ≫ E ◁ cap ≫ (rightUnitor E).hom
  map_add' z z' := by
    simp only [TwoSupercategory.add_whiskerRight (R := k), Preadditive.comp_add,
      Preadditive.add_comp]
  map_smul' r z := by
    simp only [TwoSupercategory.smul_whiskerRight (R := k), Linear.comp_smul,
      Linear.smul_comp, RingHom.id_apply]

private theorem cupCapLinear_right {a b c : B} (E : a ⟶ b) (H : b ⟶ c) (F : c ⟶ b)
    (cup : 𝟙 b ⟶ H ≫ F) (cap : H ≫ F ⟶ 𝟙 b) (x : End H) :
    cupCapLinear (k := k) E H F cup cap (E ◁ x) =
      (rightUnitor E).inv ≫ E ◁ (cup ≫ x ▷ F ≫ cap) ≫ (rightUnitor E).hom := by
  change (rightUnitor E).inv ≫ E ◁ cup ≫ (associator E H F).inv ≫ (E ◁ x) ▷ F ≫
    (associator E H F).hom ≫ E ◁ cap ≫ (rightUnitor E).hom = _
  rw [TwoSupercategory.whisker_assoc (R := k)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, TwoSupercategory.whiskerLeft_comp (R := k)]

private theorem cupCapLinear_left {a b c : B} (E : a ⟶ b) (H : b ⟶ c) (F : c ⟶ b)
    (cup : 𝟙 b ⟶ H ≫ F) (cap : H ≫ F ⟶ 𝟙 b) {p q : ZMod 2}
    (hcup : cup ∈ parity (R := k) _ _ q) (f : End E)
    (hf : f ∈ parity (R := k) _ _ p) (x : End H) :
    cupCapLinear (k := k) E H F cup cap (f ▷ H ≫ E ◁ x) =
      sign k (p * q) • (f ≫ cupCapLinear (k := k) E H F cup cap (E ◁ x)) := by
  have hs : E ◁ cup ≫ f ▷ (H ≫ F) =
      sign k (p * q) • (f ▷ 𝟙 b ≫ E ◁ cup) := by
    rw [TwoSupercategory.super_interchange (R := k) hf hcup, koszulSign_smul (R := k),
      smul_smul, sign_mul_self, one_smul]
  change (rightUnitor E).inv ≫ E ◁ cup ≫ (associator E H F).inv ≫
    (f ▷ H ≫ E ◁ x) ▷ F ≫ (associator E H F).hom ≫ E ◁ cap ≫
      (rightUnitor E).hom = _
  rw [TwoSupercategory.comp_whiskerRight (R := k)]
  simp only [Category.assoc]
  rw [← TwoSupercategory.associator_inv_naturality_left_assoc (R := k) f H F,
    reassoc_of% hs]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
  rw [← TwoSupercategory.rightUnitor_inv_naturality_assoc (R := k) f]
  rfl

namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) {Sc : Scalars D k}
  {i j : I} {a b c₀ c d : X}
  (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d) (hprev : c₀ + D.α i = c)
local notation "Ej" => T.E j hj
local notation "Ei" => T.E i hji
local notation "Fi" => T.F i hji
local notation "L" => T.loc i hprev hji

/-- Apply the given dotted upper cup and inverse-defined upper cap to
an endomorphism of the actual upward pair. -/
def distinctCapColumnLinear (n : ℕ) : End (Ej ≫ Ei) →ₗ[k] End Ej :=
  cupCapLinear (k := k) Ej Ei Fi ((L).cupD n) (L).capL

/-- Right dots add to the given cup exponent, retaining the entire
finite Kronecker coefficient at the shifted weight. -/
theorem distinctCapColumn_rightDot (hh : D.h i c < 0) (n p : ℕ)
    (hnp : n + p < (-D.h i c).toNat) :
    T.distinctCapColumnLinear hj hji hprev n (Ej ◁ rouquierPower (T.dot i hji) p) =
      if n + p = (-D.h i c - 1).toNat then 𝟙 Ej else 0 := by
  unfold distinctCapColumnLinear
  rw [cupCapLinear_right (k := k), ← Category.assoc ((L).cupD n) _ (L).capL,
    (L).cupD_powComp_whiskerRight, (L).cupD_capL hh hnp]
  split_ifs
  · simp only [TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp, Iso.inv_hom_id]
  · simp only [TwoSupercategory.whiskerLeft_zero (R := k), Limits.comp_zero, Limits.zero_comp]

/-- Every separated middle-dot term strictly below the shifted cap
boundary vanishes, with its actual homogeneous interchange sign. -/
theorem distinctCapColumn_monomial_zero (hh : D.h i c < 0) (n p q : ℕ)
    (hnp : n + p < (-D.h i c - 1).toNat) :
    T.distinctCapColumnLinear hj hji hprev n
      (rouquierPower (T.dot j hj) q ▷ Ei ≫ Ej ◁ rouquierPower (T.dot i hji) p) = 0 := by
  unfold distinctCapColumnLinear
  rw [cupCapLinear_left (k := k) Ej Ei Fi ((L).cupD n) (L).capL ((L).cupD_mem n)
    (rouquierPower (T.dot j hj) q) (rouquierPower_mem (T.dot_mem j hj) q)]
  change sign k _ • (rouquierPower (T.dot j hj) q ≫
    T.distinctCapColumnLinear hj hji hprev n (Ej ◁ rouquierPower (T.dot i hji) p)) = 0
  rw [T.distinctCapColumn_rightDot hj hji hprev hh n p (by omega),
    ite_eq_right (by omega), Limits.comp_zero, smul_zero]

end RouquierFamily
namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) {Sc : Scalars D k}
  (M : RouquierMulticolour T Sc) {i j : I} (hne : i ≠ j)
  {a b c₀ c d : X} (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d) (hprev : c₀ + D.α i = c)

include M hne in
/-- Every finite upper dotted-cup/double-cross/cap column is the
original leading scalar times the lower boundary Kronecker coefficient.
Both connected and disconnected colours use the actual quadratic
relations and the prescribed inverse-defined cap. -/
theorem distinctCapQuadraticColumn_of_neg (hh : D.h i a < 0) (n : ℕ)
    (hn : n < (-D.h i a).toNat) :
    (rightUnitor (T.E j hj)).inv ≫ T.E j hj ◁ (T.loc i hprev hji).cupD n ≫
      (associator (T.E j hj) (T.E i hji) (T.F i hji)).inv ≫
      (T.cross i j hj hji hi hij ≫ T.cross j i hi hij hj hji) ▷ T.F i hji ≫
      (associator (T.E j hj) (T.E i hji) (T.F i hji)).hom ≫
      T.E j hj ◁ (T.loc i hprev hji).capL ≫ (rightUnitor (T.E j hj)).hom =
    (Sc.t i j : k) • (if n = (-D.h i a - 1).toNat then 𝟙 (T.E j hj) else 0) := by
  change T.distinctCapColumnLinear hj hji hprev n
    (T.cross i j hj hji hi hij ≫ T.cross j i hi hij hj hji) = _
  have hcast := D.dn_cast hne
  have hc : D.h i c = D.h i a - (D.dn i j : ℤ) := by
    rw [← hj, Datum.h, map_add]
    change D.h i a + D.h i (D.α j) = _
    rw [hcast, Datum.d]
    ring
  have hcneg : D.h i c < 0 := by omega
  have hlast : (-D.h i c - 1).toNat = (-D.h i a - 1).toNat + D.dn i j := by omega
  by_cases hd : D.d i j = 0
  · have hd0 : D.dn i j = 0 := by omega
    rw [M.quadZero i j hne hd hj hji hi hij, map_smul]
    have hv := T.distinctCapColumn_rightDot hj hji hprev hcneg n 0 (by omega)
    simp only [Nat.add_zero, rouquierPower_zero,
      TwoSupercategory.whiskerLeft_id (R := k)] at hv
    rw [hv, hlast, hd0, Nat.add_zero]
  · have hdpos : 0 < D.dn i j := by have := D.d_nonneg hne; omega
    have hleading : T.distinctCapColumnLinear hj hji hprev n
        (T.E j hj ◁ rouquierPower (T.dot i hji) (D.dn i j)) =
        if n = (-D.h i a - 1).toNat then 𝟙 (T.E j hj) else 0 := by
      have hv := T.distinctCapColumn_rightDot hj hji hprev hcneg n (D.dn i j) (by omega)
      have heq : n + D.dn i j = (-D.h i c - 1).toNat ↔
          n = (-D.h i a - 1).toNat := by omega
      simpa only [heq] using hv
    have hmiddle : T.distinctCapColumnLinear hj hji hprev n
        (rouquierPower (T.dot j hj) (D.dn j i) ▷ T.E i hji) = 0 := by
      have hz := T.distinctCapColumn_monomial_zero hj hji hprev hcneg n 0
        (D.dn j i) (by omega)
      simpa only [rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k),
        Category.comp_id] using hz
    rw [M.quadNe i j hne hd hj hji hi hij]
    simp only [map_add, map_smul, map_sum]
    rw [hleading, hmiddle, smul_zero, add_zero]
    have hinterior : (∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
        Sc.s i j p q • T.distinctCapColumnLinear hj hji hprev n
          (rouquierPower (T.dot j hj) q ▷ T.E i hji ≫
            T.E j hj ◁ rouquierPower (T.dot i hji) p)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      apply Finset.sum_eq_zero
      intro q _
      have hp' := Finset.mem_Ioo.mp hp
      rw [T.distinctCapColumn_monomial_zero hj hji hprev hcneg n p q (by omega), smul_zero]
    rw [hinterior, add_zero]

end RouquierFamily
end OddMath.SKM
