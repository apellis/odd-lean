import OddMath.SKM.RouquierReflectedCupCap
import OddMath.SKM.RouquierReflectedBraid
import OddMath.SKM.RouquierPitchfork

/-!
# The canonical F triangle by signed horizontal reflection

The scalar calculation in `SignedFTriangle.md`, §§5–6, is symbolic at every
integer height. The local triangle uses only the original right adjunctions,
augmented inverses, crossing squares and braid (Brundan, arXiv:1501.00350v1,
Theorem 4.3, reflection step).
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory

private theorem reflection_power_sign (p : ZMod 2) (n : ℕ) :
    koszulSign p p ^ n = koszulSign (p * (n : ZMod 2)) (p * (n : ZMod 2)) := by
  have diag (q : ZMod 2) : koszulSign (p * q) (p * q) = koszulSign p (q * p) := by
    fin_cases p <;> fin_cases q <;> decide
  rw [diag]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, koszulSign_add_right,
      pow_succ, ih]

private theorem reflection_choose_pair (p : ZMod 2) (n : ℕ) :
    koszulSign p p ^ ((n + 1).choose 2) * koszulSign p p ^ (n.choose 2) =
      koszulSign p p ^ n := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_add, mul_assoc,
    ← mul_pow, koszulSign_mul_self, one_pow, mul_one]

/-- The product of the canonical reflected cup and cap scalars at adjacent heights. -/
theorem reflection_triangle_scalar (p : ZMod 2) (h : ℤ) :
    (if 0 < h + 2 then koszulSign p p ^ ((h + 2 - 1).toNat.choose 2)
      else koszulSign p p * koszulSign p p ^ ((-(h + 2)).toNat.choose 2)) *
    (if h < 0 then koszulSign p p ^ ((-h - 1).toNat.choose 2)
      else koszulSign p p * koszulSign p p ^ (h.toNat.choose 2)) =
    koszulSign (p * ((h + 1 : ℤ) : ZMod 2)) (p * ((h + 1 : ℤ) : ZMod 2)) := by
  by_cases hh : 0 ≤ h
  · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    have hn : (h + 2 - 1).toNat = h.toNat + 1 := by omega
    rw [hn, ← mul_left_comm, reflection_choose_pair, ← pow_succ', reflection_power_sign]
    have he : ((h.toNat + 1 : ℕ) : ℤ) = h + 1 := by omega
    rw [← Int.cast_natCast, he]
  · by_cases hb : h = -1
    · subst h
      norm_num
    · have hn : (-h - 1).toNat = (-(h + 2)).toNat + 1 := by omega
      rw [ite_eq_right (by omega), ite_eq_left (by omega), hn]
      rw [mul_assoc, mul_comm (koszulSign p p ^ _) (koszulSign p p ^ _),
        reflection_choose_pair, ← pow_succ', reflection_power_sign]
      have he : (((-(h + 2)).toNat + 1 : ℕ) : ℤ) = -(h + 1) := by omega
      have hc : (((-(h + 2)).toNat + 1 : ℕ) : ZMod 2) = ((h + 1 : ℤ) : ZMod 2) := by
        rw [← Int.cast_natCast, he, Int.cast_neg]
        generalize ((h + 1 : ℤ) : ZMod 2) = q
        fin_cases q <;> decide
      rw [hc]

universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
namespace SuperRouquierLoc
variable {a b c d : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
  {E₂ : b ⟶ c} {F₂ : c ⟶ b} {E₃ : c ⟶ d} {F₃ : d ⟶ c}
  {A₁ : SuperAdjunction (k := k) E₁ F₁}
  {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {A₃ : SuperAdjunction (k := k) E₃ F₃}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {x₃ : E₃ ⟶ E₃}
  {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {t' : E₂ ≫ E₃ ⟶ E₂ ≫ E₃}
  {p : ZMod 2} {h h' : ℤ}
  (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)
  (U : SuperRouquierLoc A₂ A₃ x₂ x₃ t' p h')

/-- The canonical F composite, with its prescribed scalar at every height. -/
theorem leftAdj_triangle_F (hw : h' = h + 2)
    (hsq : t ≫ t = 0) (hsq' : t' ≫ t' = 0)
    (hB : E₁ ◁ t' ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom) ≫ E₁ ◁ t' =
      ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom) ≫
      E₁ ◁ t' ≫ ((associator E₁ E₂ E₃).inv ≫ t ▷ E₃ ≫ (associator E₁ E₂ E₃).hom)) :
    (leftUnitor F₂).inv ≫ U.cupL ▷ F₂ ≫ (associator F₂ E₂ F₂).hom ≫
      F₂ ◁ L.capL ≫ (rightUnitor F₂).hom =
    (koszulSign (p * ((h + 1 : ℤ) : ZMod 2)) (p * ((h + 1 : ℤ) : ZMod 2)) *
      (if h < 0 then 1 else koszulSign p p)) • 𝟙 F₂ := by
  have he :
      (leftUnitor F₂).inv ≫
        whiskerRight (B := B) (show 𝟙 c ⟶ F₂ ≫ E₂ from U.horizontalReflection.cupL) F₂ ≫
        (associator F₂ E₂ F₂).hom ≫
        whiskerLeft (B := B) F₂ (show E₂ ≫ F₂ ⟶ 𝟙 b from L.horizontalReflection.capL) ≫
        (rightUnitor F₂).hom = (if h < 0 then 1 else koszulSign p p) • 𝟙 F₂ := by
    by_cases hh : h < 0
    · rw [ite_eq_left hh, one_smul]
      exact L.horizontalReflection.leftAdj_triangle_E_of_neg (B := HOpS B)
        U.horizontalReflection hw hh (L.reflectedCross_square hsq)
        (U.reflectedCross_square hsq') (L.reflectedCross_braid U hB)
    · rw [ite_eq_right hh]
      exact L.horizontalReflection.leftAdj_triangle_E_of_nonneg (B := HOpS B)
        U.horizontalReflection hw (by omega) (L.reflectedCross_square hsq)
        (U.reflectedCross_square hsq') (L.reflectedCross_braid U hB)
  rw [U.horizontalReflection_cupL, L.horizontalReflection_capL] at he
  simp only [TwoSupercategory.zsmul_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_zsmul (R := k), Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, smul_smul] at he
  have hc := reflection_triangle_scalar p h
  rw [← hw] at hc
  rw [mul_comm, hc] at he
  have he' := congrArg (fun z =>
    koszulSign (p * ((h + 1 : ℤ) : ZMod 2)) (p * ((h + 1 : ℤ) : ZMod 2)) • z) he
  simpa only [smul_smul, koszulSign_mul_self, one_smul] using he'
end SuperRouquierLoc

namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D)

/-- The canonical lowering-strand zigzag at every source height. -/
theorem leftZigF_eq (i : I) {x y : X} (e : x + D.α i = y) :
    T.leftZigF i e = (koszulSign (leftAdjParity D i x) (leftAdjParity D i x) *
      (if D.h i x < 0 then 1 else koszulSign (D.parity i) (D.parity i))) • 𝟙 (T.F i e) := by
  have hw : D.h i y = D.h i x + 2 := by
    rw [← e]
    simp [Datum.h, Datum.α, map_add, D.cd.coroot_root_self]
  have ht := (T.loc i (sub_add_cancel x (D.α i)) e).leftAdj_triangle_F
    (T.loc i e rfl) hw (T.square i (sub_add_cancel x (D.α i)) e)
    (T.square i e rfl) (T.braid i (sub_add_cancel x (D.α i)) e rfl)
  simpa only [leftAdjParity, Int.cast_add, Int.cast_one, leftZigF, leftCup, leftCap] using ht

/-- Both canonical triangles have the common involutive unit required by the
shifted left-adjunction API; no left-triangle hypothesis is needed. -/
theorem leftZigzags : T.LeftZigzags :=
  T.leftZigzags_iff_leftZigF.mpr (fun i _ _ e => T.leftZigF_eq i e)

/-- Normalize only the cap using the existing common-unit construction. -/
def leftAdjoints : RouquierLeftAdjoints (k := k) T :=
  T.leftAdjointsOfZigzags T.leftZigzags
end RouquierFamily
end OddMath.SKM
