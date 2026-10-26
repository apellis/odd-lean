import OddMath.SKM.RouquierHorizontalReflection
import OddMath.SKM.RouquierTransposeWhiskering

/-!
# Signed reflection of local Rouquier data

The same-height reflection of `SignedFTriangle.md` §4, (10)–(11), supporting
Brundan, arXiv:1501.00350v1, Theorem 4.3. Vertical composition is unchanged.
The crossing is multiplied by s = koszulSign p p and the nth window entry
by s^(n.choose 2). Both inverse orientations retain their prescribed entries.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k]

namespace SuperSumInvTo
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [Supercategory k C] {A B Z : C} {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
  {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}

/-- Rescale each row and its prescribed inverse by the same involutive integer. -/
def rescale (I : SuperSumInvTo (k := k) f g p q n)
    (s : ℤ) (d : ℕ → ℤ) (hs : s * s = 1) (hd : ∀ m, d m * d m = 1) :
    SuperSumInvTo (k := k) (s • f) (fun m => d m • g m) p q n where
  f' := s • I.f'
  g' m := d m • I.g' m
  f_mem := (parity (R := k) _ _ p).toAddSubgroup.zsmul_mem I.f_mem s
  g_mem m := (parity (R := k) _ _ (q m)).toAddSubgroup.zsmul_mem (I.g_mem m) (d m)
  f'_mem := (parity (R := k) _ _ p).toAddSubgroup.zsmul_mem I.f'_mem s
  g'_mem m := (parity (R := k) _ _ (q m)).toAddSubgroup.zsmul_mem (I.g'_mem m) (d m)
  total := by simpa only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    smul_smul, hs, hd, one_smul] using I.total
  ff := by simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    smul_smul, hs, one_smul, I.ff]
  fg m hm := by simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    I.fg m hm, smul_zero]
  gf m hm := by simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    I.gf m hm, smul_zero]
  gg m l hm hl := by
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, I.gg m l hm hl]
    split_ifs with e
    · subst l; rw [hd, one_smul]
    · exact smul_zero _
/-- Replace equal forward maps without transporting the prescribed inverse entries. -/
def copyMaps (I : SuperSumInvTo (k := k) f g p q n)
    (f₁ : A ⟶ B) (g₁ : ℕ → (A ⟶ Z)) (ef : f₁ = f) (eg : g₁ = g) :
    SuperSumInvTo (k := k) f₁ g₁ p q n where
  f' := I.f'
  g' := I.g'
  f_mem := by simpa only [ef] using I.f_mem
  g_mem m := by simpa only [eg] using I.g_mem m
  f'_mem := I.f'_mem
  g'_mem := I.g'_mem
  total := by simpa only [ef, eg] using I.total
  ff := by simpa only [ef] using I.ff
  fg m hm := by simpa only [ef, eg] using I.fg m hm
  gf m hm := by simpa only [ef, eg] using I.gf m hm
  gg m l hm hl := by simpa only [eg] using I.gg m l hm hl

end SuperSumInvTo

namespace SuperSumInvFrom
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [Supercategory k C] {A B Z : C} {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
  {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}

/-- Column rescaling preserves all augmented inverse equations, also at n = 0. -/
def rescale (I : SuperSumInvFrom (k := k) f g p q n)
    (s : ℤ) (d : ℕ → ℤ) (hs : s * s = 1) (hd : ∀ m, d m * d m = 1) :
    SuperSumInvFrom (k := k) (s • f) (fun m => d m • g m) p q n where
  f' := s • I.f'
  g' m := d m • I.g' m
  f_mem := (parity (R := k) _ _ p).toAddSubgroup.zsmul_mem I.f_mem s
  g_mem m := (parity (R := k) _ _ (q m)).toAddSubgroup.zsmul_mem (I.g_mem m) (d m)
  f'_mem := (parity (R := k) _ _ p).toAddSubgroup.zsmul_mem I.f'_mem s
  g'_mem m := (parity (R := k) _ _ (q m)).toAddSubgroup.zsmul_mem (I.g'_mem m) (d m)
  total := by simpa only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    smul_smul, hs, hd, one_smul] using I.total
  ff := by simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    smul_smul, hs, one_smul, I.ff]
  fg m hm := by simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    I.fg m hm, smul_zero]
  gf m hm := by simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    I.gf m hm, smul_zero]
  gg m l hm hl := by
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, I.gg m l hm hl]
    split_ifs with e
    · subst l; rw [hd, one_smul]
    · exact smul_zero _
/-- Replace equal forward maps without transporting the prescribed inverse entries. -/
def copyMaps (I : SuperSumInvFrom (k := k) f g p q n)
    (f₁ : B ⟶ A) (g₁ : ℕ → (Z ⟶ A)) (ef : f₁ = f) (eg : g₁ = g) :
    SuperSumInvFrom (k := k) f₁ g₁ p q n where
  f' := I.f'
  g' := I.g'
  f_mem := by simpa only [ef] using I.f_mem
  g_mem m := by simpa only [eg] using I.g_mem m
  f'_mem := I.f'_mem
  g'_mem := I.g'_mem
  total := by simpa only [ef, eg] using I.total
  ff := by simpa only [ef] using I.ff
  fg m hm := by simpa only [ef, eg] using I.fg m hm
  gf m hm := by simpa only [ef, eg] using I.gf m hm
  gg m l hm hl := by simpa only [eg] using I.gg m l hm hl

end SuperSumInvFrom

variable {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
omit [∀ a b : B, Preadditive (a ⟶ b)] in
/-- Horizontal opposition leaves ordered vertical powers unchanged. -/
theorem rouquierPower_horizontalOpposite {a b : B} {F : b ⟶ a} (x : F ⟶ F) (n : ℕ) :
    rouquierPower (B := HOpS B) (a := ⟨a⟩) (b := ⟨b⟩) x n =
      rouquierPower (B := B) x n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rouquierPower, ih]

namespace SuperRouquierLoc
variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}
  {p : ZMod 2} {h : ℤ} (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)

/-- The signed crossing prescribed by reflection. -/
def reflectedCross (_L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h) : F₂ ≫ F₁ ⟶ F₂ ≫ F₁ :=
  koszulSign p p • (A₁.comp A₂).rightTranspose (A₁.comp A₂) t

/-- The prescribed reflected cup–crossing–cap is s times the original mate. -/
theorem reflectedCross_mate :
    rouquierMate A₁.horizontalOpposite A₂.horizontalOpposite L.reflectedCross =
      koszulSign p p • rouquierMate A₁ A₂ t := by
  rw [reflectedCross, rouquierMate]
  simp only [TwoSupercategory.zsmul_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_zsmul (R := k), Preadditive.comp_zsmul,
    Preadditive.zsmul_comp]
  congr 1
  exact (rouquierMate_horizontalOpposite A₁ A₂ _).trans
    (mixedMateBend_symm_rightTranspose A₁ A₂ t)

/-- The original right slide transposes to the reflected left slide. -/
theorem reflected_slide_left :
    A₂.rightTranspose A₂ x₂ ▷ F₁ ≫ L.reflectedCross -
      koszulSign p p • (L.reflectedCross ≫ F₂ ◁ A₁.rightTranspose A₁ x₁) = 𝟙 _ := by
  have e := congrArg ((A₁.comp A₂).rightTransposeLinear (A₁.comp A₂)) L.slide_right
  simp only [map_sub, map_zsmul] at e
  change (A₁.comp A₂).rightTranspose (A₁.comp A₂) (t ≫ E₁ ◁ x₂) -
    koszulSign p p • (A₁.comp A₂).rightTranspose (A₁.comp A₂) (x₁ ▷ E₂ ≫ t) =
      (A₁.comp A₂).rightTranspose (A₁.comp A₂) (𝟙 _) at e
  rw [SuperAdjunction.rightTranspose_comp _ _ _ L.cross_mem
      (TwoSupercategory.whiskerLeft_mem E₁ L.dot₂_mem),
    SuperAdjunction.rightTranspose_comp _ _ _
      (TwoSupercategory.whiskerRight_mem E₂ L.dot₁_mem) L.cross_mem,
    SuperAdjunction.rightTranspose_whiskerLeft,
    SuperAdjunction.rightTranspose_whiskerRight, SuperAdjunction.rightTranspose_id] at e
  simpa only [reflectedCross, Preadditive.comp_zsmul, Preadditive.zsmul_comp] using e

/-- The original left slide transposes to the reflected right slide. -/
theorem reflected_slide_right :
    L.reflectedCross ≫ A₂.rightTranspose A₂ x₂ ▷ F₁ -
      koszulSign p p • (F₂ ◁ A₁.rightTranspose A₁ x₁ ≫ L.reflectedCross) = 𝟙 _ := by
  have e := congrArg ((A₁.comp A₂).rightTransposeLinear (A₁.comp A₂)) L.slide_left
  simp only [map_sub, map_zsmul] at e
  change (A₁.comp A₂).rightTranspose (A₁.comp A₂) (E₁ ◁ x₂ ≫ t) -
    koszulSign p p • (A₁.comp A₂).rightTranspose (A₁.comp A₂) (t ≫ x₁ ▷ E₂) =
      (A₁.comp A₂).rightTranspose (A₁.comp A₂) (𝟙 _) at e
  rw [SuperAdjunction.rightTranspose_comp _ _ _
      (TwoSupercategory.whiskerLeft_mem E₁ L.dot₂_mem) L.cross_mem,
    SuperAdjunction.rightTranspose_comp _ _ _ L.cross_mem
      (TwoSupercategory.whiskerRight_mem E₂ L.dot₁_mem),
    SuperAdjunction.rightTranspose_whiskerLeft,
    SuperAdjunction.rightTranspose_whiskerRight, SuperAdjunction.rightTranspose_id] at e
  simpa only [reflectedCross, Preadditive.comp_zsmul, Preadditive.zsmul_comp] using e

/-- Reflected local data at the same height, with both signed slides and both
finite augmented inverses derived from the prescribed original components. -/
def horizontalReflection :
    SuperRouquierLoc A₁.horizontalOpposite A₂.horizontalOpposite
      (A₁.rightTranspose A₁ x₁) (A₂.rightTranspose A₂ x₂) L.reflectedCross p h where
  dot₁_mem := A₁.rightTranspose_mem A₁ L.dot₁_mem
  dot₂_mem := A₂.rightTranspose_mem A₂ L.dot₂_mem
  cross_mem := (parity (R := k) _ _ p).toAddSubgroup.zsmul_mem
    ((A₁.comp A₂).rightTranspose_mem (A₁.comp A₂) L.cross_mem) _
  slide_left := L.reflected_slide_left
  slide_right := L.reflected_slide_right
  invPos hh := by
    have I := (L.invPos hh).rescale (koszulSign p p)
      (fun n => koszulSign p p ^ (n.choose 2)) (koszulSign_mul_self p p)
      (fun n => by rw [← mul_pow, koszulSign_mul_self, one_pow])
    refine I.copyMaps _ _ L.reflectedCross_mate ?_
    funext n
    simp only [rouquierPower_horizontalOpposite]
    exact L.rightTranspose_capD n
  invNeg hh := by
    have I := (L.invNeg hh).rescale (koszulSign p p)
      (fun n => koszulSign p p ^ (n.choose 2)) (koszulSign_mul_self p p)
      (fun n => by rw [← mul_pow, koszulSign_mul_self, one_pow])
    refine I.copyMaps _ _ L.reflectedCross_mate ?_
    funext n
    simp only [rouquierPower_horizontalOpposite]
    exact L.rightTranspose_cupD n

/-- Reflection transports the nilpotent crossing square. -/
theorem reflectedCross_square (ht : t ≫ t = 0) :
    L.reflectedCross ≫ L.reflectedCross = 0 := by
  have e := congrArg ((A₁.comp A₂).rightTransposeLinear (A₁.comp A₂)) ht
  rw [map_zero] at e
  change (A₁.comp A₂).rightTranspose (A₁.comp A₂) (t ≫ t) = 0 at e
  rw [SuperAdjunction.rightTranspose_comp _ _ _ L.cross_mem L.cross_mem] at e
  have e' := congrArg (fun z => koszulSign p p • z) e
  simpa only [reflectedCross, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    smul_smul, koszulSign_mul_self, one_smul, smul_zero] using e'

/-- The reflected positive principal inverse retains its prescribed formula. -/
theorem horizontalReflection_invPos_f' (hh : 0 ≤ h) :
    (L.horizontalReflection.invPos hh).f' = koszulSign p p • (L.invPos hh).f' := by
  rfl

/-- Every reflected positive window entry, including outside the finite window. -/
theorem horizontalReflection_invPos_g' (hh : 0 ≤ h) (n : ℕ) :
    (L.horizontalReflection.invPos hh).g' n =
      koszulSign p p ^ (n.choose 2) • (L.invPos hh).g' n := by
  rfl

/-- The reflected negative principal inverse retains its prescribed formula. -/
theorem horizontalReflection_invNeg_f' (hh : h ≤ 0) :
    (L.horizontalReflection.invNeg hh).f' = koszulSign p p • (L.invNeg hh).f' := by
  rfl

/-- Every reflected negative window entry, including outside the finite window. -/
theorem horizontalReflection_invNeg_g' (hh : h ≤ 0) (n : ℕ) :
    (L.horizontalReflection.invNeg hh).g' n =
      koszulSign p p ^ (n.choose 2) • (L.invNeg hh).g' n := by
  rfl

end SuperRouquierLoc
end OddMath.SKM
