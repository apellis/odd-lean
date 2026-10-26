import OddMath.SKM.RouquierMate
import OddMath.SKM.RouquierLeftCupCap

/-!
# Right transposition for the signed reflection

The right-counit bending equivalence and signed reversal of composition are
inputs to the reflection in Brundan, arXiv:1501.00350v1, Theorem 4.3 and
Brundan–Ellis, arXiv:1701.04133v2, Proposition 6.2, (6.6).
Only the even right adjunctions are used, on full Hom spaces including odd maps.
No left triangle, cyclicity, or faithfulness hypothesis is imposed.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

namespace SuperAdjunction
variable {a b : B} {E E' E'' : a ⟶ b} {F F' F'' : b ⟶ a}

/-- Bend a right-adjoint map down using its even counit. -/
def counitBend (A : SuperAdjunction (k := k) E F) (G : b ⟶ a) :
    (G ⟶ F) ≃ (G ≫ E ⟶ 𝟙 b) :=
  (Iso.homCongr (Iso.refl G) (leftUnitor F).symm).trans
    ((homPostAdjunction A).homEquiv G (𝟙 b)).symm

private theorem counitUnitor {C : Type u} [Bicategory.{w,v} C]
    {a b : C} (E : a ⟶ b) (F : b ⟶ a) (ε : F ≫ E ⟶ 𝟙 b) :
    Bicategory.whiskerRight (Bicategory.leftUnitor F).inv E ≫
      (Bicategory.associator (𝟙 b) F E).hom ≫
      Bicategory.whiskerLeft (𝟙 b) ε ≫ (Bicategory.rightUnitor (𝟙 b)).hom = ε := by
  bicategory

/-- The equivalence is precisely the prescribed counit composite. -/
theorem counitBend_apply (A : SuperAdjunction (k := k) E F)
    (G : b ⟶ a) (ψ : G ⟶ F) :
    A.counitBend G ψ = ψ ▷ E ≫ A.counit := by
  have h := congrArg Subtype.val (counitUnitor
    (Underlying2.hom1 (R := k) E) (Underlying2.hom1 (R := k) F)
    ⟨A.counit, A.counit_mem⟩)
  change (leftUnitor F).inv ▷ E ≫ (associator (𝟙 b) F E).hom ≫
    (𝟙 b) ◁ A.counit ≫ (rightUnitor (𝟙 b)).hom = A.counit at h
  dsimp [counitBend, Iso.homCongr, CategoryTheory.Adjunction.homEquiv,
    homPostAdjunction, homPostCounit, homPostComp, homPostTransform,
    homPostId, SuperNatTrans.toNatTrans, homPost]
  simp only [Category.id_comp, TwoSupercategory.comp_whiskerRight (R := k),
    Category.assoc, h]

/-- Right transpose characterized by bending down with the original counits. -/
def rightTranspose (A : SuperAdjunction (k := k) E F)
    (A' : SuperAdjunction (k := k) E' F') (f : E ⟶ E') : F' ⟶ F :=
  (A.counitBend F').symm (F' ◁ f ≫ A'.counit)

/-- The first bending identity, also for odd maps. -/
theorem rightTranspose_counit (A : SuperAdjunction (k := k) E F)
    (A' : SuperAdjunction (k := k) E' F') (f : E ⟶ E') :
    rightTranspose A A' f ▷ E ≫ A.counit = F' ◁ f ≫ A'.counit := by
  rw [← counitBend_apply]
  exact (A.counitBend F').apply_symm_apply _

/-- Uniqueness of the prescribed right transpose; no faithfulness assumption. -/
theorem rightTranspose_eq (A : SuperAdjunction (k := k) E F)
    (A' : SuperAdjunction (k := k) E' F') (f : E ⟶ E') (ψ : F' ⟶ F)
    (hψ : ψ ▷ E ≫ A.counit = F' ◁ f ≫ A'.counit) :
    rightTranspose A A' f = ψ := by
  apply (A.counitBend F').injective
  simpa only [counitBend_apply, rightTranspose_counit] using hψ.symm

/-- The explicit cup–map–cap formula used for parity and linearity. -/
theorem rightTranspose_apply (A : SuperAdjunction (k := k) E F)
    (A' : SuperAdjunction (k := k) E' F') (f : E ⟶ E') :
    rightTranspose A A' f =
      (rightUnitor F').inv ≫ F' ◁ A.unit ≫ (associator F' E F).inv ≫
        (F' ◁ f ≫ A'.counit) ▷ F ≫ (leftUnitor F).hom := by
  simp [rightTranspose, counitBend, Iso.homCongr, CategoryTheory.Adjunction.homEquiv,
    homPostAdjunction, homPostUnit, homPostComp, homPostTransform,
    homPostId, SuperNatTrans.toNatTrans, homPost, Category.assoc]

/-- Transposition preserves the degree, not just the even subcategory. -/
theorem rightTranspose_mem (A : SuperAdjunction (k := k) E F)
    (A' : SuperAdjunction (k := k) E' F') {p : ZMod 2} {f : E ⟶ E'}
    (hf : f ∈ parity (R := k) _ _ p) :
    rightTranspose A A' f ∈ parity (R := k) _ _ p := by
  rw [rightTranspose_apply]
  have hm := comp_mem (TwoSupercategory.whiskerLeft_mem F' hf) A'.counit_mem
  have h := comp_mem (inv_mem _ (TwoSupercategory.rightUnitor_hom_mem (R := k) F'))
    (comp_mem (TwoSupercategory.whiskerLeft_mem F' A.unit_mem)
      (comp_mem (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) F' E F))
        (comp_mem (TwoSupercategory.whiskerRight_mem F hm)
          (TwoSupercategory.leftUnitor_hom_mem (R := k) F))))
  simpa only [zero_add, add_zero] using h

/-- Even right adjunctions still give *signed* reversal of composition. -/
theorem rightTranspose_comp (A : SuperAdjunction (k := k) E F)
    (A' : SuperAdjunction (k := k) E' F')
    (A'' : SuperAdjunction (k := k) E'' F'')
    {p q : ZMod 2} {f : E ⟶ E'} {g : E' ⟶ E''}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ q) :
    rightTranspose A A'' (f ≫ g) =
      koszulSign q p • (rightTranspose A' A'' g ≫ rightTranspose A A' f) := by
  apply rightTranspose_eq
  simp only [TwoSupercategory.zsmul_whiskerRight (R := k),
    TwoSupercategory.comp_whiskerRight (R := k), Preadditive.zsmul_comp,
    Category.assoc, rightTranspose_counit]
  rw [← Category.assoc, TwoSupercategory.super_interchange
    (rightTranspose_mem A' A'' hg) hf, Preadditive.zsmul_comp, smul_smul,
    koszulSign_mul_self, one_smul, Category.assoc, rightTranspose_counit,
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]

/-- Transposition is linear on the full Hom space. -/
def rightTransposeLinear (A : SuperAdjunction (k := k) E F)
    (A' : SuperAdjunction (k := k) E' F') : (E ⟶ E') →ₗ[k] (F' ⟶ F) where
  toFun := rightTranspose A A'
  map_add' f g := by
    simp [rightTranspose_apply, TwoSupercategory.whiskerLeft_add (R := k),
      TwoSupercategory.add_whiskerRight (R := k), Preadditive.comp_add, Preadditive.add_comp]
  map_smul' c f := by
    simp [rightTranspose_apply, TwoSupercategory.whiskerLeft_smul,
      TwoSupercategory.smul_whiskerRight, Linear.comp_smul, Linear.smul_comp]

/-- The transpose of the identity is the identity. -/
theorem rightTranspose_id (A : SuperAdjunction (k := k) E F) :
    rightTranspose A A (𝟙 E) = 𝟙 F := by
  apply rightTranspose_eq
  simp only [TwoSupercategory.id_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp]

private theorem rightTranspose_powerSign (p : ZMod 2) (n : ℕ) :
    koszulSign p ((n : ZMod 2) * p) = koszulSign p p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, koszulSign_add_right, ih, pow_succ]

omit [∀ a b : B, Preadditive (a ⟶ b)] in
private theorem power_comm {a b : B} {X : a ⟶ b} (x : X ⟶ X) (n : ℕ) :
    x ≫ rouquierPower x n = rouquierPower x n ≫ x := by
  induction n with
  | zero => simp [rouquierPower]
  | succ n ih => simpa only [rouquierPower, ← Category.assoc] using congrArg (· ≫ x) ih

/-- The sign `q(n)` in reflection: each reversed pair of odd dots contributes once. -/
theorem rightTranspose_power (A : SuperAdjunction (k := k) E F)
    {p : ZMod 2} {x : E ⟶ E} (hx : x ∈ parity (R := k) _ _ p) (n : ℕ) :
    rightTranspose A A (rouquierPower x n) =
      koszulSign p p ^ (n.choose 2) • rouquierPower (rightTranspose A A x) n := by
  induction n with
  | zero => simp only [rouquierPower, rightTranspose_id, Nat.choose_zero_succ, pow_zero, one_smul]
  | succ n ih =>
    change rightTranspose A A (rouquierPower x n ≫ x) = _
    rw [rightTranspose_comp A A A (rouquierPower_mem hx n) hx, rightTranspose_powerSign,
      ih, Preadditive.comp_zsmul, smul_smul, power_comm]
    simp only [Nat.choose_succ_succ, Nat.choose_one_right, pow_add, rouquierPower]

end SuperAdjunction

namespace SuperRouquierLoc
variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}
  {p : ZMod 2} {h : ℤ} (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)

/-- The reflected dotted cap has exactly the coefficient `q(n)` of the
signed reflection proof. This uses the original dot and original right counit. -/
theorem rightTranspose_capD (n : ℕ) :
    rouquierPower (A₁.rightTranspose A₁ x₁) n ▷ E₁ ≫ A₁.counit =
      koszulSign p p ^ (n.choose 2) • L.capD n := by
  have he := A₁.rightTranspose_counit A₁ (rouquierPower x₁ n)
  rw [A₁.rightTranspose_power L.dot₁_mem n,
    TwoSupercategory.zsmul_whiskerRight (R := k), Preadditive.zsmul_comp] at he
  have hh := congrArg (fun z => koszulSign p p ^ (n.choose 2) • z) he
  simpa only [smul_smul, ← mul_pow, koszulSign_mul_self, one_pow, one_smul, capD] using hh

end SuperRouquierLoc
end OddMath.SKM
