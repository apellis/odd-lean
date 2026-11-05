import OddMath.SKM.RouquierBoundary
import OddMath.SKM.RouquierLeftCupCap

/-! # Local Rouquier data with a zero lower loop

Brundan–Ellis (1.13)–(1.14): the actual lower loop and double upward
cell may have zero identity without being a chosen zero-cell model.
The prescribed upper dotted-unit coefficients construct the full local
record at nonpositive height, including both orientations at height zero.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.SKM.RouquierZeroLocal
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a₀ a b : B} {E₀ : a₀ ⟶ a} {F₀ : a ⟶ a₀} {E : a ⟶ b} {F : b ⟶ a}
  (A₀ : SuperAdjunction (k := k) E₀ F₀) (A : SuperAdjunction (k := k) E F)
  (x : End E) (p : ZMod 2) (n : ℕ) (V : RouquierBoundary.Coefficients A x p n)

private theorem zeroMate : rouquierMate A₀ A (0 : End (E₀ ≫ E)) = 0 := by
  simp only [rouquierMate, TwoSupercategory.zero_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_zero (R := k), Limits.comp_zero, Limits.zero_comp]

private theorem lowerMap_zero (hLower : (𝟙 (F₀ ≫ E₀) : _ ⟶ _) = 0)
    {T : a ⟶ a} (f : F₀ ≫ E₀ ⟶ T) : f = 0 := by
  calc
    f = 𝟙 (F₀ ≫ E₀) ≫ f := (Category.id_comp f).symm
    _ = 0 := by rw [hLower, Limits.zero_comp]

/-- The actual boundary column inverse retains every given upper coefficient. -/
def negativeInverse (hLower : (𝟙 (F₀ ≫ E₀) : _ ⟶ _) = 0) :
    SuperSumInvFrom (k := k) (rouquierMate A₀ A (0 : End (E₀ ≫ E)))
      (fun j => A.unit ≫ rouquierPower x j ▷ F) p (fun j => (j : ZMod 2) * p) n where
  f' := 0
  g' := V.coeff
  f_mem := by rw [zeroMate]; exact Submodule.zero_mem _
  g_mem j := by
    simpa only [zero_add] using comp_mem A.unit_mem
      (TwoSupercategory.whiskerRight_mem F (rouquierPower_mem V.dot_mem j))
  f'_mem := Submodule.zero_mem _
  g'_mem := V.coeff_mem
  total := by
    rw [Limits.zero_comp, zero_add]
    simpa only [RouquierBoundary.cup] using V.total
  ff := by simpa only [Limits.comp_zero] using hLower.symm
  fg j hj := by rw [zeroMate, Limits.zero_comp]
  gf j hj := Limits.comp_zero
  gg j l hj hl := by simpa only [RouquierBoundary.cup] using V.entry j l hj hl

/-- Zero identities on the actual lower loop and double cell suffice for the local record. -/
def ofCoefficients (hLower : (𝟙 (F₀ ≫ E₀) : _ ⟶ _) = 0)
    (hDouble : (𝟙 (E₀ ≫ E) : _ ⟶ _) = 0) :
    SuperRouquierLoc A₀ A (0 : End E₀) x (0 : End (E₀ ≫ E)) p (-(n : ℤ)) where
  dot₁_mem := Submodule.zero_mem _
  dot₂_mem := V.dot_mem
  cross_mem := Submodule.zero_mem _
  slide_left := by
    simp only [Limits.comp_zero, Limits.zero_comp, smul_zero, sub_zero]
    exact hDouble.symm
  slide_right := by
    simp only [Limits.comp_zero, Limits.zero_comp, smul_zero, sub_zero]
    exact hDouble.symm
  invPos hh := by
    have hn : n = 0 := by omega
    subst n
    have hUpper : (0 : End (E ≫ F)) = 𝟙 (E ≫ F) := by
      simpa only [Finset.range_zero, Finset.sum_empty] using V.total
    refine {
      f' := 0
      g' := fun _ => 0
      f_mem := ?_
      g_mem := ?_
      f'_mem := Submodule.zero_mem _
      g'_mem := fun _ => Submodule.zero_mem _
      total := ?_
      ff := ?_
      fg := ?_
      gf := ?_
      gg := ?_ }
    · rw [zeroMate]; exact Submodule.zero_mem _
    · intro j
      have hz : (F₀ ◁ rouquierPower (0 : End E₀) j ≫ A₀.counit) = 0 :=
        lowerMap_zero hLower _
      rw [hz]
      exact Submodule.zero_mem _
    · simp only [Limits.comp_zero, Finset.sum_const_zero, add_zero]
      exact hLower.symm
    · simpa only [Limits.zero_comp] using hUpper
    · intro j hj; omega
    · intro j hj; omega
    · intro j l hj hl; omega
  invNeg _ := by
    simpa only [neg_neg, Int.toNat_natCast] using negativeInverse A₀ A x p n V hLower

end OddMath.SKM.RouquierZeroLocal
