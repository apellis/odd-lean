import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPrincipalInverseCoordinates
import OddMath.SKM.AugmentedInverseEvaluation
import OddMath.SKM.AugmentedInverseNaturality

/-! # Coordinates of the chosen reservoir finite inverse windows

For SwappedHomInversion §4 (7), every finite chosen `g'` is forced by
its forward matrix. These equations retain the supported weight-to-content
charts in both orientations, without a new inverse comparison premise.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
universe u
private theorem identity_obj {k : Type u} [CommRing k]
    (A : PiSCat.{u, u, u + 1} k) (V : A) :
    (𝟙 A : Superfunctor k A A).obj V = V := rfl

section Detection
variable {k : Type u} [CommRing k] {C : Type*} [Category C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {A B Z : C} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
private theorem row_window_square {A' B' : C} {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    {f' : A' ⟶ B'} {g' : ℕ → (A' ⟶ Z)}
    (K : SKM.SuperSumInvTo (k := k) f' g' p q n) (j : ℕ) (hj : j < n) (s : Z ⟶ A)
    (a : A ⟶ A') (b : B ⟶ B') (hf : a ≫ f' = f ≫ b)
    (hg : ∀ r, r < n → a ≫ g' r = g r)
    (hs : s ≫ f = 0) (hsg : ∀ r, r < n → s ≫ g r = if j = r then 𝟙 Z else 0) :
    s ≫ a = K.g' j := by
  apply K.hom_ext
  · rw [Category.assoc, hf, ← Category.assoc, hs, Limits.zero_comp, K.gf j hj]
  · intro r hr
    rw [Category.assoc, hg r hr, hsg r hr, K.gg j r hj hr]

private theorem column_window_square {A' B' : C} {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    {f' : B' ⟶ A'} {g' : ℕ → (Z ⟶ A')}
    (K : SKM.SuperSumInvFrom (k := k) f' g' p q n) (j : ℕ) (hj : j < n) (s : A ⟶ Z)
    (a : A ≅ A') (b : B ≅ B') (hf : f ≫ a.hom = b.hom ≫ f')
    (hg : ∀ r, r < n → g r ≫ a.hom = g' r)
    (hs : f ≫ s = 0) (hgs : ∀ r, r < n → g r ≫ s = if r = j then 𝟙 Z else 0) :
    s = a.hom ≫ K.g' j := by
  apply (cancel_epi a.inv).mp
  rw [← Category.assoc a.inv a.hom, a.inv_hom_id, Category.id_comp]
  apply K.hom_ext
  · have he : f' ≫ a.inv = b.inv ≫ f := by
      apply (cancel_mono a.hom).mp
      simp only [Category.assoc, a.inv_hom_id, Category.comp_id]
      rw [hf, ← Category.assoc, b.inv_hom_id, Category.id_comp]
    rw [← Category.assoc f' a.inv, he, Category.assoc b.inv f,
      hs, Limits.comp_zero, K.fg j hj]
  · intro r hr
    rw [← hg r hr, Category.assoc, a.hom_inv_id_assoc,
      hgs r hr, hg r hr, K.gg r j hr hj]
end Detection

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (M : ELVWeightProduct D Sc cutoff N Λ x₁) (δ : WeightBlocks D Λ x₁)
local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The chosen positive-weight finite cap inverse column on an output block. -/
def elvChosenCapWindow (hh : 0 ≤ D.h i x₁) (j : ℕ) :=
  ((((W).loc i h₁ h₂).invPos hh).g' j).total M δ

/-- The chosen negative-weight finite unit inverse row on an output block. -/
def elvChosenUnitWindow (hh : D.h i x₁ ≤ 0) (j : ℕ) :=
  ((((W).loc i h₁ h₂).invNeg hh).g' j).total M δ

variable (β : WeightBlocks D Λ x₀)
local notation "δ₁" => blockSucc D Λ i h₁ β
local notation "δ₂" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "hS" => elvWeightMixedSource_obj D Sc cutoff N i i Λ h₁ h₁ β M
local notation "hT" => elvWeightMixedTarget_obj D Sc cutoff N i i Λ h₁ h₂ h₁ h₂ β M

local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
local notation "CapField" r => elvF D Sc cutoff N i Λ h₁ ◁
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) r ≫
    elvActionCounit D Sc cutoff N i Λ h₁
local notation "UnitField" r => elvActionUnit D Sc cutoff N i Λ h₂ ≫
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) r ▷
    elvF D Sc cutoff N i Λ h₂

/-- Every finite weight cap inverse column has the prescribed content coordinate. -/
theorem elvCapWindow_coordinates (hh : 0 ≤ D.h i x₁)
    (L : SKM.SuperSumInvTo (k := k) (φ) (fun r => CapField r)
      (D.parity i) (fun r => (r : ZMod 2) * D.parity i) (D.h i x₁).toNat)
    (j : ℕ) (hj : j < (D.h i x₁).toNat) :
    (L.g' j).total M δ₁ ≫ eqToHom hS =
      (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j := by
  let J := L.at M
  let K := elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
  have hcount := contentCapCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ₁
  have hj' : j < contentCapCount D cutoff i δ₁.1 := by simpa only [hcount] using hj
  apply row_window_square K j hj' ((L.g' j).total M δ₁) (eqToHom hS) (eqToHom hT)
  · exact (elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M).symm
  · intro r _
    exact (elvWeightCapPower_localCoordinates D Sc cutoff N i Λ h₁ β M r).symm
  · have he := (CategoryTheory.Pi.eval _ δ₁).congr_map (J.gf j hj)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at he
    dsimp only [J, CategoryTheory.Pi.eval] at he
    simpa only [SKM.SuperSumInvTo.at_g', Superfunctor.id, Functor.id_obj] using he
  · intro r hr
    have hr' : r < (D.h i x₁).toNat := by simpa only [hcount] using hr
    have he := (CategoryTheory.Pi.eval _ δ₁).congr_map (J.gg j r hj hr')
    split_ifs at he ⊢
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at he
      dsimp only [J, CategoryTheory.Pi.eval] at he
      simp only [identity_obj] at he
      simpa only [SKM.SuperSumInvTo.at_g', Superfunctor.id, Functor.id_obj] using he
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at he
      dsimp only [J, CategoryTheory.Pi.eval] at he
      simp only [identity_obj] at he
      simpa only [SKM.SuperSumInvTo.at_g', Superfunctor.id, Functor.id_obj] using he

/-- Every finite weight unit inverse row has the prescribed content coordinate. -/
theorem elvUnitWindow_coordinates (hh : D.h i x₁ ≤ 0)
    (L : SKM.SuperSumInvFrom (k := k) (φ) (fun r => UnitField r)
      (D.parity i) (fun r => (r : ZMod 2) * D.parity i) (-D.h i x₁).toNat)
    (j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    (L.g' j).total M δ₁ =
      eqToHom hT ≫ (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j := by
  let J := L.at M
  let K := elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
  have hcount := contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ₁
  have hj' : j < contentUnitCount D cutoff i δ₁.1 := by simpa only [hcount] using hj
  apply column_window_square K j hj' ((L.g' j).total M δ₁) (eqToIso hT) (eqToIso hS)
  · exact elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M
  · intro r _
    exact elvWeightUnitPower_localCoordinates D Sc cutoff N i Λ h₁ h₂ β M r
  · have he := (CategoryTheory.Pi.eval _ δ₁).congr_map (J.fg j hj)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at he
    dsimp only [J, CategoryTheory.Pi.eval] at he
    simpa only [SKM.SuperSumInvFrom.at_g', Superfunctor.id, Functor.id_obj] using he
  · intro r hr
    have hr' : r < (-D.h i x₁).toNat := by simpa only [hcount] using hr
    have he := (CategoryTheory.Pi.eval _ δ₁).congr_map (J.gg r j hr' hj)
    split_ifs at he ⊢
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at he
      dsimp only [J, CategoryTheory.Pi.eval] at he
      simp only [identity_obj] at he
      simpa only [SKM.SuperSumInvFrom.at_g', Superfunctor.id, Functor.id_obj] using he
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at he
      dsimp only [J, CategoryTheory.Pi.eval] at he
      simp only [identity_obj] at he
      simpa only [SKM.SuperSumInvFrom.at_g', Superfunctor.id, Functor.id_obj] using he

/-- The literal chosen positive finite inverse column retains the content chart. -/
theorem elvChosenCapWindow_coordinates (hh : 0 ≤ D.h i x₁)
    (j : ℕ) (hj : j < (D.h i x₁).toNat) :
    elvChosenCapWindow D Sc cutoff N Λ hcutoff i h₁ h₂ M δ₁ hh j ≫ eqToHom hS =
      (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j :=
  elvCapWindow_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
    (((W).loc i h₁ h₂).invPos hh) j hj

/-- The literal chosen negative finite inverse row retains the content chart. -/
theorem elvChosenUnitWindow_coordinates (hh : D.h i x₁ ≤ 0)
    (j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    elvChosenUnitWindow D Sc cutoff N Λ hcutoff i h₁ h₂ M δ₁ hh j =
      eqToHom hT ≫ (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j :=
  elvUnitWindow_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
    (((W).loc i h₁ h₂).invNeg hh) j hj

end OddMath.QuiverHecke.ELVOld
