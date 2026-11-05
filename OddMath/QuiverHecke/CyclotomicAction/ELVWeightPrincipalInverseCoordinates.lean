import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierFamily
import OddMath.SKM.AugmentedInverseEvaluation
import OddMath.SKM.AugmentedInverseNaturality

/-! # Coordinates of the chosen reservoir principal inverses

The reservoir closure uses the principal inverse selected by the actual
Rouquier family. Its finite forward matrix determines this principal,
independently of the choices used to construct the local record.
These coordinates attach that chosen inverse to the represented matrices
used in the integer-degree calculation of ReservoirClosureDegree.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
universe u
section Detection
variable {k : Type u} [CommRing k] {C : Type*} [Category C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {A B Z : C} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
private theorem column_principal_eq {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (K : SKM.SuperSumInvFrom (k := k) f g p q n) (s : A ⟶ B)
    (hs : f ≫ s = 𝟙 B) (hg : ∀ r, r < n → g r ≫ s = 0) : s = K.f' := by
  apply K.hom_ext
  · exact hs.trans K.ff.symm
  · intro r hr
    exact (hg r hr).trans (K.gf r hr).symm
private theorem row_principal_square {A' B' : C} {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    {f' : A' ⟶ B'} {g' : ℕ → (A' ⟶ Z)}
    (K : SKM.SuperSumInvTo (k := k) f' g' p q n) (s : B ⟶ A)
    (a : A ⟶ A') (b : B ⟶ B') (hf : a ≫ f' = f ≫ b)
    (hg : ∀ r, r < n → a ≫ g' r = g r)
    (hs : s ≫ f = 𝟙 B) (hsg : ∀ r, r < n → s ≫ g r = 0) :
    s ≫ a = b ≫ K.f' := by
  apply K.hom_ext
  · rw [Category.assoc, hf, ← Category.assoc, hs, Category.id_comp,
      Category.assoc, K.ff, Category.comp_id]
  · intro r hr
    rw [Category.assoc, hg r hr, hsg r hr, Category.assoc, K.fg r hr, Limits.comp_zero]

private theorem column_principal_square {A' B' : C} {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    {f' : B' ⟶ A'} {g' : ℕ → (Z ⟶ A')}
    (K : SKM.SuperSumInvFrom (k := k) f' g' p q n) (s : A ⟶ B)
    (a : A ≅ A') (b : B ≅ B') (hf : f ≫ a.hom = b.hom ≫ f')
    (hg : ∀ r, r < n → g r ≫ a.hom = g' r)
    (hs : f ≫ s = 𝟙 B) (hgs : ∀ r, r < n → g r ≫ s = 0) :
    s ≫ b.hom = a.hom ≫ K.f' := by
  apply (cancel_epi a.inv).mp
  rw [← Category.assoc a.inv a.hom, a.inv_hom_id, Category.id_comp]
  apply column_principal_eq K
  · have he : f' ≫ a.inv = b.inv ≫ f := by
      apply (cancel_mono a.hom).mp
      simp only [Category.assoc, a.inv_hom_id, Category.comp_id]
      rw [hf, ← Category.assoc, b.inv_hom_id, Category.id_comp]
    rw [← Category.assoc f' a.inv, he, Category.assoc b.inv f,
      ← Category.assoc f s, hs, Category.id_comp, b.inv_hom_id]
  · intro r hr
    rw [← hg r hr, Category.assoc, a.hom_inv_id_assoc,
      ← Category.assoc, hgs r hr, Limits.zero_comp]

end Detection

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (M : ELVWeightProduct D Sc cutoff N Λ x₁) (δ : WeightBlocks D Λ x₁)
local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The literal chosen principal at an input family and output block. -/
def elvChosenCapPrincipal (hh : 0 ≤ D.h i x₁) :=
  ((((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invPos hh).f').total M δ

/-- The literal chosen negative principal at an input family and output block. -/
def elvChosenUnitPrincipal (hh : D.h i x₁ ≤ 0) :=
  ((((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invNeg hh).f').total M δ

variable (β : WeightBlocks D Λ x₀)
local notation "δ₁" => blockSucc D Λ i h₁ β
local notation "δ₂" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "hS" => elvWeightMixedSource_obj D Sc cutoff N i i Λ h₁ h₁ β M
local notation "hT" => elvWeightMixedTarget_obj D Sc cutoff N i i Λ h₁ h₂ h₁ h₂ β M

/-- The constructed canonical content cap inverse at this supported weight block. -/
def elvContentCapInverseAtWeight (hh : 0 ≤ D.h i x₁) :=
  Classical.choice (contentTargetsLocalInverseTo_nonempty D Sc cutoff N β.1 i δ₁.1 δ₂.1
    (elvBlockSucc_content_eq D i Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₂ δ₁) (M δ₁) (by
      rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ (hcutoff i) δ₁]
      exact neg_nonpos.mpr hh))

/-- The constructed canonical content unit inverse at this supported weight block. -/
def elvContentUnitInverseAtWeight (hh : D.h i x₁ ≤ 0) :=
  Classical.choice (contentTargetsLocalInverseFrom_nonempty D Sc cutoff N β.1 i δ₁.1 δ₂.1
    (elvBlockSucc_content_eq D i Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₂ δ₁) (M δ₁) (by
      rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ (hcutoff i) δ₁]
      exact neg_nonneg.mpr hh))

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

/-- Any cap inverse of the prescribed forward matrix has these coordinates. -/
theorem elvCapPrincipal_coordinates (hh : 0 ≤ D.h i x₁)
    (L : SKM.SuperSumInvTo (k := k) (φ) (fun r => CapField r)
      (D.parity i) (fun r => (r : ZMod 2) * D.parity i) (D.h i x₁).toNat) :
    L.f'.total M δ₁ ≫ eqToHom hS =
      eqToHom hT ≫ (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).f' := by
  let J := L.at M
  let K := elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
  apply row_principal_square K (L.f'.total M δ₁) (eqToHom hS) (eqToHom hT)
  · exact (elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M).symm
  · intro r _
    exact (elvWeightCapPower_localCoordinates D Sc cutoff N i Λ h₁ β M r).symm
  · have hj := congrFun J.ff δ₁
    dsimp only [J] at hj
    simpa only [SKM.SuperSumInvTo.at_f', CategoryTheory.Pi.comp_apply,
      CategoryTheory.Pi.id_apply, Categorification.TwoRep.pi_zero_apply] using hj
  · intro r hr
    have hcount := contentCapCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ₁
    have hr' : r < (D.h i x₁).toNat := by simpa only [hcount] using hr
    have hj := (CategoryTheory.Pi.eval _ δ₁).congr_map (J.fg r hr')
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at hj
    dsimp only [J, CategoryTheory.Pi.eval] at hj
    simpa only [SKM.SuperSumInvTo.at_f'] using hj

/-- Any unit inverse of the prescribed forward matrix has these coordinates. -/
theorem elvUnitPrincipal_coordinates (hh : D.h i x₁ ≤ 0)
    (L : SKM.SuperSumInvFrom (k := k) (φ) (fun r => UnitField r)
      (D.parity i) (fun r => (r : ZMod 2) * D.parity i) (-D.h i x₁).toNat) :
    L.f'.total M δ₁ ≫ eqToHom hS =
      eqToHom hT ≫ (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).f' := by
  let J := L.at M
  let K := elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
  apply column_principal_square K (L.f'.total M δ₁) (eqToIso hT) (eqToIso hS)
  · exact elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M
  · intro r _
    exact elvWeightUnitPower_localCoordinates D Sc cutoff N i Λ h₁ h₂ β M r
  · have hj := congrFun J.ff δ₁
    dsimp only [J] at hj
    simpa only [SKM.SuperSumInvFrom.at_f', CategoryTheory.Pi.comp_apply,
      CategoryTheory.Pi.id_apply, Categorification.TwoRep.pi_zero_apply] using hj
  · intro r hr
    have hcount := contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ₁
    have hr' : r < (-D.h i x₁).toNat := by simpa only [hcount] using hr
    have hj := (CategoryTheory.Pi.eval _ δ₁).congr_map (J.gf r hr')
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at hj
    dsimp only [J, CategoryTheory.Pi.eval] at hj
    simpa only [SKM.SuperSumInvFrom.at_f'] using hj

/-- The chosen positive principal has the canonical content inverse square. -/
theorem elvChosenCapPrincipal_coordinates (hh : 0 ≤ D.h i x₁) :
    elvChosenCapPrincipal D Sc cutoff N Λ hcutoff i h₁ h₂ M δ₁ hh ≫ eqToHom hS =
      eqToHom hT ≫ (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).f' :=
  elvCapPrincipal_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
    (((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invPos hh)

/-- The chosen negative principal has the canonical content inverse square. -/
theorem elvChosenUnitPrincipal_coordinates (hh : D.h i x₁ ≤ 0) :
    elvChosenUnitPrincipal D Sc cutoff N Λ hcutoff i h₁ h₂ M δ₁ hh ≫ eqToHom hS =
      eqToHom hT ≫ (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).f' :=
  elvUnitPrincipal_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh
    (((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invNeg hh)

end OddMath.QuiverHecke.ELVOld
