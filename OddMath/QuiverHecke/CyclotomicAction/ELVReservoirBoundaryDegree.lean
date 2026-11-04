import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaries
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightWindowInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVAbsentWindowInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWindowInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedContentKernelBoundaryCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleCentreTotalDegree

/-! # Chosen reservoir boundary contractions in source coordinates

SwappedHomInversion §4 (7): the finite chosen `g'` fields retain their
weight, content, parity and raw OLD coefficient coordinates. Supported
blocks use the prescribed local matrices; absent unit windows are retained.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirBoundaries
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
universe u
section EvenMaps
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
private theorem even_map_apply {F G : Superfunctor k C (SVec k)}
    (f : F ⟶ G) (hf : f ∈ parity (R := k) F G 0)
    {v w : C} (a : v ⟶ w) (b : F.obj v) :
    f.total w (F.map a b) = G.map a (f.total v b) := by
  have hz (t : C) : f.total t = f.app 0 t := by
    change f.app 0 t + f.app 1 t = f.app 0 t
    rw [Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  rw [hz v, hz w]
  have h := ((Superfunctor.toSuperNatTrans f).isSupernatural 0).naturality_zero a
  simpa only [SVec.comp_apply] using congrArg (fun t : F.obj v ⟶ G.obj w => t b) h
private theorem restriction_map_total
    {A : Type u} [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {F G : Superfunctor k A (SVec k)} (f : F ⟶ G) (w : C) :
    ((BalancedInduction.restriction Q).map f).total w = f.total (Q.obj w) := rfl
private theorem module_action_transport {R S : Superfunctor k C (SVec k)}
    (h : R = S) (η : ∀ M : Superfunctor k C (SVec k), End M)
    {w : C} (a : End w)
    (ha : ∀ b : R.obj w, (η R).total w b = R.map a b) :
    ∀ b : S.obj w, (η S).total w b = S.map a b := by
  cases h
  exact ha
private theorem module_value_transport {R S : Superfunctor k C (SVec k)}
    (h : R = S) (η : ∀ M : Superfunctor k C (SVec k), End M)
    (ha : η R = 0) : η S = 0 := by
  cases h
  exact ha
private theorem module_action_of_family_extension {F : Type*}
    (Q : F → Superfunctor k C (SVec k))
    (e : Superfunctor k C (SVec k) → F)
    (he : ∀ R, Q (e R) = R)
    (η : ∀ R : Superfunctor k C (SVec k), End R)
    (ξ : ∀ M, End (Q M)) {w : C} (a : End w)
    (hη : ∀ M, η (Q M) = ξ M)
    (hξ : ∀ M (b : (Q M).obj w), (ξ M).total w b = (Q M).map a b)
    (R : Superfunctor k C (SVec k)) (b : R.obj w) :
    (η R).total w b = R.map a b := by
  have ha (x : (Q (e R)).obj w) :
      (η (Q (e R))).total w x = (Q (e R)).map a x :=
    (congrArg (fun f : End (Q (e R)) => f.total w x) (hη (e R))).trans (hξ (e R) x)
  exact module_action_transport (k := k) (C := C) (R := Q (e R)) (S := R) (w := w)
    (he R) η a ha b
end EvenMaps

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (M : ELVWeightProduct D Sc cutoff N Λ x₁) (β : WeightBlocks D Λ x₀)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "J" => elvBlockAppend D Sc cutoff N i Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff N i Λ h₂ δ
local notation "hDotJ" => elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β
local notation "hDotK" => elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ
local notation "Source" => eqToHom (elvWeightMixedSource_obj D Sc cutoff N i i Λ h₁ h₁ β M)
local notation "Target" => eqToHom (elvWeightMixedTarget_obj D Sc cutoff N i i Λ h₁ h₂ h₁ h₂ β M)
local notation "UnitField" r => elvActionUnit D Sc cutoff N i Λ h₂ ≫
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) r ▷ elvF D Sc cutoff N i Λ h₂
local notation "CapField" s => elvF D Sc cutoff N i Λ h₁ ◁
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) s ≫ elvActionCounit D Sc cutoff N i Λ h₁

/-- The literal chosen positive boundary has the content cap inverse column. -/
theorem positive_content_coordinates (hh : 0 ≤ D.h i x₁)
    (j : ℕ) (hj : j < (D.h i x₁).toNat) (r : ℕ) :
    (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh j r).total M δ =
      (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j ≫
        capDotRow J hDotJ (M δ) r := by
  have hp := elvChosenCapWindow_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh j hj
  have hc := elvWeightCapPower_localCoordinates D Sc cutoff N i Λ h₁ β M r
  have h : elvChosenCapWindow D Sc cutoff N Λ hcutoff i h₁ h₂ M δ hh j ≫
      (CapField r).total M δ = _ := by
    rw [hc, ← Category.assoc, hp]
  have hε : ((elvRouquierFamily D Sc cutoff N Λ hcutoff).adj i h₁).counit =
      elvActionCounit D Sc cutoff N i Λ h₁ := rfl
  have hx : (elvRouquierFamily D Sc cutoff N Λ hcutoff).dot i h₁ =
      elvActionDot D Sc cutoff N i Λ h₁ := rfl
  simpa only [positive, SKM.SuperRouquierLoc.boundaryPos, elvChosenCapWindow,
    Superfunctor.comp_total, SuperNatTrans.vcomp_total, CategoryTheory.Pi.comp_apply,
    Category.assoc, hε, hx, elvRouquierFamily_F] using h

/-- The literal chosen negative boundary has the content unit inverse row. -/
theorem negative_content_coordinates (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j).total M δ =
      unitDotColumn K hDotK (M δ) r ≫
        (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j := by
  have hp := elvChosenUnitWindow_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh j hj
  have hu := elvWeightUnitPower_localCoordinates D Sc cutoff N i Λ h₁ h₂ β M r
  have h : (UnitField r).total M δ ≫
      elvChosenUnitWindow D Sc cutoff N Λ hcutoff i h₁ h₂ M δ hh j = _ := by
    rw [hp, ← Category.assoc, hu]
  have hη : ((elvRouquierFamily D Sc cutoff N Λ hcutoff).adj i h₂).unit =
      elvActionUnit D Sc cutoff N i Λ h₂ := rfl
  have hx : (elvRouquierFamily D Sc cutoff N Λ hcutoff).dot i h₂ =
      elvActionDot D Sc cutoff N i Λ h₂ := rfl
  simpa only [negative, SKM.SuperRouquierLoc.boundaryNeg, elvChosenUnitWindow,
    Superfunctor.comp_total, SuperNatTrans.vcomp_total, CategoryTheory.Pi.comp_apply,
    Category.assoc, hη, hx, elvRouquierFamily_F] using h

private theorem boundarySingletonDot_mem (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

section ContentTargets
variable (βt γt δt : Multiset I) (hγt : βt + ([i] : Multiset I) = γt)
  (hδt : γt + ([i] : Multiset I) = δt) (Mt : ContentModules D Sc cutoff N γt)
local notation "Jt" => contentAppendTo D Sc cutoff N βt [i] γt hγt
local notation "Kt" => contentAppendTo D Sc cutoff N γt [i] δt hδt
local notation "hCrosst" => contentTargetsGridCross_supernatural D Sc cutoff N βt γt δt i hγt hδt
local notation "hDotJt" => contentAppendTo_supernatural D Sc cutoff N hγt hγt
  (boundarySingletonDot_mem D Sc i)
local notation "hDotKt" => contentAppendTo_supernatural D Sc cutoff N hδt hδt
  (boundarySingletonDot_mem D Sc i)
local notation "Qt" => contentInclusion D Sc cutoff N γt
local notation "Tt" => truncatedAppend D Sc cutoff N [i]
local notation "Pt" => induced Qt Mt
local notation "Valuet" => contentExtensionUnitIso D Sc cutoff N γt Mt
local notation "Sourcet" => contentPrincipalSourceIso D Sc cutoff N βt γt i hγt Mt
local notation "Targett" => contentPrincipalTargetIso D Sc cutoff N γt δt i hδt Mt

/-- The content cap boundary retains the weighted finite inverse column. -/
theorem contentTargetsCapBoundary_coordinates
    (L : SKM.SuperSumInvTo (k := k) (orderedGridMateComponent Jt Kt hCrosst Mt)
      (capDotRow Jt hDotJt Mt) (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γt))
    (hh : contentCrossingHeight D cutoff i γt ≤ 0)
    (j : ℕ) (hj : j < contentCapCount D cutoff i γt) (r : ℕ) :
    (L.g' j ≫ capDotRow Jt hDotJt Mt r) ≫ (Valuet).hom =
      (Valuet).hom ≫ (weightedContentLocalInverseTo D Sc cutoff N i Pt γt hh).g' j ≫
        (restriction Qt).map (capDotRow Tt (truncatedDot_supernatural D Sc cutoff N i) Pt r) := by
  rw [contentTargetsLocalInverseTo_window D Sc cutoff N βt i γt δt hγt hδt Mt L hh j hj]
  -- The same ordinary cap square with the stored successor contents.
  have hc' : capDotRow Jt hDotJt Mt r ≫ (Valuet).hom =
      (Sourcet).hom ≫
        (restriction Qt).map (capDotRow Tt (truncatedDot_supernatural D Sc cutoff N i) Pt r) := by
    subst δt
    subst γt
    exact contentMatrixCapDotRow_square D Sc cutoff N βt i Mt r
  simp only [Category.assoc]
  rw [hc']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The content unit boundary retains the weighted finite inverse row. -/
theorem contentTargetsUnitBoundary_coordinates
    (L : SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent Jt Kt hCrosst Mt)
      (unitDotColumn Kt hDotKt Mt) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γt))
    (hh : 0 ≤ contentCrossingHeight D cutoff i γt)
    (r j : ℕ) (hj : j < contentUnitCount D cutoff i γt) :
    (unitDotColumn Kt hDotKt Mt r ≫ L.g' j) ≫ (Valuet).hom =
      (Valuet).hom ≫
        (restriction Qt).map (unitDotColumn Tt (truncatedDot_supernatural D Sc cutoff N i) Pt r) ≫
          (weightedContentLocalInverseFrom D Sc cutoff N i Pt γt hh).g' j := by
  rw [contentTargetsLocalInverseFrom_window D Sc cutoff N βt i γt δt hγt hδt Mt L hh j hj]
  have hu' : unitDotColumn Kt hDotKt Mt r ≫ (Targett).hom =
      (Valuet).hom ≫
        (restriction Qt).map (unitDotColumn Tt (truncatedDot_supernatural D Sc cutoff N i) Pt r) := by
    subst δt
    subst γt
    exact contentUnitDotColumn_square D Sc cutoff N (βt + ([i] : Multiset I)) i Mt r
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hu']
  simp only [Category.assoc]
end ContentTargets

local notation "Qδ" => contentInclusion D Sc cutoff N δ.1
local notation "Tδ" => truncatedAppend D Sc cutoff N [i]
local notation "Pδ" => induced Qδ (M δ)
local notation "Valueδ" => contentExtensionUnitIso D Sc cutoff N δ.1 (M δ)

include hcutoff in
private theorem cap_height (γ : WeightBlocks D Λ x₁) (hh : 0 ≤ D.h i x₁) :
    contentCrossingHeight D cutoff i γ.1 ≤ 0 := by
  rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ (hcutoff i) γ]
  exact neg_nonpos.mpr hh
include hcutoff in
private theorem unit_height (γ : WeightBlocks D Λ x₁) (hh : D.h i x₁ ≤ 0) :
    0 ≤ contentCrossingHeight D cutoff i γ.1 := by
  rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ (hcutoff i) γ]
  exact neg_nonneg.mpr hh

/-- The chosen positive boundary has the literal weighted cap-window coordinates. -/
theorem positive_weighted_coordinates (hh : 0 ≤ D.h i x₁)
    (j : ℕ) (hj : j < (D.h i x₁).toNat) (r : ℕ) :
    (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh j r).total M δ ≫ (Valueδ).hom =
      (Valueδ).hom ≫
        (weightedContentLocalInverseTo D Sc cutoff N i Pδ δ.1
          (cap_height D cutoff Λ hcutoff i δ hh)).g' j ≫
        (restriction Qδ).map (capDotRow Tδ (truncatedDot_supernatural D Sc cutoff N i) Pδ r) := by
  rw [positive_content_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh j hj r]
  exact contentTargetsCapBoundary_coordinates D Sc cutoff N i β.1 δ.1
    (blockSucc D Λ i h₂ δ).1 (elvBlockSucc_content_eq D i Λ h₁ β)
    (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ)
    (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh)
    (cap_height D cutoff Λ hcutoff i δ hh) j
    (by simpa only [contentCapCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ] using hj) r

/-- The chosen negative boundary has the literal weighted unit-window coordinates. -/
theorem negative_weighted_coordinates (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j).total M δ ≫ (Valueδ).hom =
      (Valueδ).hom ≫
        (restriction Qδ).map (unitDotColumn Tδ (truncatedDot_supernatural D Sc cutoff N i) Pδ r) ≫
          (weightedContentLocalInverseFrom D Sc cutoff N i Pδ δ.1
            (unit_height D cutoff Λ hcutoff i δ hh)).g' j := by
  rw [negative_content_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh r j hj]
  exact contentTargetsUnitBoundary_coordinates D Sc cutoff N i β.1 δ.1
    (blockSucc D Λ i h₂ δ).1 (elvBlockSucc_content_eq D i Λ h₁ β)
    (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ)
    (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh)
    (unit_height D cutoff Λ hcutoff i δ hh) r j
    (by simpa only [contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ] using hj)

end OddMath.QuiverHecke.ELVOld.ReservoirBoundaries
