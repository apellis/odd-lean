import OddMath.Algebra.FiniteSupermoduleInverseColumns
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockMatrix.ContentFiniteMatrixComparison

/-!
# Content block matrix

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Local inverse columns of the given weighted cap matrix

BE (1.13): the constructed weighted cap matrix inverse restricts to the
specified output content with the given mate and ordinary dot/cap fields.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
namespace BalancedInduction
universe u
variable {k C A : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  {ι : Type}

/-- Restriction retains all rows in the literal finite product coordinate. -/
theorem restriction_finiteRows
    {V : ι → Superfunctor k A (SVec k)} {S : Superfunctor k A (SVec k)}
    (f : ∀ a, S ⟶ V a) (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) :
    (restriction Q).map (OddMath.FiniteSupermodule.rowsHom f hf) ≫
        eqToHom (restriction_finiteProduct Q V) =
      OddMath.FiniteSupermodule.rowsHom (fun a => (restriction Q).map (f a))
        (fun a => map_mem (restriction Q) (hf a)) := by
  change ((restriction Q).map (OddMath.FiniteSupermodule.rowsHom f hf) ≫ 𝟙 _) = _
  rw [Category.comp_id]
  apply Superfunctor.hom_ext_parity
  · intro t
    rfl
  · intro t
    rfl

end BalancedInduction
open BalancedInduction OddMath.FiniteSupermodule CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
  (β : Multiset I)
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "R" => restriction (contentInclusion D Sc cutoff N β)
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "m" => contentCapCount D cutoff i β
local notation "p" => D.parity i
local instance weightedCapLocalPi : PiSupercategory k
    (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) := supermodulePiSupercategory

/-- The given weighted cap matrix supplies every local inverse column on its
output content. The prescribed forward fields are retained without an inverse premise. -/
def weightedContentLocalInverseTo
    (hh : contentCrossingHeight D cutoff i β ≤ 0) :
    SKM.SuperSumInvTo (k := k) ((R).map (weightedMatrixMate D Sc cutoff N i M))
      (fun n => (R).map (capDotRow T (truncatedDot_supernatural D Sc cutoff N i) M n))
      p (fun n => n • p) m :=
  localInverseToRows p (fun n => n • p)
    ((R).mapIso ((SKM.homParityShiftDatum (k := k) p).iso ((restriction T).obj (induced T M))))
    (fun r => (R).mapIso ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M))
    (map_mem R ((SKM.homParityShiftDatum (k := k) p).hom_mem _))
    (fun r => map_mem R ((SKM.homParityShiftDatum (k := k) (r.val • p)).hom_mem M))
    ((R).map (weightedMatrixMate D Sc cutoff N i M))
    (fun n => (R).map (capDotRow T (truncatedDot_supernatural D Sc cutoff N i) M n))
    (map_mem R (weightedMatrixMate_mem D Sc cutoff N i M))
    (fun n => map_mem R (capDotRow_mem T (truncatedDot_supernatural D Sc cutoff N i) M n))
    (weightedContentCapMatrixIso D Sc cutoff N i M β hh ≪≫
      eqToIso (restriction_finiteProduct Q (weightedCapMatrixFamily D Sc cutoff N i M m))) (by
        rw [Iso.trans_hom, weightedContentCapMatrixIso_hom]
        change (R).map (rowsHom _ _) ≫ eqToHom (restriction_finiteProduct Q _) = _
        rw [restriction_finiteRows]
        unfold restoredRows
        congr 1
        funext a
        cases a with
        | none =>
          simp only [restoredRow, optionRestoringIso, optionForwardRows,
            Functor.mapIso_inv, ← CategoryTheory.Functor.map_comp, weightedCapMatrixEntry_none]
        | some r =>
          simp only [restoredRow, optionRestoringIso, optionForwardRows,
            Functor.mapIso_inv, ← CategoryTheory.Functor.map_comp, weightedCapMatrixEntry_some])

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Prescribed content inverses with a lower predecessor

BE (1.13)–(1.14): the given global weighted inverse transports through
the selected full-content source, target and value isomorphisms. Both
orientations retain the literal negative-crossing grid mate and every
ordinary unit/dot column or cap/dot row.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "δ" => γ + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "hK" => contentBlockCanonicalSum γ [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hK
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "Q₂" => contentInclusion D Sc cutoff N δ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sqJ" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hJ
local notation "sqK" => contentAppendTo_inclusion D Sc cutoff N γ [i] δ hK
local notation "hCross" => contentBlockMatrixCross_supernatural D Sc cutoff N β i
local notation "hDotJ" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hDotK" => contentBlockMatrixDot_supernatural D Sc cutoff N γ i
variable (M : ContentModules D Sc cutoff N (β + ([i] : Multiset I)))
local notation "P" => induced Q₁ M
local notation "FE" => Functor.obj (restriction T) (induced T P)
local notation "Target" => fullSquareTargetRetargetIso K Q₂ Q₁ T sqK M FE FE
  (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P)) (Iso.refl FE)
local notation "Source" => fullSquareSourceIso J Q₁ Q₀ T sqJ
  (Functor.obj (restriction J) M) (Functor.obj (restriction T) P)
  (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N γ M

/-- The prescribed unit inverse on a supported content block is constructed
from the given weighted unit matrix, with no inverse premise. -/
theorem contentSupportedLocalInverseFrom_nonempty
    (hh : 0 ≤ contentCrossingHeight D cutoff i γ) :
    Nonempty (SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J K hCross M)
      (unitDotColumn K hDotK M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γ)) := by
  let B := weightedContentLocalInverseFrom D Sc cutoff N i P γ hh
  let a := Target
  let b := Source
  let c := Value
  have H := B.mapCoordinates (𝟭 (ContentModules D Sc cutoff N γ)) a b c
    (contentUnitTargetIso_hom_mem D Sc cutoff N γ i M)
    (contentMatrixSourceIso_hom_mem D Sc cutoff N β i M)
    (contentUnitValueIso_hom_mem D Sc cutoff N γ M)
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (weightedMatrixMate D Sc cutoff N i P)) ≫ a.inv =
      orderedGridMateComponent J K hCross M := by
    have hs := contentPrincipalMate_square D Sc cutoff N β i M
    rw [← weightedMatrixMate_eq_ordered D Sc cutoff N i P] at hs
    have he := congrArg (fun f => f ≫ a.inv) hs
    dsimp only [a, b, c] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ a.inv =
      unitDotColumn K hDotK M n := by
    have hs := contentUnitDotColumn_square D Sc cutoff N γ i M n
    have he := congrArg (fun f => f ≫ a.inv) hs
    dsimp only [a, b, c] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  exact ⟨by simpa only [hf, hg] using H⟩

/-- The prescribed cap inverse on a supported block retains the same chosen
principal field and all ordinary dotted rows. -/
theorem contentSupportedLocalInverseTo_nonempty
    (hh : contentCrossingHeight D cutoff i γ ≤ 0) :
    Nonempty (SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J K hCross M)
      (capDotRow J hDotJ M) (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γ)) := by
  let B := weightedContentLocalInverseTo D Sc cutoff N i P γ hh
  let a := Source
  let b := Target
  let c := Value
  have H := B.mapCoordinates (𝟭 (ContentModules D Sc cutoff N γ)) a b c
    (contentMatrixSourceIso_hom_mem D Sc cutoff N β i M)
    (contentUnitTargetIso_hom_mem D Sc cutoff N γ i M)
    (contentUnitValueIso_hom_mem D Sc cutoff N γ M)
  have hf : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (weightedMatrixMate D Sc cutoff N i P)) ≫ b.inv =
      orderedGridMateComponent J K hCross M := by
    have hs := contentPrincipalMate_square D Sc cutoff N β i M
    rw [← weightedMatrixMate_eq_ordered D Sc cutoff N i P] at hs
    have he := congrArg (fun f => f ≫ b.inv) hs
    dsimp only [a, b, c] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  have hg (n : ℕ) : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (capDotRow T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ c.inv =
      capDotRow J hDotJ M n := by
    have hs := contentMatrixCapDotRow_square D Sc cutoff N β i M n
    have he := congrArg (fun f => f ≫ c.inv) hs
    dsimp only [a, b, c] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  exact ⟨by simpa only [hf, hg] using H⟩

private theorem supportedSingletonDot_mem (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

section Targets
variable (γ' δ' : Multiset I) (hγ' : β + ([i] : Multiset I) = γ')
  (hδ' : γ' + ([i] : Multiset I) = δ')
local notation "J'" => contentAppendTo D Sc cutoff N β [i] γ' hγ'
local notation "K'" => contentAppendTo D Sc cutoff N γ' [i] δ' hδ'
local notation "hCross'" => contentTargetsGridCross_supernatural D Sc cutoff N β γ' δ' i hγ' hδ'
local notation "hDotJ'" => contentAppendTo_supernatural D Sc cutoff N hγ' hγ' (supportedSingletonDot_mem D Sc i)
local notation "hDotK'" => contentAppendTo_supernatural D Sc cutoff N hδ' hδ' (supportedSingletonDot_mem D Sc i)

/-- The constructed unit inverse retains the stored successor contents used
by the weight induction functors. -/
theorem contentTargetsLocalInverseFrom_nonempty (M' : ContentModules D Sc cutoff N γ')
    (hh : 0 ≤ contentCrossingHeight D cutoff i γ') :
    Nonempty (SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J' K' hCross' M')
      (unitDotColumn K' hDotK' M') (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γ')) := by
  subst δ'
  subst γ'
  exact contentSupportedLocalInverseFrom_nonempty D Sc cutoff N β i M' hh

/-- The constructed cap inverse keeps the same two stored append targets. -/
theorem contentTargetsLocalInverseTo_nonempty (M' : ContentModules D Sc cutoff N γ')
    (hh : contentCrossingHeight D cutoff i γ' ≤ 0) :
    Nonempty (SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J' K' hCross' M')
      (capDotRow J' hDotJ' M') (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γ')) := by
  subst δ'
  subst γ'
  exact contentSupportedLocalInverseTo_nonempty D Sc cutoff N β i M' hh
end Targets

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Prescribed weight inverses on supported blocks

BE (1.13)–(1.14): transport the constructed supported-content inverse
through the selected weight mate coordinates. The same equations govern
the literal unit/power columns and cap/power rows. Standing cutoff
compatibility identifies every content count with categorical height.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff N Λ x₁)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "ε" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "J" => elvBlockAppend D Sc cutoff N i Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff N i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "hCross" => contentTargetsGridCross_supernatural D Sc cutoff N
  (Subtype.val β) (Subtype.val (blockSucc D Λ i h₁ β))
  (Subtype.val (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β))) i
  (elvBlockSucc_content_eq D i Λ h₁ β)
  (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ i h₁ β))
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
local notation "hSource" => elvWeightMixedSource_obj D Sc cutoff N i i Λ h₁ h₁ β M
local notation "hTarget" => elvWeightMixedTarget_obj D Sc cutoff N i i Λ h₁ h₂ h₁ h₂ β M

/-- The supported nonpositive-height block has the prescribed weight unit inverse. -/
theorem elvWeightSupportedUnitInverse_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
          elvF D Sc cutoff N i Λ h₂).total M δ)
      (D.parity i) (fun n => n • D.parity i) (-D.h i x₁).toNat) := by
  rw [← contentUnitCount_weightBlock D cutoff i Λ x₁ hcutoff δ]
  have hc : 0 ≤ contentCrossingHeight D cutoff i δ.1 := by
    rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ hcutoff δ]
    exact neg_nonneg.mpr hh
  let B := Classical.choice (contentTargetsLocalInverseFrom_nonempty D Sc cutoff N β.1 i δ.1 ε.1
    (elvBlockSucc_content_eq D i Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ) hc)
  let a := eqToIso hTarget
  let b := eqToIso hSource
  let c := Iso.refl (M δ)
  have hc0 : c.hom = 𝟙 (M δ) := rfl
  have H := B.mapCoordinates (𝟭 (ContentModules D Sc cutoff N δ.1)) a b c
    (eqToHom_mem_parity_zero hTarget) (eqToHom_mem_parity_zero hSource) (id_mem _)
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (orderedGridMateComponent J K hCross (M δ)) ≫ a.inv = (φ).app (D.parity i) M δ := by
    have hp := elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M
    have hs : (φ).app (D.parity i) M δ ≫ a.hom =
        b.hom ≫ orderedGridMateComponent J K hCross (M δ) := by
      simpa only [a, b, eqToIso.hom] using hp
    simpa only [Functor.id_map, ← Category.assoc] using
      (Iso.comp_inv_eq a).2 hs.symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (unitDotColumn K (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ) (M δ) n) ≫ a.inv =
      (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
          elvF D Sc cutoff N i Λ h₂).total M δ := by
    have hp := elvWeightUnitPower_localCoordinates D Sc cutoff N i Λ h₁ h₂ β M n
    have hs : (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
          elvF D Sc cutoff N i Λ h₂).total M δ ≫ a.hom =
        c.hom ≫ unitDotColumn K (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ) (M δ) n := by
      simpa only [a, eqToIso.hom, hc0, Category.id_comp] using hp
    simpa only [Functor.id_map, ← Category.assoc] using
      (Iso.comp_inv_eq a).2 hs.symm
  exact ⟨by simpa only [hf, hg] using H⟩

/-- The supported nonnegative-height block has the prescribed weight cap inverse. -/
theorem elvWeightSupportedCapInverse_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (elvF D Sc cutoff N i Λ h₁ ◁
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
          elvActionCounit D Sc cutoff N i Λ h₁).total M δ)
      (D.parity i) (fun n => n • D.parity i) (D.h i x₁).toNat) := by
  rw [← contentCapCount_weightBlock D cutoff i Λ x₁ hcutoff δ]
  have hc : contentCrossingHeight D cutoff i δ.1 ≤ 0 := by
    rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ hcutoff δ]
    exact neg_nonpos.mpr hh
  let B := Classical.choice (contentTargetsLocalInverseTo_nonempty D Sc cutoff N β.1 i δ.1 ε.1
    (elvBlockSucc_content_eq D i Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ) hc)
  let a := eqToIso hSource
  let b := eqToIso hTarget
  let c := Iso.refl (M δ)
  have hc0 : c.inv = 𝟙 (M δ) := rfl
  have H := B.mapCoordinates (𝟭 (ContentModules D Sc cutoff N δ.1)) a b c
    (eqToHom_mem_parity_zero hSource) (eqToHom_mem_parity_zero hTarget) (id_mem _)
  have hf : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (orderedGridMateComponent J K hCross (M δ)) ≫ b.inv = (φ).app (D.parity i) M δ := by
    have hp := elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M
    have hs : (φ).app (D.parity i) M δ ≫ b.hom =
        a.hom ≫ orderedGridMateComponent J K hCross (M δ) := by
      simpa only [a, b, eqToIso.hom] using hp
    simpa only [Functor.id_map, ← Category.assoc] using
      (Iso.comp_inv_eq b).2 hs.symm
  have hg (n : ℕ) : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n) ≫ c.inv =
      (elvF D Sc cutoff N i Λ h₁ ◁
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
          elvActionCounit D Sc cutoff N i Λ h₁).total M δ := by
    have hs : (elvF D Sc cutoff N i Λ h₁ ◁
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
          elvActionCounit D Sc cutoff N i Λ h₁).total M δ =
        a.hom ≫ capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n := by
      simpa only [a, eqToIso.hom] using
        elvWeightCapPower_localCoordinates D Sc cutoff N i Λ h₁ β M n
    rw [Functor.id_map]
    calc
      a.hom ≫ capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n ≫ c.inv =
          (a.hom ≫ capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n) ≫ c.inv :=
        (Category.assoc _ _ _).symm
      _ = a.hom ≫ capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n := by
        rw [hc0]
        exact Category.comp_id _
      _ = _ := hs.symm
  exact ⟨by simpa only [hf, hg] using H⟩

end OddMath.QuiverHecke.ELV
end

end
