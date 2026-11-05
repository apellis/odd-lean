import OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentUnitInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedCoefficientMaps
import OddMath.SKM.AugmentedInverseNaturality

/-! # Coefficient rows at the empty-content boundary

BE (1.14) and SwappedVacuumCoordinates: the coefficient row transported
through the selected full-inclusion charts is the row of the inverse of
the given unit/dot columns. No finite-matrix inverse compatibility is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u v w

private theorem if_identity_total_apply
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C]
    [Linear k C] [Supercategory k C] (F : Superfunctor k C (SVec k))
    (b : Prop) [Decidable b] (w : C) (z : F.obj w) :
    ((if b then 𝟙 F else 0) : F ⟶ F).total w z = if b then z else 0 := by
  split_ifs
  · simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
      add_zero, SVec.id_apply]
  · simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add]
    rfl

private theorem conjugate_column_window
    {k : Type u} {C : Type v} [CommRing k] [Category.{w} C] [Preadditive C]
    [Linear k C] {A B V W : C} (a : A ≅ B) (c : V ≅ W)
    (g : V ⟶ A) (h : W ⟶ B) (r : B ⟶ W) (b : Prop) [Decidable b]
    (hs : g ≫ a.hom = c.hom ≫ h) (hr : h ≫ r = if b then 𝟙 W else 0) :
    g ≫ (a.hom ≫ r ≫ c.inv) = if b then 𝟙 V else 0 := by
  rw [← Category.assoc g, hs, Category.assoc c.hom, ← Category.assoc h, hr]
  split_ifs <;> simp

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem emptyContent_eq (w : ContentCategory D Sc cutoff N 0) :
    w = ⟨⟨[]⟩, rfl⟩ := by
  rcases w with ⟨⟨w⟩, hw⟩
  have he : w = [] := by simpa only [Multiset.coe_eq_zero] using hw
  subst w
  rfl

/-- On every weighted input module, the given coefficient module map
extracts the given unit/dot columns as a whole module identity. -/
theorem weightedContentCoefficientMap_unitDotColumn
    (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hh : 0 ≤ contentCrossingHeight D cutoff i (0 : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (0 : Multiset I)))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i (0 : Multiset I)) :
    (restriction (contentInclusion D Sc cutoff N (0 : Multiset I))).map
        (unitDotColumn (truncatedAppend D Sc cutoff N [i])
          (truncatedDot_supernatural D Sc cutoff N i) M a) ≫
      weightedContentCoefficientMap D Sc cutoff N i M 0 hh r =
        if a = r.val then 𝟙 _ else 0 := by
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [emptyContent_eq D Sc cutoff N w]
  apply SVec.hom_ext
  intro z
  rw [Superfunctor.comp_total]
  change (weightedContentCoefficientMap D Sc cutoff N i M 0 hh r).total
      ⟨⟨[]⟩, rfl⟩
      ((unitDotColumn (truncatedAppend D Sc cutoff N [i])
        (truncatedDot_supernatural D Sc cutoff N i) M a).total
        ((oldTruncateFunctor D Sc cutoff N).obj ⟨[]⟩) z) = _
  rw [weightedContentCoefficientMap_vacuum_total]
  rw [weightedUnitCoefficient_unitDotColumn D Sc cutoff N i M ⟨[]⟩ hh r a ha z]
  exact (if_identity_total_apply _ _ _ z).symm

variable (i : I) (M : ContentModules D Sc cutoff N (0 : Multiset I))
local notation "β" => (0 : Multiset I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hK" => contentBlockCanonicalSum β [i]
local notation "K" => contentAppendTo D Sc cutoff N β [i] γ hK
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "U" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sq" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hK
local notation "P" => induced Q M
local notation "FE" => Functor.obj (restriction T) (induced T P)
local notation "Target" => fullSquareTargetRetargetIso K U Q T sq M FE FE
  (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)) (Iso.refl FE)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N β M
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i

/-- Transport the prescribed weighted inverse row through the same selected
upper and value charts as the given canonical-content unit columns. -/
def contentVacuumCoefficientMap
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (r : Fin (contentUnitCount D cutoff i β)) :
    (restriction K).obj (induced K M) ⟶ M :=
  (Target).hom ≫ weightedContentCoefficientMap D Sc cutoff N i P β hh r ≫ (Value).inv

/-- The transported row extracts the literal canonical-content columns,
including the empty lower-predecessor boundary. -/
theorem contentVacuumCoefficientMap_unitDotColumn
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (r : Fin (contentUnitCount D cutoff i β))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i β) :
    unitDotColumn K hDot M a ≫ contentVacuumCoefficientMap D Sc cutoff N i M hh r =
      if a = r.val then 𝟙 M else 0 :=
  conjugate_column_window (k := k) Target Value _ _ _ _
    (contentUnitDotColumn_square D Sc cutoff N β i M a)
    (weightedContentCoefficientMap_unitDotColumn D Sc cutoff N i P hh r a ha)

/-- Every inverse of the given boundary columns has this same coefficient
row. This uses the proved joint-epimorphism identities, with no additional
inverse or matrix-comparison hypothesis. -/
theorem contentVacuumCoefficientMap_eq_inverseRow
    (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (r : Fin (contentUnitCount D cutoff i β))
    (J : SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff N β ⟶ (restriction K).obj (induced K M))
      (unitDotColumn K hDot M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i β)) :
    contentVacuumCoefficientMap D Sc cutoff N i M hh r = J.g' r.val := by
  apply J.hom_ext
  · simp only [Limits.zero_comp]
  · intro a ha
    rw [contentVacuumCoefficientMap_unitDotColumn D Sc cutoff N i M hh r a ha]
    exact (J.gg a r.val ha r.isLt).symm

end OddMath.QuiverHecke.ELVOld
