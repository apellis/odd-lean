import OddMath.QuiverHecke.CyclotomicAction.ELVContentCoefficientCaps
import OddMath.QuiverHecke.CyclotomicAction.ELVContentUpperCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows

/-! # The given coefficient-cap window on the old empty-content category

The empty local inverse in Brundan's Theorem 4.3 uses the ordinary unit
columns and the given inverse coefficients over the full old coefficient
algebra. The selected native charts retain that window on every input
module; no scalar-evaluation or regular-module restriction is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u

private theorem chart_column_window
    {k V W V' W' : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid V'] [Module k V'] [AddCommMonoid W'] [Module k W']
    (v : V ≃ₗ[k] V') (e : W ≃ₗ[k] W')
    (row : W →ₗ[k] V) (rawRow : W' →ₗ[k] V')
    (col : V →ₗ[k] W) (rawCol : V' →ₗ[k] W')
    (q : Prop) [Decidable q]
    (hc : row = v.symm.toLinearMap.comp (rawRow.comp e.toLinearMap))
    (he : ∀ b, e (col b) = rawCol (v b))
    (hw : ∀ b, rawRow (rawCol b) = if q then b else 0) (b : V) :
    row (col b) = if q then b else 0 := by
  apply v.injective
  rw [hc]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [he, hw]
  split_ifs <;> simp only [map_zero]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem coefficient_unitDot_window
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (i : I)
    (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (t.word : Multiset I)))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i (t.word : Multiset I)) (b : M.obj t) :
    moduleUnitCoefficient D Sc cutoff M i t hh r
      (unitDotLinear (append D Sc cutoff i) (oldAppendDot_supernatural D Sc cutoff i) M a t b) =
      if a = r.val then b else 0 := by
  have h := moduleUnitCoefficient_dot_window D Sc cutoff M i t hh r a ha b
  change moduleUnitCoefficient D Sc cutoff M i t hh r
    (((actualInductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t)) ^ a)
      (((adjunctionUnit (append D Sc cutoff i)).app M).total t b)) = _ at h
  rw [adjunctionUnit_total_apply] at h
  exact h

private theorem coefficient_map_unitDot_window
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (i : I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i (([] : List I) : Multiset I))
    (b : M.obj (OldCategory.mk [])) :
    (contentUnitCoefficientMap D Sc cutoff M i [] hh r).total
      (OldContentCategory.mk (OldCategory.mk []) (List.Perm.refl []))
      (unitDotLinear (append D Sc cutoff i) (oldAppendDot_supernatural D Sc cutoff i) M a
        (OldCategory.mk []) b) = if a = r.val then b else 0 := by
  rw [contentUnitCoefficientMap_vacuum_total]
  exact coefficient_unitDot_window D Sc cutoff M i (OldCategory.mk []) hh r a ha b

variable (N : Superfunctor k (OldContentCategory D Sc cutoff []) (SVec k)) (i : I)
local notation "K" => oldContentAppend D Sc cutoff [] i
local notation "Q" => oldContentInclusion D Sc cutoff []
local notation "J" => append D Sc cutoff i
local notation "G" => induced Q N
local notation "count" => contentUnitCount D cutoff i (([] : List I) : Multiset I)

private theorem empty_content_unique (w : OldContentCategory D Sc cutoff []) :
    w = OldContentCategory.mk (OldCategory.mk []) (List.Perm.refl []) := by
  rcases w with ⟨⟨word⟩, hw⟩
  have hn : word = [] := List.perm_nil.mp hw
  subst word
  rfl

private theorem vacuum_height : 0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

/-- Over the full old coefficient algebra, the selected native coefficient
cap extracts its given unit/dot column on every empty-content input module. -/
theorem contentVacuumCoefficientCap_unitDot (w : OldContentCategory D Sc cutoff [])
    (r : Fin count) (a : ℕ) (ha : a < count) (b : N.obj w) :
    (contentCoefficientCap D Sc cutoff [] i N (vacuum_height D cutoff i) r).total w
      (unitDotLinear K (oldContentAppendDot_supernatural D Sc cutoff [] i) N a w b) =
      if a = r.val then b else 0 := by
  obtain rfl := empty_content_unique D Sc cutoff w
  exact chart_column_window
    (oldContentValueChart D Sc cutoff [] N _)
    (oldContentFEChart D Sc cutoff [] i N _)
    ((contentCoefficientCap D Sc cutoff [] i N (vacuum_height D cutoff i) r).total _)
    ((contentUnitCoefficientMap D Sc cutoff G i [] (vacuum_height D cutoff i) r).total _)
    (unitDotLinear K (oldContentAppendDot_supernatural D Sc cutoff [] i) N a _)
    (unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) G a _)
    (a = r.val)
    (contentCoefficientCap_total D Sc cutoff [] i N (vacuum_height D cutoff i) r _)
    (oldContentFEChart_unitDot D Sc cutoff [] i N _ a)
    (coefficient_map_unitDot_window D Sc cutoff G i (vacuum_height D cutoff i) r a ha) b

end OddMath.QuiverHecke.ELVOld
