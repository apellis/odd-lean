import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexLoopComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexRows
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendUpperLoop

/-! # Dotted evaluated rows through the selected loop comparisons

Brundan–Ellis (1.13)–(1.14): every dotted cap and unit column is retained
under the selected change of central and upper content representatives.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
attribute [local irreducible] oldAppendReindexIso
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc cut ν i ν₁ h₁
local notation "T" => probeReindexLoopFunctor D Sc m ν i h₁
local notation "R" => oldModuleReindex D Sc cut h₁
local notation "R⁻¹" => probeEvaluatedReindex D Sc m h₁.symm

/-- The total selected cap row retains its literal OLD dotted counit. -/
theorem probeAppendToCapRow_total_eq (n : ℕ) (N : ProbeEvaluatedModules D Sc m ν₁) :
    ((probeAppendToCapRow D Sc m ν i h₁ n).total N).hom =
      capDotRow J (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁) N.obj n := by
  change ((probeAppendToCapRow D Sc m ν i h₁ n).app 0 N).hom +
    ((probeAppendToCapRow D Sc m ν i h₁ n).app 1 N).hom = _
  rw [probeAppendToCapRow_app, probeAppendToCapRow_app]
  change (oldAppendToCapRow D Sc m ν i h₁ n).total N.obj = _
  rw [oldAppendToCapRow_eq, gridCapRowTransformation_total]

/-- Reindexing preserves every cap row through the chosen lower loop map. -/
theorem probeAppendToCapRow_reindex (n : ℕ) :
    (T).map (probeAppendToCapRow D Sc m ν i (List.Perm.refl (i :: ν)) n) =
      (probeReindexLowerLoopSuperIso D Sc m ν i h₁).hom ≫
        probeAppendToCapRow D Sc m ν i h₁ n := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change (R).map
      (((probeAppendToCapRow D Sc m ν i (List.Perm.refl (i :: ν)) n).total
        ((R⁻¹).obj N)).hom) =
    ((probeReindexLowerLoopSuperIso D Sc m ν i h₁).hom.total N).hom ≫
      ((probeAppendToCapRow D Sc m ν i h₁ n).total N).hom
  rw [probeAppendToCapRow_total_eq, probeAppendToCapRow_total_eq,
    probeReindexLowerLoopSuperIso_hom_total_eq]
  exact oldAppendReindexIso_capDotRow D Sc m ν i h₁ ((R⁻¹).obj N).obj n

/-- Reindexing preserves every unit column through the chosen upper loop map. -/
theorem probeAppendToUnitColumn_reindex (n : ℕ) :
    (T).map (probeAppendToUnitColumn D Sc m (i :: ν) i
      (List.Perm.refl (i :: i :: ν)) n) ≫
        (probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂).hom =
      probeAppendToUnitColumn D Sc m ν₁ i h₂ n := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change (R).map
      (((probeAppendToUnitColumn D Sc m (i :: ν) i
        (List.Perm.refl (i :: i :: ν)) n).total ((R⁻¹).obj N)).hom) ≫
    ((probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂).hom.total N).hom =
      ((probeAppendToUnitColumn D Sc m ν₁ i h₂ n).total N).hom
  rw [probeAppendToUnitColumn_total_eq, probeAppendToUnitColumn_total_eq,
    probeReindexUpperLoopSuperIso_hom_total_eq]
  exact oldAppendReindexIso_unitDotColumn D Sc m ν i h₁ h₂ ((R⁻¹).obj N).obj n

local notation "C₀" => probeEvaluatedTarget D Sc m ν
local notation "C₁" => probeEvaluatedTarget D Sc m (i :: ν)
local notation "E₀" => probeEvaluatedE D Sc m ν i
local notation "F₀" => probeEvaluatedF D Sc m ν i
local notation "x₀" => probeEvaluatedInductionDot D Sc m ν i

private theorem standard_dot :
    probeAppendToInductionDot D Sc m ν i (i :: ν) (List.Perm.refl _) = x₀ := by
  apply Superfunctor.hom_ext
  intro q N
  apply InducedCategory.hom_ext
  rfl

private theorem standard_counit :
    (probeAppendToRightAdjunction D Sc m ν i (i :: ν) (List.Perm.refl _)).counit =
      (probeEvaluatedRightAdjunction D Sc m ν i).counit := by
  apply Superfunctor.hom_ext
  intro q N
  apply InducedCategory.hom_ext
  fin_cases q <;> rfl

private theorem standard_unit :
    (probeAppendToRightAdjunction D Sc m ν i (i :: ν) (List.Perm.refl _)).unit =
      (probeEvaluatedRightAdjunction D Sc m ν i).unit := by
  apply Superfunctor.hom_ext
  intro q N
  apply InducedCategory.hom_ext
  fin_cases q <;> rfl

/-- The source cap row uses the original evaluated adjunction and dot. -/
theorem probeAppendToCapRow_standard (n : ℕ) :
    probeAppendToCapRow D Sc m ν i (List.Perm.refl (i :: ν)) n =
      BicategoryStruct.whiskerLeft (a := C₁) (b := C₀) (c := C₁) F₀
        (g := E₀) (h := E₀) (SKM.rouquierPower (a := C₀) (b := C₁) (E := E₀) x₀ n) ≫
        (probeEvaluatedRightAdjunction D Sc m ν i).counit := by
  unfold probeAppendToCapRow probeAppendToDotPower
  rw [standard_dot, standard_counit]
  rfl

/-- The source unit column uses the original evaluated adjunction and dot. -/
theorem probeAppendToUnitColumn_standard (n : ℕ) :
    probeAppendToUnitColumn D Sc m ν i (List.Perm.refl (i :: ν)) n =
      (probeEvaluatedRightAdjunction D Sc m ν i).unit ≫
        BicategoryStruct.whiskerRight (a := C₀) (b := C₁) (c := C₀)
          («f» := E₀) (g := E₀) (SKM.rouquierPower (a := C₀) (b := C₁) (E := E₀) x₀ n) F₀ := by
  unfold probeAppendToUnitColumn probeAppendToDotPower
  rw [standard_unit, standard_dot]
  rfl

end OddMath.QuiverHecke
