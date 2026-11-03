import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareParity
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockCapPowers
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixComponents
import Mathlib.CategoryTheory.Comma.Arrow

/-! # Module charts for the canonical content matrices

Brundan–Ellis (1.13)–(1.14): retain the selected full-inclusion E/F
comparisons as even module isomorphisms with the literal weighted matrix
endpoint modules. These charts supply canonical finite parity coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "T" => truncatedAppend D Sc cutoff N [i]

private def matrixMateArrow (P : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    Arrow (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :=
  Arrow.mk (weightedMatrixMate D Sc cutoff N i P)

private theorem matrixMateArrow_source (P : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (matrixMateArrow D Sc cutoff N i P).left = induced T ((restriction T).obj P) := rfl
private theorem matrixMateArrow_target (P : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (matrixMateArrow D Sc cutoff N i P).right = (restriction T).obj (induced T P) := rfl

private theorem restrictionSquare_mem (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ)
    (P : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (contentAppendToRestrictionSquare D Sc cutoff N β σ γ h P).hom ∈ parity (R := k) _ _ 0 :=
  id_mem _

variable (β : Multiset I)
local notation "γ" => β + ([i] : Multiset I)
local notation "δ" => γ + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "hK" => contentBlockCanonicalSum γ [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hK
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "Q₂" => contentInclusion D Sc cutoff N δ
local notation "sqJ" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hJ
local notation "sqK" => contentAppendTo_inclusion D Sc cutoff N γ [i] δ hK
variable (M : ContentModules D Sc cutoff N (β + ([i] : Multiset I)))
local notation "P" => induced Q₁ M

local notation "SourceChart" => fullSquareSourceRetargetIso J Q₁ Q₀ T sqJ (Functor.obj (restriction J) M)
  (Functor.obj (restriction T) P)
  (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
  (Arrow.left (matrixMateArrow D Sc cutoff N i P))
  (eqToIso (Eq.symm (matrixMateArrow_source D Sc cutoff N i P)))
local notation "TargetChart" => fullSquareTargetRetargetIso K Q₂ Q₁ T sqK M
  (Functor.obj (restriction T) (induced T P)) (Arrow.right (matrixMateArrow D Sc cutoff N i P))
  (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P))
  (eqToIso (Eq.symm (matrixMateArrow_target D Sc cutoff N i P)))
local notation "ValueChart" => contentExtensionUnitIso D Sc cutoff N γ M

theorem contentBlockMatrixSourceIso_hom_mem :
    (SourceChart).hom ∈ parity (R := k) _ _ 0 := by
  exact fullSquareSourceRetargetIso_hom_mem J Q₁ Q₀ T sqJ ((restriction J).obj M) ((restriction T).obj P)
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (matrixMateArrow D Sc cutoff N i P).left (eqToIso (matrixMateArrow_source D Sc cutoff N i P).symm)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)
    (eqToHom_mem (R := k) (matrixMateArrow_source D Sc cutoff N i P).symm)

theorem contentBlockMatrixTargetIso_hom_mem :
    (TargetChart).hom ∈ parity (R := k) _ _ 0 := by
  exact fullSquareTargetRetargetIso_hom_mem K Q₂ Q₁ T sqK M ((restriction T).obj (induced T P))
    (matrixMateArrow D Sc cutoff N i P).right
    (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P))
    (eqToIso (matrixMateArrow_target D Sc cutoff N i P).symm)
    (restrictionSquare_mem D Sc cutoff N γ [i] δ hK (induced T P))
    (eqToHom_mem (R := k) (matrixMateArrow_target D Sc cutoff N i P).symm)

theorem contentBlockMatrixValueIso_hom_mem :
    (ValueChart).hom ∈ parity (R := k) _ _ 0 := by
  rw [contentExtensionUnitIso, fullyFaithfulUnitIso_hom]
  exact adjunctionUnit_mem Q₁ M

theorem contentBlockMatrixSourceIso_inv_mem :
    (SourceChart).inv ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (contentBlockMatrixSourceIso_hom_mem D Sc cutoff N i β M)
theorem contentBlockMatrixTargetIso_inv_mem :
    (TargetChart).inv ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (contentBlockMatrixTargetIso_hom_mem D Sc cutoff N i β M)
theorem contentBlockMatrixValueIso_inv_mem :
    (ValueChart).inv ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (contentBlockMatrixValueIso_hom_mem D Sc cutoff N i β M)

/-- The selected source component, with its specified final endpoint map retained. -/
theorem contentBlockMatrixSourceIso_total
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I)))
    (x : (induced J ((restriction J).obj M)).obj t) :
    (SourceChart).hom.total t x =
      (eqToIso (matrixMateArrow_source D Sc cutoff N i P).symm).hom.total ((Q₁).obj t)
        ((fullSquareSourceIso J Q₁ Q₀ T sqJ ((restriction J).obj M) ((restriction T).obj P)
          (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)).hom.total t x) :=
  fullSquareSourceRetargetIso_total_apply J Q₁ Q₀ T sqJ ((restriction J).obj M) ((restriction T).obj P)
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (matrixMateArrow D Sc cutoff N i P).left (eqToIso (matrixMateArrow_source D Sc cutoff N i P).symm) t x

/-- The selected target component, including the strict restriction square. -/
theorem contentBlockMatrixTargetIso_total
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I)))
    (x : ((restriction K).obj (induced K M)).obj t) :
    (TargetChart).hom.total t x =
      (eqToIso (matrixMateArrow_target D Sc cutoff N i P).symm).hom.total ((Q₁).obj t)
        ((contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P)).hom.total t
          ((fullSquareRestrictionIso K Q₂ Q₁ T sqK M).hom.total ((K).obj t) x)) :=
  fullSquareTargetRetargetIso_total_apply K Q₂ Q₁ T sqK M ((restriction T).obj (induced T P))
    (matrixMateArrow D Sc cutoff N i P).right
    (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P))
    (eqToIso (matrixMateArrow_target D Sc cutoff N i P).symm) t x

/-- The chosen value chart is the fully faithful inclusion unit. -/
theorem contentBlockMatrixValueIso_total
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) (x : M.obj t) :
    (ValueChart).hom.total t x = unit Q₁ M.toFunctor t x := by
  simp only [contentExtensionUnitIso, fullyFaithfulUnitIso_hom, adjunctionUnit,
    Superfunctor.homMk, SuperNatTrans.total, unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

end OddMath.QuiverHecke.ELVOld
