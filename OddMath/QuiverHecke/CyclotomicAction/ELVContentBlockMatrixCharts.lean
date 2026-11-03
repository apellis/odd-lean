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
private def composeIso {E : Type*} [Category E] {F G H : E} (e : F ≅ G) (d : G ≅ H) : F ≅ H := e ≪≫ d
private theorem composeIso_mem {k E : Type*} [CommRing k] [Category E]
    [Preadditive E] [Linear k E] [Supercategory k E]
    {F G H : E} (e : F ≅ G) (d : G ≅ H)
    (he : e.hom ∈ parity (R := k) _ _ 0) (hd : d.hom ∈ parity (R := k) _ _ 0) :
    (composeIso e d).hom ∈ parity (R := k) _ _ 0 := by
  simpa only [composeIso, Iso.trans_hom, zero_add] using comp_mem he hd
private def composeIso3 {E : Type*} [Category E] {F G H K : E}
    (e : F ≅ G) (d : G ≅ H) (f : H ≅ K) : F ≅ K := e ≪≫ d ≪≫ f
private theorem composeIso3_mem {k E : Type*} [CommRing k] [Category E]
    [Preadditive E] [Linear k E] [Supercategory k E]
    {F G H K : E} (e : F ≅ G) (d : G ≅ H) (f : H ≅ K)
    (he : e.hom ∈ parity (R := k) _ _ 0) (hd : d.hom ∈ parity (R := k) _ _ 0)
    (hf : f.hom ∈ parity (R := k) _ _ 0) :
    (composeIso3 e d f).hom ∈ parity (R := k) _ _ 0 := by
  simpa only [composeIso3, Iso.trans_hom, zero_add, Category.assoc] using comp_mem he (comp_mem hd hf)

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

/-- The selected E/F source isomorphism, retargeted to the prescribed weighted mate domain. -/
def contentBlockMatrixSourceIso :
    induced J ((restriction J).obj M) ≅ (restriction Q₁).obj (matrixMateArrow D Sc cutoff N i P).left :=
  composeIso (fullSquareSourceIso J Q₁ Q₀ T sqJ ((restriction J).obj M) ((restriction T).obj P)
      (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M))
    ((restriction Q₁).mapIso (eqToIso (matrixMateArrow_source D Sc cutoff N i P).symm))

/-- The selected F/E target isomorphism, retargeted to the prescribed weighted mate codomain. -/
def contentBlockMatrixTargetIso :
    (restriction K).obj (induced K M) ≅ (restriction Q₁).obj (matrixMateArrow D Sc cutoff N i P).right :=
  composeIso3 ((restriction K).mapIso (fullSquareRestrictionIso K Q₂ Q₁ T sqK M))
    (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P))
    ((restriction Q₁).mapIso (eqToIso (matrixMateArrow_target D Sc cutoff N i P).symm))

/-- The value chart is the chosen fully faithful inclusion unit. -/
def contentBlockMatrixValueIso : M ≅ (restriction Q₁).obj P :=
  contentExtensionUnitIso D Sc cutoff N γ M

theorem contentBlockMatrixSourceIso_hom_mem :
    (contentBlockMatrixSourceIso D Sc cutoff N i β M).hom ∈ parity (R := k) _ _ 0 := by
  have hS := fullSquareSourceIso_hom_mem J Q₁ Q₀ T sqJ ((restriction J).obj M) ((restriction T).obj P)
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)
  have hE := map_mem (restriction Q₁) (eqToHom_mem (R := k) (matrixMateArrow_source D Sc cutoff N i P).symm)
  exact composeIso_mem _ _ hS hE

theorem contentBlockMatrixTargetIso_hom_mem :
    (contentBlockMatrixTargetIso D Sc cutoff N i β M).hom ∈ parity (R := k) _ _ 0 := by
  have hT := map_mem (restriction K) (fullSquareRestrictionIso_hom_mem K Q₂ Q₁ T sqK M)
  have hS := restrictionSquare_mem D Sc cutoff N γ [i] δ hK (induced T P)
  have hE := map_mem (restriction Q₁) (eqToHom_mem (R := k) (matrixMateArrow_target D Sc cutoff N i P).symm)
  exact composeIso3_mem _ _ _ hT hS hE

theorem contentBlockMatrixValueIso_hom_mem :
    (contentBlockMatrixValueIso D Sc cutoff N i β M).hom ∈ parity (R := k) _ _ 0 := by
  rw [contentBlockMatrixValueIso, contentExtensionUnitIso, fullyFaithfulUnitIso_hom]
  exact adjunctionUnit_mem Q₁ M

theorem contentBlockMatrixSourceIso_inv_mem :
    (contentBlockMatrixSourceIso D Sc cutoff N i β M).inv ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (contentBlockMatrixSourceIso_hom_mem D Sc cutoff N i β M)
theorem contentBlockMatrixTargetIso_inv_mem :
    (contentBlockMatrixTargetIso D Sc cutoff N i β M).inv ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (contentBlockMatrixTargetIso_hom_mem D Sc cutoff N i β M)
theorem contentBlockMatrixValueIso_inv_mem :
    (contentBlockMatrixValueIso D Sc cutoff N i β M).inv ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (contentBlockMatrixValueIso_hom_mem D Sc cutoff N i β M)

end OddMath.QuiverHecke.ELVOld
