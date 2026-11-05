import OddMath.Algebra.FiniteZeroCoordinate
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentColour
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixInverse

/-! # The unit matrix at a missing-colour output

Brundan--Ellis (1.13), and DeformedMatrixComparison (4), at output content
containing no i. The lower E/F summand is zero. Dropping that principal
coordinate from the GIVEN old matrix inverse gives precisely the finite
family of prescribed shifted unit-dot columns, including empty output.
Comparison with the ordinary scalar probe is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction OddMath.FiniteSuperspace
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
  (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
local notation "G" => induced (oldContentInclusion D Sc cutoff γ) N
local notation "count" => contentUnitCount D cutoff i (γ : Multiset I)

/-- The remaining canonical shifted value coordinates after removing zero E/F. -/
def missingColourUnitSource (w : OldContentCategory D Sc cutoff γ) : SVec k :=
  withoutPrincipal (fun a => (unitMatrixFamily D Sc cutoff i G count a).obj w.obj)

/-- The GIVEN global unit inverse, with only the proved-zero principal
coordinate removed. No matrix compatibility premise is required. -/
def missingColourUnitMatrixIso (w : OldContentCategory D Sc cutoff γ) :
    missingColourUnitSource D Sc cutoff γ i N w ≅ mateTargetSpace D Sc cutoff i G w.obj :=
  (SVec.isoOfLinearEquiv (dropZeroPrincipalEquiv
    (fun a => (unitMatrixFamily D Sc cutoff i G count a).obj w.obj)
    (oldContentUnitPrincipal_subsingleton_of_not_mem D Sc cutoff γ i hi N count w.obj))).symm ≪≫
  contentUnitMatrixComponentIso D Sc cutoff G i γ
    (contentCrossingHeight_nonneg_of_not_mem D cutoff γ i hi) w

/-- The forward field is literally the finite assembly of the GIVEN shifted
unit-dot columns. The zero principal mate column has disappeared. -/
theorem missingColourUnitMatrixIso_hom (w : OldContentCategory D Sc cutoff γ) :
    (missingColourUnitMatrixIso D Sc cutoff γ i hi N w).hom =
      assembleColumns
        (fun r : Fin count => (unitMatrixFamily D Sc cutoff i G count (some r)).obj w.obj)
        (mateTargetSpace D Sc cutoff i G w.obj)
        (fun r => (unitMatrixEntry D Sc cutoff i G count (some r)).total w.obj) := by
  change (SVec.isoOfLinearEquiv (dropZeroPrincipalEquiv _ _)).inv ≫
    (contentUnitMatrixComponentIso D Sc cutoff G i γ _ w).hom = _
  rw [contentUnitMatrixComponentIso_hom]
  exact dropZeroPrincipalEquiv_columns _ _ _ _

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
