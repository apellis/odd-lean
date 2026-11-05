import OddMath.QuiverHecke.CyclotomicAction.ELVProbeLeftCapComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCoefficientCaps

/-! # The native prescribed left cap under the selected scalar chart

The inverse-defined left cap of DeformedMatrixComparison is the selected
F/E chart, prescribed inverse unit coefficient and inverse inclusion unit.
Its actual native module-map field is preserved by the original scalar
value and append charts, with the canonical row normalization unchanged.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
universe u

private theorem leftCap_field_total
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
    (γ : List I) (i : I) (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
    (hh : 0 ≤ contentCrossingHeight D cutoff i (γ : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (γ : Multiset I)))
    (w : OldContentCategory D Sc cutoff γ) :
    SVec.toLinearMap ((contentCoefficientCap D Sc cutoff γ i N hh r).total w) =
      (oldContentValueChart D Sc cutoff γ N w).symm.toLinearMap ∘ₗ
        SVec.toLinearMap ((contentUnitCoefficientMap D Sc cutoff
          (induced (oldContentInclusion D Sc cutoff γ) N) i γ hh r).total w) ∘ₗ
        (oldContentFEChart D Sc cutoff γ i N w).toLinearMap := by
  exact contentCoefficientCap_total D Sc cutoff γ i N hh r w

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N) (i : I) (hi : i ∉ γ)
  (w : OldContentCategory D Sc (probeCutoff D m) γ)
local notation "cut" => probeCutoff D m
local notation "count" => contentUnitCount D cut i (γ : Multiset I)

/-- The actual native prescribed inverse-defined left-cap field is carried
to the actual ordinary inverse coefficient by the selected scalar charts.
The ordinary right counit is not substituted for this field. -/
theorem probeMissingColourUnitCoefficient_cap (r : Fin count) :
    (probeOutputValueLinearEquiv D Sc m γ N hN w).toLinearMap ∘ₗ
      SVec.toLinearMap ((contentCoefficientCap D Sc cut γ i N
        (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r).total w) =
    SVec.toLinearMap (probeMissingColourUnitCoefficient D Sc m γ N hN i hi w r) ∘ₗ
      (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap := by
  have hCompare := probeMissingColourUnitCoefficient_relative D Sc m γ N hN i hi w r
  have hField := leftCap_field_total D Sc cut γ i N
    (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r w
  have h := linearSquare_reencode _ _ _ _ _ _ _ _ rfl hField rfl rfl hCompare
  exact h

end OddMath.QuiverHecke
