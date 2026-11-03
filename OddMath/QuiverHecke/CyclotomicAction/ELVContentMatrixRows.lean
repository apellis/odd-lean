import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixRows

/-! # Prescribed dotted columns and rows under chosen content charts

DeformedMatrixComparison (4), (5) requires the given ordinary unit/dot and
dot/counit fields through the selected content comparisons. All dot powers
are retained before the canonical finite parity coordinates are applied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i
local notation "d₁" => oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i
local notation "d" => oldAppendDot_supernatural D Sc cutoff i

/-- Every prescribed unit/dot column is transported through the selected
following E/F and value charts, with no rescaling. -/
theorem oldContentFELinearEquiv_unitDot
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) (n : ℕ) (b : N.obj t) :
    oldContentFELinearEquiv D Sc cutoff ν i N t (unitDotLinear J₁ d₁ N n t b) =
      unitDotLinear J d (induced Q₁ N) n t.obj
        (oldContentValueLinearEquiv D Sc cutoff ν i N t b) := by
  let g := actualInductionDot D Sc cutoff i (induced Q₁ N) ((J₁).obj t).obj
  have hd := oldContentAppendRestrictionIso_dot D Sc cutoff (i :: ν) i N ((J₁).obj t)
  have hpn := intertwine_pow _ _ _ hd n
  have hp := LinearMap.congr_fun hpn (unit J₁ N.toFunctor t b)
  have hu := oldContentAppendRestrictionIso_unit D Sc cutoff (i :: ν) i N t b
  have hv := oldContentValueLinearEquiv_apply D Sc cutoff ν i N t b
  change oldContentValueLinearEquiv D Sc cutoff ν i N t b = unit Q₁ N.toFunctor t b at hv
  have hunit := congrArg (fun x => (g ^ n) x) hu
  have hvalue := congrArg (fun x => (g ^ n) (unit J (induced Q₁ N).toFunctor t.obj x)) hv
  have he := oldContentFELinearEquiv_apply D Sc cutoff ν i N t
    (unitDotLinear J₁ d₁ N n t b)
  have hraw := hp.trans (hunit.trans hvalue.symm)
  dsimp only [unitDotLinear, LinearMap.comp_apply] at he hraw ⊢
  dsimp only [Module.End] at he hraw ⊢
  have hfinal := he.trans hraw
  exact hfinal

end OddMath.QuiverHecke.ELVOld
