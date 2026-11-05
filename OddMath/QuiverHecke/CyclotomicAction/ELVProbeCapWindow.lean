import OddMath.QuiverHecke.CyclotomicAction.ELVProbeLeftCapField
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeUnitCoefficientWindow
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldVacuumPolynomial

/-! # Native probe cap normalization

The last inverse-unit row in `SwappedVacuumNonpositiveBubbles.md`, §2,
extracts the prescribed native unit/dot column. The selected scalar charts
are cancelled, retaining the actual module unit, dot and coefficient cap.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
universe u

private theorem inverseRow_window_cancel
    {k V W S T : Type u} [CommRing k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup S] [Module k S] [AddCommGroup T] [Module k T]
    (v : V ≃ₗ[k] W) (c : S →ₗ[k] T)
    (f : S →ₗ[k] V) (g : T →ₗ[k] W) (a : V →ₗ[k] S) (b : W →ₗ[k] T)
    (hf : v.toLinearMap ∘ₗ f = g ∘ₗ c)
    (ha : c ∘ₗ a = b ∘ₗ v.toLinearMap)
    (q : Prop) [Decidable q] (hg : g ∘ₗ b = if q then LinearMap.id else 0) :
    f ∘ₗ a = if q then LinearMap.id else 0 := by
  apply LinearMap.ext
  intro x
  apply v.injective
  have h : v (f (a x)) = (g ∘ₗ b) (v x) := by
    calc
      _ = g (c (a x)) := LinearMap.congr_fun hf (a x)
      _ = g (b (v x)) := congrArg g (LinearMap.congr_fun ha x)
      _ = _ := rfl
  rw [hg] at h
  by_cases hq : q
  · simpa only [hq, ↓reduceIte, LinearMap.id_apply, LinearMap.comp_apply] using h
  · simpa only [hq, ↓reduceIte, LinearMap.zero_apply, map_zero, LinearMap.comp_apply] using h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N) (i : I) (hi : i ∉ γ)
  (w : OldContentCategory D Sc (probeCutoff D m) γ)
local notation "cut" => probeCutoff D m
local notation "count" => contentUnitCount D cut i (γ : Multiset I)
local notation "K" => oldContentAppend D Sc cut γ i
include hN

/-- The actual native prescribed cap extracts its own given dotted-unit
column, with the canonical inverse-row unshift and no additional scalar. -/
theorem probeContentCoefficientCap_unitDot (r : Fin count) (a : ℕ) (ha : a < count) :
    SVec.toLinearMap ((contentCoefficientCap D Sc cut γ i N
      (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r).total w) ∘ₗ
      unitDotLinear K (probeOldContentAppendDot_supernatural D Sc m γ i) N a w =
    if a = r.val then LinearMap.id else 0 := by
  classical
  exact inverseRow_window_cancel
    (probeOutputValueLinearEquiv D Sc m γ N hN w)
    (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap _ _ _ _
    (probeMissingColourUnitCoefficient_cap D Sc m γ N hN i hi w r)
    (probeOutputFELinearEquiv_unitDot D Sc m γ N hN i w a) _
    (probeMissingColourUnitCoefficient_unitDot D Sc m γ N hN i hi w r a ha)

/-- The same native window on the component of the actual module
unit/dot column, rather than a separately specified coend operator. -/
theorem probeContentCoefficientCap_unitDotColumn
    (r : Fin count) (a : ℕ) (ha : a < count) :
    SVec.toLinearMap ((contentCoefficientCap D Sc cut γ i N
      (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r).total w) ∘ₗ
      SVec.toLinearMap ((unitDotColumn K
        (probeOldContentAppendDot_supernatural D Sc m γ i) N a).total w) =
    if a = r.val then LinearMap.id else 0 := by
  rw [unitDotColumn_total]
  exact probeContentCoefficientCap_unitDot D Sc m γ N hN i hi w r a ha

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []
local notation "s" => probeOldVacuumObject D Sc m

/-- The actual native dot on the same F/E probe superspace as the cap. -/
abbrev dot (i : I) : End ((source D Sc m i).obj s) :=
  restrictedDotComponent (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N s

/-- The given ordinary unit applied to the literal ground coordinate. -/
def unitVector (i : I) (c : k) : (source D Sc m i).obj s :=
  ((adjunction (K i)).unit.app N).total s ((probeVacuumScalarEquiv D Sc m) c)

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
