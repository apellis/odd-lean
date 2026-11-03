import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendUpperLoop
import OddMath.SKM.RouquierBoundaryTransport

/-! # Missing-colour boundary rows for the stored upper append

Brundan–Ellis (1.13)–(1.14): the constructed evaluated missing-colour
coefficients follow the selected even upper-loop chart, whose prescribed
dotted-unit square is proved for every exponent. No matrix inverse or
chart-compatibility premise is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
universe u
attribute [local irreducible] oldAppendReindexIso probeAppendUpperLoopSuperIso
  probeEvaluatedMissingCoefficients
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ) (hi : i ∉ γ)

/-- The specified stored-target upper adjunction has the constructed finite
boundary coefficients, including count zero and every indexed inverse row. -/
def probeMissingStoredCoefficients :
    SKM.RouquierBoundary.Coefficients (probeAppendToRightAdjunction D Sc m γ i μ h)
      (probeAppendToInductionDot D Sc m γ i μ h) (D.parity i)
      (contentUnitCount D (probeCutoff D m) i (γ : Multiset I)) :=
  SKM.RouquierBoundaryTransport.ofIso (B := PiSCat.{u,u,u+1} k)
    (a := probeEvaluatedTarget D Sc m γ)
    (b := probeEvaluatedTarget D Sc m (i :: γ))
    (b' := probeEvaluatedTarget D Sc m μ)
    (E := probeEvaluatedE D Sc m γ i) (F := probeEvaluatedF D Sc m γ i)
    (E' := probeAppendToE D Sc m γ i μ h) (F' := probeAppendToF D Sc m γ i μ h)
    (A := probeEvaluatedRightAdjunction D Sc m γ i)
    (x := probeEvaluatedInductionDot D Sc m γ i)
    (probeEvaluatedMissingCoefficients D Sc m γ i hi)
    (probeAppendToRightAdjunction D Sc m γ i μ h)
    (probeAppendToInductionDot D Sc m γ i μ h)
    (probeAppendUpperLoopSuperIso D Sc m γ i h)
    (probeAppendUpperLoopSuperIso_hom_mem D Sc m γ i h)
    (probeAppendToInductionDot_mem D Sc m γ i μ h)
    (probeAppendUpperLoop_unitColumn D Sc m γ i h)

end OddMath.QuiverHecke
