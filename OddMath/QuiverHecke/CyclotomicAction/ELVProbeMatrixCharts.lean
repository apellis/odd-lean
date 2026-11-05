import OddMath.QuiverHecke.CyclotomicAction.ELVProbeShiftedUnitComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVParityMatrixCoordinates

/-! # Selected scalar charts for the prescribed finite matrices

DeformedMatrixComparison (4), (5) requires genuine invertible charts on the
source and target of each matrix. These are the selected scalar append
isomorphisms, including the induced restriction equality in the E/F source.
The charts are independent of the matrix's invertibility.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u

section AppendCharts
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
  (R : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hR : ProbeEvaluatesCoefficients D m Sc ν R)
  (M : Superfunctor k (OrdinaryContentCategory D Sc
    (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))
  (c : probeOrdinaryModuleSuperfunctor D Sc m ν R hR ≅ M) (i : I)
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m ν R hR

/-- The original chosen append isomorphism on its literal old/ordinary coends. -/
def probeAppendLinearEquiv (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    Obj J R.toFunctor w ≃ₗ[k] Obj T (O).toFunctor ((U).obj w) :=
  moduleIsoLinearEquiv (probeAppendOrdinaryModuleIso D Sc m ν R hR i) ((U).obj w)

end AppendCharts

section MatrixCharts
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "K" => ELVOld.oldContentAppend D Sc (probeCutoff D m) (i :: ν) i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN
local notation "R" => Functor.obj (restriction J) N
local notation "hR" => probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
local notation "c" => eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)

end MatrixCharts
end OddMath.QuiverHecke
