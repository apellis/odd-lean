import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMateComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVOperatorPowerComparison

/-! # Given signed dot powers under mapped scalar append comparison

The dotted unit and cap entries in DeformedMatrixComparison (1), (2), (5)
use powers of the same signed dot. An independent intermediate module keeps
the selected append and restriction comparisons on their literal coends.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
  (R : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hR : ProbeEvaluatesCoefficients D m Sc ν R)
  (M : Superfunctor k (OrdinaryContentCategory D Sc
    (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))
  (c : probeOrdinaryModuleSuperfunctor D Sc m ν R hR ≅ M)
  (i : I) (hc : c.hom ∈ parity (R := k) _ _ 0)
include hc
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)

end OddMath.QuiverHecke
