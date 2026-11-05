import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeQuotientInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridComposition

/-! # The literal equal-colour crossing under scalar probe specialization

The two-letter generator comparison in DeformedActionAssembly §§5–6 and
DeformedMatrixComparison (2), (4) retains the existing `crossLast` component,
its parity twist, and the prescribed extra minus on induced crossings.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "J" => ELVOld.oldContentAppend D Sc cut ν i
local notation "K" => ELVOld.oldContentAppend D Sc cut (i :: ν) i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "S" => probeOrdinaryAppend D Sc m (i :: ν) i
local notation "Q₀" => probeOldOrdinaryFunctor D Sc m ν
local notation "Q₂" => probeOldOrdinaryFunctor D Sc m (i :: i :: ν)

variable (M : Superfunctor k (OrdinaryContentCategory D Sc
  (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))

end OddMath.QuiverHecke
