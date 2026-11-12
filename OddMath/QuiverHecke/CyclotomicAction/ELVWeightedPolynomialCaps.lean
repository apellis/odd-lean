import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerMomentMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVEndEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerMomentMaps
import Mathlib.Data.Nat.Choose.Sum

/-! # Polynomial caps of the actual weighted power vacuum

The coefficient cap lambda(D^2+1)^M in
`SwappedVacuumNonpositiveBubbles.md`, §§3–4, is a literal module map:
apply the polynomial in the given restricted module dot, then the
prescribed weighted inverse row. Its unit/dot closures are evaluated on
every A/T vector. Identification with the mixed inverse cap remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u

namespace PowerVacuumCoefficient
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "WM" => weightedVacuum D Sc cutoff L
local notation "Q" => oldTruncateFunctor D Sc cutoff bound
local notation "Q₀" => contentInclusion D Sc cutoff bound (0 : Multiset I)
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELVOld
