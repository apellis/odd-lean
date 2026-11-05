import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerMomentMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVEndEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerPolynomialCap

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

private def componentMomentLinear {k U : Type u} [CommRing k]
    [AddCommGroup U] [Module k U] (V : SVec k) (cap : V →ₗ[k] U) (cup : U →ₗ[k] V) :
    (Module.End k V) →ₗ[k] Module.End k U where
  toFun f := cap ∘ₗ f ∘ₗ cup
  map_add' f g := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' r f := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

namespace PowerVacuumCoefficient
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "WM" => weightedVacuum D Sc cutoff L
local notation "Q" => oldTruncateFunctor D Sc cutoff bound
local notation "Q₀" => contentInclusion D Sc cutoff bound (0 : Multiset I)
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L

/-- The given restricted dot, as an endomorphism of the actual weighted
F/E module before total evaluation. -/
abbrev weightedModuleDot (i : I) :=
  restrictedDotEnd (truncatedAppend D Sc cutoff bound [i])
    (truncatedDot_supernatural D Sc cutoff bound i) WM

/-- Linear evaluation of the given cap after native module endomorphisms,
with its prescribed n-th unit/dot column and original A/T coordinate. -/
def weightedCapMomentLinear (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    End ((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM)) →ₗ[k] Module.End k AQ :=
  (componentMomentLinear
    (((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM)).obj ((Q).obj ⟨[]⟩))
    (weightedFunctional D Sc cutoff L i hN)
    (SVec.toLinearMap ((unitDotColumn (truncatedAppend D Sc cutoff bound [i])
      (truncatedDot_supernatural D Sc cutoff bound i) WM n).total ((Q).obj ⟨[]⟩)) ∘ₗ
        (weightedEmptyEquiv D Sc cutoff L).toLinearMap)).comp
    ((svecEndEvaluation
      (((restriction (truncatedAppend D Sc cutoff bound [i])).obj
        ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM)).obj ((Q).obj ⟨[]⟩))).toLinearMap.comp
      (supernaturalTotalLinearMap _ _ ((Q).obj ⟨[]⟩)))

/-- All dotted-unit closures of the actual plus-one polynomial module cap. -/
def weightedPolynomialCapMoment (i : I) (hN : 0 < cutoff i) (M n : ℕ) : Module.End k AQ :=
  weightedCapMomentLinear D Sc cutoff L i hN n ((weightedModuleDot D Sc cutoff L i ^ 2 + 1) ^ M)

omit [Fintype I] in

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELVOld
