import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerMomentMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVEndEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerNonpositiveCap

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

private theorem unitDotColumn_post_dot_power
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (J : C ⥤ C) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (a n : ℕ) :
    unitDotColumn J hα M n ≫ restrictedDotEnd J hα M ^ a = unitDotColumn J hα M (a + n) := by
  rw [unitDotColumn_eq_restrictedDotEnd, unitDotColumn_eq_restrictedDotEnd, Category.assoc]
  congr 1
  change restrictedDotEnd J hα M ^ a * restrictedDotEnd J hα M ^ n =
    restrictedDotEnd J hα M ^ (a + n)
  exact (pow_add _ _ _).symm

private theorem unitDotColumn_post_dot_power_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (J : C ⥤ C) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (a n : ℕ) (w : C) (b : M.obj w) :
    (restrictedDotEnd J hα M ^ a).total w ((unitDotColumn J hα M n).total w b) =
      (unitDotColumn J hα M (a + n)).total w b := by
  have h := congrArg (fun f => f.total w) (unitDotColumn_post_dot_power J hα M a n)
  rw [Superfunctor.comp_total] at h
  simpa only [SVec.comp_apply] using congrArg (fun f => f b) h

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

/-- Apply a given native module endomorphism before the actual prescribed
coefficient cap. The cap and both endpoints remain fixed. -/
def weightedCapAfter (i : I) (hN : 0 < cutoff i)
    (f : End ((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM))) :
    (restriction Q₀).obj ((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM)) ⟶ (restriction Q₀).obj WM :=
  (restriction Q₀).map f ≫ weightedCoefficientCap D Sc cutoff i L hN

/-- The actual weighted module-cap polynomial lambda(D^2+1)^M. -/
def weightedPolynomialCap (i : I) (hN : 0 < cutoff i) (M : ℕ) :=
  weightedCapAfter D Sc cutoff L i hN ((weightedModuleDot D Sc cutoff L i ^ 2 + 1) ^ M)

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

/-- These evaluations are exactly the closures of the actual module cap,
including its canonical output restriction and original empty coordinate. -/
theorem weightedCapMomentLinear_capAfter (i : I) (hN : 0 < cutoff i) (n : ℕ)
    (f : End ((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM))) (a : AQ) :
    weightedCapMomentLinear D Sc cutoff L i hN n f a =
      (weightedEmptyEquiv D Sc cutoff L).symm
        ((weightedCapAfter D Sc cutoff L i hN f).total
          (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff bound 0)
          ((unitDotColumn (truncatedAppend D Sc cutoff bound [i])
            (truncatedDot_supernatural D Sc cutoff bound i) WM n).total ((Q).obj ⟨[]⟩)
              (weightedEmptyEquiv D Sc cutoff L a))) := by
  rw [weightedCapAfter, Superfunctor.comp_total, SVec.comp_apply]
  exact weightedFunctional_coefficientCap D Sc cutoff i L hN _

/-- Powers of the same native restricted dot shift the actual weighted
moment exponent, with no independently specified component operator. -/
theorem weightedCapMomentLinear_pow (i : I) (hN : 0 < cutoff i) (n a : ℕ) :
    weightedCapMomentLinear D Sc cutoff L i hN n (weightedModuleDot D Sc cutoff L i ^ a) =
      weightedMomentMap D Sc cutoff L i hN (a + n) := by
  apply LinearMap.ext
  intro z
  have h := unitDotColumn_post_dot_power_apply (truncatedAppend D Sc cutoff bound [i])
    (truncatedDot_supernatural D Sc cutoff bound i) WM a n ((Q).obj ⟨[]⟩)
    (weightedEmptyEquiv D Sc cutoff L z)
  exact congrArg (weightedFunctional D Sc cutoff L i hN) h

/-- All dotted-unit closures of the actual plus-one polynomial module cap. -/
def weightedPolynomialCapMoment (i : I) (hN : 0 < cutoff i) (M n : ℕ) : Module.End k AQ :=
  weightedCapMomentLinear D Sc cutoff L i hN n ((weightedModuleDot D Sc cutoff L i ^ 2 + 1) ^ M)

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELVOld
