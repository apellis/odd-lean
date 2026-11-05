import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerMomentMaps
import Mathlib.Data.Nat.Choose.Sum

/-! # Polynomial coefficient-extraction caps on the power vacuum

The candidate cap λg(y) in `SwappedVacuumNonpositiveBubbles.md`, §§3–4,
is evaluated using the original signed dot and the prescribed last inverse
row on literal A/T. Identification with the mixed inverse cap is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private abbrev polynomialCapTarget (i : I) :=
  mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩
private def polynomialCapDot (i : I) : Module.End k (polynomialCapTarget D Sc cutoff L i) :=
  inductionDot D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
    ((append D Sc cutoff i).obj ⟨[]⟩)

/-- The coefficient-extraction functional after the literal plus-one probe polynomial. -/
def polynomialCap (i : I) (hN : 0 < cutoff i) (M : ℕ) :
    polynomialCapTarget D Sc cutoff L i →ₗ[k] CoefficientPowerQuotient (k := k) D cutoff L :=
  (functional D Sc cutoff L i hN).comp ((polynomialCapDot D Sc cutoff L i ^ 2 + 1) ^ M)

private def capMomentLinear (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    Module.End k (polynomialCapTarget D Sc cutoff L i) →ₗ[k]
      Module.End k (CoefficientPowerQuotient (k := k) D cutoff L) where
  toFun f := (functional D Sc cutoff L i hN).comp
    (f.comp ((polynomialCapDot D Sc cutoff L i ^ n).comp (unit D Sc cutoff L i)))
  map_add' f g := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' r f := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

end OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
