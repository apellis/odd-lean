/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.NativeCyclic.MixedLeading
import OddMath.CoveringQuantum.UDot.NativeCyclic.IntegrableTensor
import OddMath.CoveringQuantum.UDot.TriangularTensor

/-! Native cyclic evaluation on the original Serre tensor. -/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.NativeCyclic
open PreF Coefficients TensorProduct NativeLeading
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (Λ Μ : X)

/-- Application of an actual tensor endomorphism to the highest/lowest vacuum. -/
def vacuumApply : Module.End Coefficients.Ring
    (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ) →ₗ[Coefficients.Ring]
    (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ) where
  toFun f := f (toIntegrable D Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D Μ 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The native cyclic map, not the different regular tensor evaluation. -/
def cyclic (s : Bool) :
    D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
    (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ) :=
  (vacuumApply D Λ Μ).comp ((tensorRepresentation D Λ Μ s).toLinearMap.comp
    (triangularTensor D Coefficients.q pi (Λ - Μ)))

/-- Word tensors in the original, unquotiented Serre halves. -/
def wordTensor (a b : List I) :=
  D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
    D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)

/-- This is literally the published native normal-word action. -/
theorem cyclic_wordTensor (s : Bool) (a b : List I) :
    cyclic D Λ Μ s (wordTensor D a b) =
      tensorRepresentation D Λ Μ s (normalWord D Coefficients.q pi a b (Λ - Μ))
        (toIntegrable D Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D Μ 1) := by
  simp only [cyclic, LinearMap.comp_apply, AlgHom.toLinearMap_apply, wordTensor,
    triangularTensor_monomial, vacuumApply, LinearMap.coe_mk, AddHom.coe_mk]

/-- The accepted leading term now stated for the actual cyclic linear map. -/
theorem cyclic_wordTensor_leading (s : Bool) (a b : List I) :
    IsUnit (leadingScalar D Λ Μ s a b) ∧
    ∃ r ∈ lowerBidegree D Λ Μ a.length b.length,
      cyclic D Λ Μ s (wordTensor D a b) =
        leadingScalar D Λ Μ s a b • toIntegrableTensor D Λ Μ (wordTensor D a b) + r := by
  rw [cyclic_wordTensor]
  exact normalWord_leading D Λ Μ s a b

end OddMath.CoveringQuantum.UDot.GenericVerma.NativeCyclic
