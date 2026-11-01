import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTransport
import OddMath.QuiverHecke.Basis
import Mathlib.RingTheory.Flat.Basic

/-! # Bounded coefficient windows tensored with affine Homs

The coefficient-specialization input of SwappedVacuumCoordinates §6.
The full bounded polynomial/exterior coefficient window survives tensoring
with an affine Hom because the proved PBW basis makes that Hom free.
No flatness of a coefficient quotient or detecting-action premise is assumed.
Cyclotomic and further coefficient-truncation detection are separate steps.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

abbrev coefficientWindowTensor (d : ℕ) (v w : List I) :=
  SKM.SYM.CoefficientAtMost D k d ⊗[k]
    ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w))

/-- The coefficient quotient on the whole bounded-coefficient/affine tensor. -/
def coefficientWindowMap (cutoff : I → ℕ) (d : ℕ) (v w : List I) :
    coefficientWindowTensor D Sc d v w →ₗ[k] ELVCoefficientHom D Sc cutoff v w :=
  TensorProduct.map
    ((SKM.SYM.elvCoefficientQuotient D cutoff).toLinearMap.comp
      (SKM.SYM.CoefficientAtMost D k d).subtype) LinearMap.id

@[simp] theorem coefficientWindowMap_tmul (cutoff : I → ℕ) (d : ℕ)
    (v w : List I) (a : SKM.SYM.CoefficientAtMost D k d)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    coefficientWindowMap D Sc cutoff d v w (a ⊗ₜ[k] f) =
      SKM.SYM.elvCoefficientQuotient D cutoff a.val ⊗ₜ[k] f := rfl

/-- The tensor injection uses the established affine PBW basis, including
all exterior coefficient products, over any commutative ground ring. -/
theorem coefficientWindowMap_injective (cutoff : I → ℕ) (d : ℕ)
    (hd : ∀ i, d ≤ cutoff i) (v w : List I) :
    Function.Injective (coefficientWindowMap D Sc cutoff d v w) := by
  let H := (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)
  let f : SKM.SYM.CoefficientAtMost D k d →ₗ[k]
      SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff :=
    (SKM.SYM.elvCoefficientQuotient D cutoff).toLinearMap.comp
      (SKM.SYM.CoefficientAtMost D k d).subtype
  have hf : Function.Injective f := by
    intro a b hab
    exact SKM.SYM.elvCoefficient_quotient_injective D k hd hab
  letI : Module.Free k H := Module.Free.of_basis (basisNF D Sc v w)
  change Function.Injective (f.rTensor H)
  exact Module.Flat.rTensor_preserves_injective_linearMap f hf

/-- Insert the same tensor into the full abstract coefficient Hom. -/
def coefficientWindowSourceMap (d : ℕ) (v w : List I) :
    coefficientWindowTensor D Sc d v w →ₗ[k]
      (coefficientObj D Sc v ⟶ coefficientObj D Sc w) :=
  (sourceTensorEquiv D Sc v w).toLinearMap.comp
    (TensorProduct.map (SKM.SYM.CoefficientAtMost D k d).subtype LinearMap.id)

@[simp] theorem coefficientWindowSourceMap_tmul (d : ℕ) (v w : List I)
    (a : SKM.SYM.CoefficientAtMost D k d)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    coefficientWindowSourceMap D Sc d v w (a ⊗ₜ[k] f) =
      sourceCoefficientHom D Sc a.val f := rfl

/-- This is a literal submodule of the source, not a replacement module. -/
def coefficientWindowSource (d : ℕ) (v w : List I) :
    Submodule k (coefficientObj D Sc v ⟶ coefficientObj D Sc w) :=
  LinearMap.range (coefficientWindowSourceMap D Sc d v w)

theorem elvHomQuotient_coefficientWindowSourceMap (cutoff : I → ℕ)
    (d : ℕ) (v w : List I) (x : coefficientWindowTensor D Sc d v w) :
    elvHomQuotient D Sc cutoff v w (coefficientWindowSourceMap D Sc d v w x) =
      coefficientWindowMap D Sc cutoff d v w x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a f =>
    rw [coefficientWindowSourceMap_tmul, elvHomQuotient_source,
      coefficientWindowMap_tmul]

/-- The prescribed full coefficient-quotient map is injective on this actual
source submodule, with no affine degree bound or faithfulness input. -/
theorem elvHomQuotient_injective_coefficientWindow (cutoff : I → ℕ)
    (d : ℕ) (hd : ∀ i, d ≤ cutoff i) (v w : List I) :
    Function.Injective (fun x : coefficientWindowSource D Sc d v w =>
      elvHomQuotient D Sc cutoff v w x.val) := by
  intro x y hxy
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := y.property
  have he : coefficientWindowMap D Sc cutoff d v w a =
      coefficientWindowMap D Sc cutoff d v w b := by
    rw [← elvHomQuotient_coefficientWindowSourceMap,
      ← elvHomQuotient_coefficientWindowSourceMap, ha, hb]
    exact hxy
  have hab := coefficientWindowMap_injective D Sc cutoff d hd v w he
  apply Subtype.ext
  exact ha.symm.trans ((congrArg (coefficientWindowSourceMap D Sc d v w) hab).trans hb)

end OddMath.QuiverHecke
