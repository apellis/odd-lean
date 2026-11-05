import OddMath.QuiverHecke.CyclotomicAction.ELVActualKernelMatrices
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight
import OddMath.QuiverHecke.CyclotomicAction.ELVFiniteMatrixComponents

/-! # Canonical coordinates for the actual coefficient-kernel matrices

Canonical-coordinate prerequisite for DeformedMatrixComparison, section 4.
This file does not assert coefficient-matrix bijectivity or arbitrary-module inversion.
The ordinary-right finite coefficient families use the literal IndRes
kernel and identity Hom kernels. These coordinates match their prescribed
mate/unit/cap maps with the actual component inverses.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Literal kernel-object coordinates on the existing actual ordinary source. -/
def kernelSourceCoordinates (i : I) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff) :
    (IndResKernel.kernel (k := k) (append D Sc cutoff i) t).obj v ≃ₗ[k]
      (unshiftedSourceModule D Sc cutoff i v.unop.word).obj t :=
  oldSourceKernelEquiv D Sc cutoff i v.unop t

/-- The ordinary Option-family source splits into its actual source and coefficient vector. -/
def positiveKernelCoordinates (i : I) (m : ℕ) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff) :
    (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj v ≃ₗ[k]
      ((unshiftedSourceModule D Sc cutoff i v.unop.word).obj t ×
        (Fin m → Old D Sc cutoff v.unop.word t.word)) :=
  (LinearEquiv.piOptionEquivProd k).trans
    ((kernelSourceCoordinates D Sc cutoff i v t).prodCongr
      (LinearEquiv.refl k (Fin m → Old D Sc cutoff v.unop.word t.word)))

/-- The ordinary Option-family target is the canonical upper Hom and coefficient vector. -/
def negativeKernelCoordinates (i : I) (m : ℕ) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff) :
    (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i m t)).obj v ≃ₗ[k]
      (Old D Sc cutoff (v.unop.word ++ [i]) (t.word ++ [i]) ×
        (Fin m → Old D Sc cutoff v.unop.word t.word)) :=
  LinearEquiv.piOptionEquivProd k

@[simp] theorem negativeKernelCoordinates_fst (i : I) (m : ℕ)
    (v : (OldCategory D Sc cutoff)ᵒᵖ) (t : OldCategory D Sc cutoff)
    (z : (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i m t)).obj v) :
    (negativeKernelCoordinates D Sc cutoff i m v t z).1 = z none := rfl

@[simp] theorem negativeKernelCoordinates_snd (i : I) (m : ℕ)
    (v : (OldCategory D Sc cutoff)ᵒᵖ) (t : OldCategory D Sc cutoff)
    (z : (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i m t)).obj v)
    (r : Fin m) :
    (negativeKernelCoordinates D Sc cutoff i m v t z).2 r = z (some r) := rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
