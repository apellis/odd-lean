import OddMath.QuiverHecke.CyclotomicAction.ELVActualKernelMatrices
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixComponents

/-! # Canonical coordinates for the actual coefficient-kernel matrices
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
      (actualUnshiftedSourceModule D Sc cutoff i v.unop.word).obj t :=
  oldSourceKernelEquiv D Sc cutoff i v.unop t

/-- At literal old words, the coordinates are the stored source linear map. -/
theorem kernelSourceCoordinates_boxed (i : I) (v t : List I)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i)
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)) :
    kernelSourceCoordinates D Sc cutoff i (op ⟨v⟩) ⟨t⟩ z =
      oldSourceKernelLinear D Sc cutoff i v t z := rfl

/-- The ordinary Option-family source splits into its actual source and coefficient vector. -/
def positiveKernelCoordinates (i : I) (m : ℕ) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff) :
    (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj v ≃ₗ[k]
      ((actualUnshiftedSourceModule D Sc cutoff i v.unop.word).obj t ×
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

@[simp] theorem positiveKernelCoordinates_fst (i : I) (m : ℕ)
    (v : (OldCategory D Sc cutoff)ᵒᵖ) (t : OldCategory D Sc cutoff)
    (z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj v) :
    (positiveKernelCoordinates D Sc cutoff i m v t z).1 =
      kernelSourceCoordinates D Sc cutoff i v t (z none) := rfl

@[simp] theorem positiveKernelCoordinates_snd (i : I) (m : ℕ)
    (v : (OldCategory D Sc cutoff)ᵒᵖ) (t : OldCategory D Sc cutoff)
    (z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj v)
    (r : Fin m) :
    (positiveKernelCoordinates D Sc cutoff i m v t z).2 r = z (some r) := rfl

@[simp] theorem negativeKernelCoordinates_fst (i : I) (m : ℕ)
    (v : (OldCategory D Sc cutoff)ᵒᵖ) (t : OldCategory D Sc cutoff)
    (z : (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i m t)).obj v) :
    (negativeKernelCoordinates D Sc cutoff i m v t z).1 = z none := rfl

@[simp] theorem negativeKernelCoordinates_snd (i : I) (m : ℕ)
    (v : (OldCategory D Sc cutoff)ᵒᵖ) (t : OldCategory D Sc cutoff)
    (z : (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i m t)).obj v)
    (r : Fin m) :
    (negativeKernelCoordinates D Sc cutoff i m v t z).2 r = z (some r) := rfl

/-- The literal kernel-object mate coefficient is the actual inverted mate row. -/
theorem actualMateKernelLinear_row (i : I) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff)
    (z : (IndResKernel.kernel (k := k) (append D Sc cutoff i) t).obj v) :
    actualMateKernelLinear D Sc cutoff i v t z =
      matrixMateRow D Sc cutoff i v.unop.word t.word
        (kernelSourceCoordinates D Sc cutoff i v t z) := by
  rcases v with ⟨⟨v⟩⟩
  rcases t with ⟨t⟩
  have h := actualMateKernelComponent_row D Sc cutoff i v t z
  have hc := kernelSourceCoordinates_boxed D Sc cutoff i v t z
  exact h.trans (congrArg (matrixMateRow D Sc cutoff i v t) hc.symm)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
