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

/-- Pointwise evaluation of the stored kernel coefficient equality. -/
theorem actualMateKernelLinear_apply_component (i : I)
    (v : (OldCategory D Sc cutoff)ᵒᵖ) (t : OldCategory D Sc cutoff)
    (z : (IndResKernel.kernel (k := k) (append D Sc cutoff i) t).obj v) :
    actualMateKernelLinear D Sc cutoff i v t z =
      actualMateKernelComponent D Sc cutoff i v.unop t z :=
  LinearMap.congr_fun (actualMateKernelLinear_eq_component D Sc cutoff i v t) z

/-- The stored kernel coefficient agrees with its matrix row on every source vector. -/
def KernelMateRowIdentity (i : I) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff) : Prop :=
  ∀ z : (IndResKernel.kernel (k := k) (append D Sc cutoff i) t).obj v,
    actualMateKernelLinear D Sc cutoff i v t z =
      matrixMateRow D Sc cutoff i v.unop.word t.word
        (kernelSourceCoordinates D Sc cutoff i v t z)

/-- The coefficient row at literal old-word endpoints. -/
theorem actualMateKernelLinear_row_boxed (i : I) (v t : List I) :
    KernelMateRowIdentity D Sc cutoff i (op ⟨v⟩) ⟨t⟩ := by
  intro z
  calc
    _ = actualMateKernelComponent D Sc cutoff i ⟨v⟩ ⟨t⟩ z :=
      actualMateKernelLinear_apply_component D Sc cutoff i (op ⟨v⟩) ⟨t⟩ z
    _ = matrixMateRow D Sc cutoff i v t (oldSourceKernelLinear D Sc cutoff i v t z) :=
      actualMateKernelComponent_row D Sc cutoff i v t z
    _ = _ := congrArg (matrixMateRow D Sc cutoff i v t)
      (kernelSourceCoordinates_boxed D Sc cutoff i v t z).symm

/-- Extend a predicate on literal words to the category wrappers. -/
private theorem oldWordPairs
    {P : (OldCategory D Sc cutoff)ᵒᵖ → OldCategory D Sc cutoff → Prop}
    (h : ∀ v t : List I, P (op ⟨v⟩) ⟨t⟩)
    (v : (OldCategory D Sc cutoff)ᵒᵖ) (t : OldCategory D Sc cutoff) : P v t := by
  rcases v with ⟨⟨v⟩⟩
  rcases t with ⟨t⟩
  exact h v t

/-- The literal kernel-object mate coefficient is the actual inverted mate row. -/
theorem actualMateKernelLinear_row (i : I) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff) : KernelMateRowIdentity D Sc cutoff i v t :=
  oldWordPairs D Sc cutoff
    (P := KernelMateRowIdentity D Sc cutoff i)
    (actualMateKernelLinear_row_boxed D Sc cutoff i) v t

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
