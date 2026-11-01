import OddMath.QuiverHecke.CyclotomicAction.ELVActualMatrixFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMateFirstRow
import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedMatrixFamilies

/-! # Ordinary-right covariance of the actual normalized mate kernel

The right coefficient action is ordinary precomposition b ↦ a ≫ b for
every arrow a, including inhomogeneous arrows. The actual mate formula
keeps b untwisted. Its co-Yoneda component therefore defines a natural map
between the concrete IndRes and upper Hom coefficient presheaves.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem equiv_total_comp_apply
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (t : C)
    {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] M.obj t) (H : N.obj t →ₗ[k] W) (z : V) :
    (H.comp ((SVec.toLinearMap (f.total t)).comp e.toLinearMap)) z =
      H (f.total t (e z)) := rfl

private def kernelNatTrans
    {C : Type u} [Category.{u} C] (K L : C ⥤ ModuleCat k)
    (f : ∀ v, K.obj v →ₗ[k] L.obj v)
    (hf : ∀ {v w} (a : v ⟶ w), (f w).comp (K.map a).hom = (L.map a).hom.comp (f v)) : K ⟶ L where
  app v := ModuleCat.ofHom (f v)
  naturality _ _ a := by
    apply ModuleCat.hom_ext
    exact hf a

private theorem kernelNatTrans_apply
    {C : Type u} [Category.{u} C] (K L : C ⥤ ModuleCat k)
    (f : ∀ v, K.obj v →ₗ[k] L.obj v)
    (hf : ∀ {v w} (a : v ⟶ w), (f w).comp (K.map a).hom = (L.map a).hom.comp (f v))
    (v : C) (z : K.obj v) : (kernelNatTrans K L f hf).app v z = f v z := rfl

/-- The representable coefficient functors agree literally in the old category. -/
def oldSourceKernelEquiv (i : I) (v t : OldCategory D Sc cutoff) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t ≃ₗ[k]
      (actualUnshiftedSourceModule D Sc cutoff i v.word).obj t := by
  cases v with
  | mk v => exact LinearEquiv.refl k _

@[simp] theorem oldSourceKernelEquiv_tensor (i : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : v ⟶ (append D Sc cutoff i).obj s) :
    oldSourceKernelEquiv D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
      BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff (⟨v.word⟩ : OldCategory D Sc cutoff))).toFunctor s g b := by
  cases v
  rfl

private theorem matrixMateRow_total (i : I) (v t : List I)
    (z : (actualUnshiftedSourceModule D Sc cutoff i v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    matrixMateRow D Sc cutoff i v t z =
      OldInductionRepresentable.upperHomEquiv D Sc cutoff i
        (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
        ((matrixMateComponent D Sc cutoff i
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
            (⟨t⟩ : OldCategory D Sc cutoff) z) := rfl

/-- The chosen actual mate, evaluated in canonical upper-Hom coordinates. -/
def actualMateKernelComponent (i : I) (v t : OldCategory D Sc cutoff) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) := by
  cases v with
  | mk v =>
    cases t with
    | mk t =>
      exact
        { toFun := fun z => matrixMateRow D Sc cutoff i v t
            (oldSourceKernelEquiv D Sc cutoff i ⟨v⟩ ⟨t⟩ z)
          map_add' := by
            intro x y
            simp only [map_add]
          map_smul' := by
            intro r x
            simp only [map_smul, RingHom.id_apply] }

/-- The stored mate row with both old endpoints in literal word coordinates. -/
theorem actualMateKernelComponent_row (i : I) (v t : List I)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i)
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)) :
    actualMateKernelComponent D Sc cutoff i ⟨v⟩ ⟨t⟩ z =
      matrixMateRow D Sc cutoff i v t
        (oldSourceKernelEquiv D Sc cutoff i ⟨v⟩ ⟨t⟩ z) := rfl

@[simp] theorem actualMateKernelComponent_tensor (i : I)
    (v s t : OldCategory D Sc cutoff) (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : v ⟶ (append D Sc cutoff i).obj s) :
    actualMateKernelComponent D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
    -((append D Sc cutoff i).map b ≫ equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i) ((append D Sc cutoff i).map g)) := by
  cases v with
  | mk v =>
    cases s with
    | mk s =>
      cases t with
      | mk t =>
        rw [actualMateKernelComponent_row]
        rw [oldSourceKernelEquiv_tensor, matrixMateRow_total]
        have hp : D.parity i * D.parity i = D.parity i := by
          rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
        have ht := oldModuleMate_upper_tensor D Sc cutoff i v s t g b
        rw [hp] at ht
        exact ht

theorem actualMateKernelComponent_precompose (i : I)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (actualMateKernelComponent D Sc cutoff i v t).comp
      (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t) =
    (Linear.leftComp k ((append D Sc cutoff i).obj t) ((append D Sc cutoff i).map a)).comp
      (actualMateKernelComponent D Sc cutoff i w t) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, IndResKernel.precompose_tensor,
    actualMateKernelComponent_tensor]
  change -((append D Sc cutoff i).map (a ≫ b) ≫ equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i) ((append D Sc cutoff i).map g)) =
    (append D Sc cutoff i).map a ≫
      (-((append D Sc cutoff i).map b ≫ equalCrossComponent D Sc cutoff i s ≫
        twist k (D.parity i) ((append D Sc cutoff i).map g)))
  rw [Functor.map_comp, Preadditive.comp_neg, Category.assoc]

/-- The same actual mate coefficient with literal kernel-object endpoints. -/
def actualMateKernelLinear (i : I) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff) :
    (IndResKernel.kernel (k := k) (append D Sc cutoff i) t).obj v →ₗ[k]
      (BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
        ((append D Sc cutoff i).obj t)).obj v :=
  actualMateKernelComponent D Sc cutoff i v.unop t

/-- The typed kernel-object coefficient is the fixed actual mate coefficient. -/
theorem actualMateKernelLinear_eq_component (i : I) (v : (OldCategory D Sc cutoff)ᵒᵖ)
    (t : OldCategory D Sc cutoff) :
    actualMateKernelLinear D Sc cutoff i v t =
      actualMateKernelComponent D Sc cutoff i v.unop t := rfl

/-- The actual normalized first entry is ordinary-right natural, not merely even-arrow natural. -/
def actualMateKernel (i : I) (t : OldCategory D Sc cutoff) :
    IndResKernel.kernel (k := k) (append D Sc cutoff i) t ⟶
      BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
        ((append D Sc cutoff i).obj t) :=
  kernelNatTrans _ _ (fun v => actualMateKernelLinear D Sc cutoff i v t)
    (fun a => actualMateKernelComponent_precompose D Sc cutoff i a.unop t)

@[simp] theorem actualMateKernel_apply (i : I) (v t : OldCategory D Sc cutoff)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    (actualMateKernel D Sc cutoff i t).app (op v) z =
      actualMateKernelComponent D Sc cutoff i v t z := by
  change actualMateKernelLinear D Sc cutoff i (op v) t z = _
  rw [actualMateKernelLinear_eq_component]
  simp only [Opposite.unop_op]
  exact LinearMap.congr_fun
    (rfl : actualMateKernelComponent D Sc cutoff i v t =
      actualMateKernelComponent D Sc cutoff i v t) z

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
