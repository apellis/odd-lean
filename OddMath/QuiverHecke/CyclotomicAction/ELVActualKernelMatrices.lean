import OddMath.QuiverHecke.CyclotomicAction.ELVUnitKernelNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVFiniteKernelTensor

/-! # The actual finite coefficient-kernel matrices

The entries are the fixed signed mate, ordinary counit/dot rows and ordinary
unscaled unit/dot columns. The finite matrix maps are natural for every
ordinary-right coefficient arrow. No degree, inverse or grading premise is
introduced into their construction.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def kernelPiLift {C : Type u} {ι : Type} [Category.{u} C]
    (K : Cᵒᵖ ⥤ ModuleCat k) (L : ι → Cᵒᵖ ⥤ ModuleCat k) (e : ∀ a, K ⟶ L a) :
    K ⟶ BalancedKernelTensor.piKernel L where
  app v := ModuleCat.ofHom (LinearMap.pi (fun a => ((e a).app v).hom))
  naturality v w f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    change (e a).app w (K.map f x) = (L a).map f ((e a).app v x)
    exact congrArg (fun h : K.obj v ⟶ (L a).obj w => h x) ((e a).naturality f)

private theorem kernelPiLift_apply {C : Type u} {ι : Type} [Category.{u} C]
    (K : Cᵒᵖ ⥤ ModuleCat k) (L : ι → Cᵒᵖ ⥤ ModuleCat k) (e : ∀ a, K ⟶ L a)
    (v : Cᵒᵖ) (x : K.obj v) (a : ι) :
    (kernelPiLift K L e).app v x a = (e a).app v x := rfl

private theorem sum_kernel_apply {C : Type u} {ι : Type} [Category.{u} C]
    (K L : C ⥤ ModuleCat k) (s : Finset ι) (e : ι → (K ⟶ L)) (v : C) (x : K.obj v) :
    ((∑ a ∈ s, e a).app v) x = ∑ a ∈ s, (e a).app v x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    change (e a).app v x + ((∑ b ∈ s, e b).app v) x = _
    rw [ih]

private theorem projection_comp_apply {C : Type u} {ι : Type} [Category.{u} C]
    (K : ι → Cᵒᵖ ⥤ ModuleCat k) (L : Cᵒᵖ ⥤ ModuleCat k) (a : ι) (e : K a ⟶ L)
    (v : Cᵒᵖ) (x : (BalancedKernelTensor.piKernel K).obj v) :
    ((BalancedKernelTensor.piProjection K a ≫ e).app v) x = e.app v (x a) := rfl

/-- The actual finite target coefficient family for the cap-row matrix. -/
def negativeKernelFamily (i : I) (m : ℕ) (t : OldCategory D Sc cutoff) :
    Option (Fin m) → (OldCategory D Sc cutoff)ᵒᵖ ⥤ ModuleCat k
  | none => BalancedKernelTensor.inductionKernel (append D Sc cutoff i)
      ((append D Sc cutoff i).obj t)
  | some _ => BalancedKernelTensor.inductionKernel (𝟭 (OldCategory D Sc cutoff)) t

private def negativeKernelEntry (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (a : Option (Fin m)) :
    IndResKernel.kernel (k := k) (append D Sc cutoff i) t ⟶ negativeKernelFamily D Sc cutoff i m t a :=
  match a with
  | none => mateKernel D Sc cutoff i t
  | some r => capKernel D Sc cutoff i r.val t

/-- The matrix whose rows are the actual mate and actual ordinary counit/dot powers. -/
def negativeKernelMap (i : I) (m : ℕ) (t : OldCategory D Sc cutoff) :
    IndResKernel.kernel (k := k) (append D Sc cutoff i) t ⟶
      BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i m t) :=
  kernelPiLift _ _ (negativeKernelEntry D Sc cutoff i m t)

@[simp] theorem negativeKernelMap_none (i : I) (m : ℕ)
    (v t : OldCategory D Sc cutoff)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    (negativeKernelMap D Sc cutoff i m t).app (op v) z none =
      mateKernelComponent D Sc cutoff i v t z := by
  rw [negativeKernelMap, kernelPiLift_apply]
  exact mateKernel_apply D Sc cutoff i v t z

@[simp] theorem negativeKernelMap_some (i : I) (m : ℕ)
    (v t : OldCategory D Sc cutoff) (r : Fin m)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    (negativeKernelMap D Sc cutoff i m t).app (op v) z (some r) =
      capKernelComponent D Sc cutoff i r.val v t z := by
  rw [negativeKernelMap, kernelPiLift_apply]
  rfl

/-- The actual finite source coefficient family for the unit-column matrix. -/
def positiveKernelFamily (i : I) (m : ℕ) (t : OldCategory D Sc cutoff) :
    Option (Fin m) → (OldCategory D Sc cutoff)ᵒᵖ ⥤ ModuleCat k
  | none => IndResKernel.kernel (k := k) (append D Sc cutoff i) t
  | some _ => BalancedKernelTensor.inductionKernel (𝟭 (OldCategory D Sc cutoff)) t

private def positiveKernelEntry (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (a : Option (Fin m)) :
    positiveKernelFamily D Sc cutoff i m t a ⟶
      BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
        ((append D Sc cutoff i).obj t) :=
  match a with
  | none => mateKernel D Sc cutoff i t
  | some r => unitKernel D Sc cutoff i r.val t

/-- The matrix with the actual mate and actual unscaled ordinary unit/dot columns. -/
def positiveKernelMap (i : I) (m : ℕ) (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t) ⟶
      BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
        ((append D Sc cutoff i).obj t) :=
  ∑ a : Option (Fin m),
    BalancedKernelTensor.piProjection (positiveKernelFamily D Sc cutoff i m t) a ≫
      positiveKernelEntry D Sc cutoff i m t a

theorem positiveKernelMap_apply (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff)
    (z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj (op v)) :
    (positiveKernelMap D Sc cutoff i m t).app (op v) z =
      mateKernelComponent D Sc cutoff i v t (z none) +
        ∑ r : Fin m, unitKernelComponent D Sc cutoff i r.val v t (z (some r)) := by
  rw [positiveKernelMap, sum_kernel_apply]
  simp only [projection_comp_apply]
  rw [Fintype.sum_option]
  exact congrArg₂ (fun x y => x + y)
    (mateKernel_apply D Sc cutoff i v t (z none))
    (Finset.sum_congr rfl (fun _ _ => rfl))

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
