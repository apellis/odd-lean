import OddMath.QuiverHecke.CyclotomicAction.EvenInputMatrix
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.ContentAppend
import OddMath.QuiverHecke.CyclotomicAction.KernelDegree
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction

/-!
# Kernel matrix evaluation

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
end

end

section

/-! # Kernel tensor coordinates for the prescribed finite matrices

The underlying endpoint comparisons in DeformedMatrixComparison, section 4.
The many-object kernel quotients are identified with the existing induction,
restriction and finite shifted module families. Every shift uses its named
canonical parity isomorphism. No preservation of general categorical colimits
or flatness is assumed. Matrix-entry identification is a separate statement.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

local instance matrixCoordinatePi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

variable (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

/-- Evaluation of the identity induction quotient, with identity insertion inverse. -/
def identityInductionCoordinates (t : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (𝟭 (OldCategory D Sc cutoff)) M.toFunctor t ≃ₗ[k] M.obj t :=
  LinearEquiv.ofLinearMap
    (BalancedInduction.counit (𝟭 _) M.toFunctor t)
    (BalancedInduction.unit (𝟭 _) M.toFunctor t)
    (BalancedInduction.counit_unit (𝟭 _) M.toFunctor t)
    (BalancedInduction.unit_counit_of_full (𝟭 _) M.toFunctor t)

/-- The identity-Hom coefficient kernel evaluates on an arbitrary module. -/
def identityKernelCoordinates (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.Obj (BalancedKernelTensor.inductionKernel (k := k)
      (𝟭 (OldCategory D Sc cutoff)) t) M.toFunctor ≃ₗ[k] M.obj t :=
  (BalancedKernelTensor.inductionKernelEquiv (𝟭 _) M.toFunctor t).trans
    (identityInductionCoordinates D Sc cutoff M t)

@[simp] theorem identityKernelCoordinates_tensor (v t : OldCategory D Sc cutoff)
    (b : v ⟶ t) (m : M.obj v) :
    identityKernelCoordinates D Sc cutoff M t
      (BalancedKernelTensor.tensor (BalancedKernelTensor.inductionKernel (k := k)
        (𝟭 (OldCategory D Sc cutoff)) t) M.toFunctor v b m) = M.map b m := by
  change BalancedInduction.counit (𝟭 _) M.toFunctor t
    (BalancedInduction.tensor (𝟭 _) M.toFunctor v b m) = _
  exact BalancedInduction.counit_tensor (𝟭 _) M.toFunctor t v b m

/-- The IndRes coefficient tensor is the literal source of the cap matrix. -/
def indResKernelCoordinates (i : I) (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.Obj (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor ≃ₗ[k]
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t :=
  IndResKernel.equiv (append D Sc cutoff i) M.toFunctor t

/-- The upper Hom coefficient tensor is the literal target of the unit matrix. -/
def resIndKernelCoordinates (i : I) (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.Obj (BalancedKernelTensor.inductionKernel (k := k)
      (append D Sc cutoff i) ((append D Sc cutoff i).obj t)) M.toFunctor ≃ₗ[k]
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).obj t :=
  BalancedKernelTensor.inductionKernelEquiv (append D Sc cutoff i) M.toFunctor
    ((append D Sc cutoff i).obj t)

theorem indResKernelCoordinates_tensor (i : I) (v t : OldCategory D Sc cutoff)
    (x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) (m : M.obj v) :
    indResKernelCoordinates D Sc cutoff M i t
      (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
        M.toFunctor v x m) =
      IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m x :=
  IndResKernel.forward_tensor (append D Sc cutoff i) M.toFunctor t v x m

theorem resIndKernelCoordinates_tensor (i : I) (v t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) (m : M.obj v) :
    resIndKernelCoordinates D Sc cutoff M i t
      (BalancedKernelTensor.tensor (BalancedKernelTensor.inductionKernel (k := k)
        (append D Sc cutoff i) ((append D Sc cutoff i).obj t)) M.toFunctor v g m) =
      BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v g m :=
  BalancedKernelTensor.inductionKernelEquiv_tensor (append D Sc cutoff i) M.toFunctor
    ((append D Sc cutoff i).obj t) v g m

/-- Each unit-source slot uses exactly the canonical source parity coordinate. -/
def positiveSlotCoordinates (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (a : Option (Fin m)) :
    BalancedKernelTensor.Obj (positiveKernelFamily D Sc cutoff i m t a) M.toFunctor ≃ₗ[k]
      (unitMatrixFamily D Sc cutoff i M m a).obj t :=
  match a with
  | none => (indResKernelCoordinates D Sc cutoff M i t).trans
      (moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t).symm
  | some r => (identityKernelCoordinates D Sc cutoff M t).trans
      (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (r.val • D.parity i)).iso M) t).symm

/-- Each cap-target slot uses exactly the canonical target parity coordinate. -/
def negativeSlotCoordinates (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (a : Option (Fin m)) :
    BalancedKernelTensor.Obj (negativeKernelFamily D Sc cutoff i m t a) M.toFunctor ≃ₗ[k]
      (capMatrixFamily D Sc cutoff i M m a).obj t :=
  match a with
  | none => (resIndKernelCoordinates D Sc cutoff M i t).trans
      (moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t).symm
  | some r => (identityKernelCoordinates D Sc cutoff M t).trans
      (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (r.val • D.parity i)).iso M) t).symm

/-- Removing the named first source shift returns the IndRes kernel evaluation. -/
theorem positiveSlotCoordinates_none (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (z : BalancedKernelTensor.Obj (positiveKernelFamily D Sc cutoff i m t none) M.toFunctor) :
    moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t
        (positiveSlotCoordinates D Sc cutoff M i m t none z) =
      indResKernelCoordinates D Sc cutoff M i t z := by
  change moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t
      ((moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t).symm
        (indResKernelCoordinates D Sc cutoff M i t z)) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- Removing a named identity-slot source shift returns ordinary Hom evaluation. -/
theorem positiveSlotCoordinates_some (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (r : Fin m)
    (z : BalancedKernelTensor.Obj (positiveKernelFamily D Sc cutoff i m t (some r)) M.toFunctor) :
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (r.val • D.parity i)).iso M) t
        (positiveSlotCoordinates D Sc cutoff M i m t (some r) z) =
      identityKernelCoordinates D Sc cutoff M t z := by
  change moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
      (r.val • D.parity i)).iso M) t
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (r.val • D.parity i)).iso M) t).symm
          (identityKernelCoordinates D Sc cutoff M t z)) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- Removing the named first target shift returns the upper Hom kernel evaluation. -/
theorem negativeSlotCoordinates_none (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (z : BalancedKernelTensor.Obj (negativeKernelFamily D Sc cutoff i m t none) M.toFunctor) :
    moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t
        (negativeSlotCoordinates D Sc cutoff M i m t none z) =
      resIndKernelCoordinates D Sc cutoff M i t z := by
  change moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t
      ((moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t).symm
        (resIndKernelCoordinates D Sc cutoff M i t z)) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- Removing a named identity-slot target shift returns ordinary Hom evaluation. -/
theorem negativeSlotCoordinates_some (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (r : Fin m)
    (z : BalancedKernelTensor.Obj (negativeKernelFamily D Sc cutoff i m t (some r)) M.toFunctor) :
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (r.val • D.parity i)).iso M) t
        (negativeSlotCoordinates D Sc cutoff M i m t (some r) z) =
      identityKernelCoordinates D Sc cutoff M t z := by
  change moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
      (r.val • D.parity i)).iso M) t
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (r.val • D.parity i)).iso M) t).symm
          (identityKernelCoordinates D Sc cutoff M t z)) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- The finite source coend realizes the exact shifted unit-matrix source. -/
def positiveKernelCoordinates (i : I) (m : ℕ) (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t))
        M.toFunctor ≃ₗ[k] unitMatrixSourceSpace D Sc cutoff i M m t :=
  (BalancedKernelTensor.piEquiv (positiveKernelFamily D Sc cutoff i m t) M.toFunctor).trans
    (LinearEquiv.piCongrRight (positiveSlotCoordinates D Sc cutoff M i m t))

/-- The finite target coend realizes the exact shifted cap-matrix target. -/
def negativeKernelCoordinates (i : I) (m : ℕ) (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i m t))
        M.toFunctor ≃ₗ[k] capMatrixTargetSpace D Sc cutoff i M m t :=
  (BalancedKernelTensor.piEquiv (negativeKernelFamily D Sc cutoff i m t) M.toFunctor).trans
    (LinearEquiv.piCongrRight (negativeSlotCoordinates D Sc cutoff M i m t))

theorem positiveKernelCoordinates_apply (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (z : BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor)
    (a : Option (Fin m)) :
    positiveKernelCoordinates D Sc cutoff M i m t z a =
      positiveSlotCoordinates D Sc cutoff M i m t a
        (BalancedKernelTensor.map M.toFunctor
          (BalancedKernelTensor.piProjection (positiveKernelFamily D Sc cutoff i m t) a) z) := rfl

theorem negativeKernelCoordinates_apply (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (z : BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i m t)) M.toFunctor)
    (a : Option (Fin m)) :
    negativeKernelCoordinates D Sc cutoff M i m t z a =
      negativeSlotCoordinates D Sc cutoff M i m t a
        (BalancedKernelTensor.map M.toFunctor
          (BalancedKernelTensor.piProjection (negativeKernelFamily D Sc cutoff i m t) a) z) := rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
end

end

section

/-! # Kernel entries on arbitrary supermodules

The kernel transfer of DeformedMatrixComparison §4 must recover the prescribed
module transformations. These evaluation identities keep the ordinary-right
coefficient action and all inhomogeneous input vectors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D]
  (J : C ⥤ D) (M : C ⥤ SVec k)

/-- Insert a fixed module vector into a Hom-kernel coefficient. -/
def coefficientEvaluation (v : C) (w : D) (m : M.obj v) :
    (J.obj v ⟶ w) →ₗ[k] Obj J M w :=
  inclusion J M w v ∘ₗ (TensorProduct.mk k _ _).flip m

@[simp] theorem coefficientEvaluation_apply (v : C) (w : D)
    (m : M.obj v) (h : J.obj v ⟶ w) :
    coefficientEvaluation J M v w m h = tensor J M v h m := rfl

private theorem evaluation_pow {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (q : V →ₗ[k] W)
    (S : Module.End k V) (T : Module.End k W)
    (h : q.comp S = T.comp q) (n : ℕ) (x : V) :
    q ((S ^ n) x) = (T ^ n) (q x) := by
  have hc : Function.Semiconj q S T := fun x => LinearMap.congr_fun h x
  simpa only [Module.End.pow_apply] using hc.iterate_right n x

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (i : I) (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
  (v t : OldCategory D Sc cutoff) (m : M.obj v)

/-- On the double tensor generators, kernel evaluation is the actual mate. -/
theorem mateKernel_evaluate_tensor (s : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : v ⟶ (append D Sc cutoff i).obj s) :
    BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v
      (mateKernelComponent D Sc cutoff i v t
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b)) m =
      (matrixMateComponent D Sc cutoff i M).total t
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj M).toFunctor
          s g (M.map b m)) := by
  rw [mateKernelComponent_tensor]
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  have hh := oldModuleMate_total_tensor D Sc cutoff i M s t g (M.map b m)
  rw [hp] at hh
  change _ = ((oldModuleMate D Sc cutoff i).app (D.parity i) M).total t _
  rw [hh]
  have hn : BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v
      (-((append D Sc cutoff i).map b ≫ equalCrossComponent D Sc cutoff i s ≫
        twist k (D.parity i) ((append D Sc cutoff i).map g))) m =
      -BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v
        ((append D Sc cutoff i).map b ≫ equalCrossComponent D Sc cutoff i s ≫
          twist k (D.parity i) ((append D Sc cutoff i).map g)) m := by
    simp only [BalancedInduction.tensor, neg_tmul, map_neg]
  exact hn.trans (congrArg Neg.neg (BalancedInduction.balance (append D Sc cutoff i)
    M.toFunctor b (equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i) ((append D Sc cutoff i).map g)) m))

/-- Evaluation with the literal induced-restriction module endpoint. -/
def moduleSourceEvaluation :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t :=
  IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m

/-- The two ordinary quotient evaluations with a fixed input vector. -/
def kernelMateEvaluation :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i) M.toFunctor
        ((append D Sc cutoff i).obj t) :=
  (BalancedInduction.coefficientEvaluation (append D Sc cutoff i) M.toFunctor
    v ((append D Sc cutoff i).obj t) m).comp (mateKernelComponent D Sc cutoff i v t)

def moduleMateEvaluation :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i) M.toFunctor
        ((append D Sc cutoff i).obj t) :=
  (SVec.toLinearMap ((matrixMateComponent D Sc cutoff i M).total t)).comp
    (moduleSourceEvaluation D Sc cutoff i M v t m)

@[simp] theorem kernelMateEvaluation_tensor (s : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : v ⟶ (append D Sc cutoff i).obj s) :
    kernelMateEvaluation D Sc cutoff i M v t m
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
      BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v
        (mateKernelComponent D Sc cutoff i v t
          (BalancedInduction.tensor (append D Sc cutoff i)
            ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b)) m := rfl

@[simp] theorem moduleMateEvaluation_tensor (s : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : v ⟶ (append D Sc cutoff i).obj s) :
    moduleMateEvaluation D Sc cutoff i M v t m
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
      (matrixMateComponent D Sc cutoff i M).total t
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj M).toFunctor
          s g (M.map b m)) := by
  exact congrArg ((matrixMateComponent D Sc cutoff i M).total t)
    (IndResKernel.evaluate_tensor (append D Sc cutoff i) M.toFunctor v t m s g b)

/-- Evaluation intertwines the actual kernel dot with the actual module dot. -/
theorem dotKernel_evaluate :
    (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m).comp
        (dotKernelComponent D Sc cutoff i v t) =
      (inductionDot D Sc cutoff i
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t).comp
        (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m) := by
  apply BalancedInduction.hom_ext
  intro s g b
  change v ⟶ (append D Sc cutoff i).obj s at b
  change IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m
    (dotKernelComponent D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b)) =
    inductionDot D Sc cutoff i
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t
      (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b))
  rw [dotKernelComponent_tensor, IndResKernel.evaluate_tensor,
    IndResKernel.evaluate_tensor]
  exact (inductionDot_tensor D Sc cutoff i
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) s t g (M.map b m)).symm

/-- The kernel counit evaluates by the ordinary module counit. -/
theorem counitKernel_evaluate :
    ((M.toFunctor.mapLinearMap (R := k)).flip m).comp
        (counitKernelComponent D Sc cutoff i v t) =
      (BalancedInduction.counit (append D Sc cutoff i) M.toFunctor t).comp
        (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m) := by
  apply BalancedInduction.hom_ext
  intro s g b
  change v ⟶ (append D Sc cutoff i).obj s at b
  change M.map (counitKernelComponent D Sc cutoff i v t
    (BalancedInduction.tensor (append D Sc cutoff i)
      ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b)) m =
    BalancedInduction.counit (append D Sc cutoff i) M.toFunctor t
      (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b))
  rw [counitKernelComponent_tensor, IndResKernel.evaluate_tensor,
    BalancedInduction.counit_tensor]
  exact congrArg (fun f : M.obj v ⟶ M.obj t => f m) (M.toFunctor.map_comp b g)

/-- Every kernel dot power has the prescribed action on arbitrary module vectors. -/
theorem dotKernel_power_evaluate (n : ℕ)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m
        ((dotKernelComponent D Sc cutoff i v t ^ n) z) =
      (inductionDot D Sc cutoff i
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t ^ n)
        (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m z) :=
  BalancedInduction.evaluation_pow _ _ _ (dotKernel_evaluate D Sc cutoff i M v t m) n z

/-- Ordinary counit-dot powers retain the full module coefficient. -/
theorem capKernel_evaluate (n : ℕ)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    M.map (capKernelComponent D Sc cutoff i n v t z) m =
      BalancedInduction.counit (append D Sc cutoff i) M.toFunctor t
        ((inductionDot D Sc cutoff i
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t ^ n)
          (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m z)) := by
  change M.map (counitKernelComponent D Sc cutoff i v t
    ((dotKernelComponent D Sc cutoff i v t ^ n) z)) m = _
  have hc := LinearMap.congr_fun (counitKernel_evaluate D Sc cutoff i M v t m)
    ((dotKernelComponent D Sc cutoff i v t ^ n) z)
  change M.map (counitKernelComponent D Sc cutoff i v t
    ((dotKernelComponent D Sc cutoff i v t ^ n) z)) m =
    BalancedInduction.counit (append D Sc cutoff i) M.toFunctor t
      (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m
        ((dotKernelComponent D Sc cutoff i v t ^ n) z)) at hc
  exact hc.trans (congrArg (BalancedInduction.counit (append D Sc cutoff i) M.toFunctor t)
    (dotKernel_power_evaluate D Sc cutoff i M v t m n z))

/-- The total of the chosen even counit is the raw balanced evaluation. -/
theorem adjunctionCounit_total_apply
    (z : BalancedInduction.Obj (append D Sc cutoff i)
      ((append D Sc cutoff i) ⋙ M.toFunctor) t) :
    ((BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M).total t z =
      BalancedInduction.counit (append D Sc cutoff i) M.toFunctor t z := by
  simp only [BalancedInduction.adjunction, BalancedInduction.adjunctionCounit,
    Superfunctor.homMk, SuperNatTrans.total, BalancedInduction.counitTransform_app,
    ↓reduceIte, one_ne_zero, add_zero]
  rfl

/-- The kernel cap row evaluates to the literal ordinary categorical cap row. -/
theorem capKernel_evaluate_moduleCapRow (n : ℕ)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    M.map (capKernelComponent D Sc cutoff i n v t z) m =
      (moduleCapRow D Sc cutoff i M n).total t
        (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m z) := by
  let q := IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m z
  let T := inductionDot D Sc cutoff i
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t
  have hm := LinearMap.congr_fun (moduleCapRow_total D Sc cutoff i M t n) q
  change (moduleCapRow D Sc cutoff i M n).total t q =
    ((BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M).total t ((T ^ n) q) at hm
  have hc := adjunctionCounit_total_apply D Sc cutoff i M t ((T ^ n) q)
  exact (capKernel_evaluate D Sc cutoff i M v t m n z).trans (hm.trans hc).symm

/-- The unscaled unit/dot kernel column evaluates to the ordinary module column. -/
theorem unitKernel_evaluate (n : ℕ) (b : v ⟶ t) :
    BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v
      (unitKernelComponent D Sc cutoff i n v t b) m =
      (moduleUnitColumn D Sc cutoff i M n).total t (M.map b m) := by
  let P : (append D Sc cutoff i).obj t ⟶ (append D Sc cutoff i).obj t :=
    (ideal D Sc cutoff _ _).mkQ (appendMovingPower D Sc cutoff i t.word n)
  have hp := inductionDot_iterate_unit D Sc cutoff i M t n (M.map b m)
  change (inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t))^[n]
      (BalancedInduction.unit (append D Sc cutoff i) M.toFunctor t (M.map b m)) =
    inductionUnitDotSign (k := k) (D.parity i) n •
      BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor t P (M.map b m) at hp
  have hc := LinearMap.congr_fun (moduleUnitColumn_total D Sc cutoff i M t n) (M.map b m)
  change (moduleUnitColumn D Sc cutoff i M n).total t (M.map b m) =
    (inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t) ^ n)
      (((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app M).total t (M.map b m)) at hc
  have hu := adjunctionUnit_total_apply D Sc cutoff i M t (M.map b m)
  change ((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app M).total t
    (M.map b m) = BalancedInduction.unit (append D Sc cutoff i) M.toFunctor t (M.map b m) at hu
  have hc' := hc.trans (congrArg
    (inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t) ^ n) hu)
  simp only [Module.End.pow_apply] at hc'
  refine (show _ = inductionUnitDotSign (k := k) (D.parity i) n •
      BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor t P (M.map b m) from ?_).trans
    (hc'.trans hp).symm
  change BalancedInduction.coefficientEvaluation (append D Sc cutoff i) M.toFunctor
    v ((append D Sc cutoff i).obj t) m
      (inductionUnitDotColumn D Sc cutoff i v.word t.word n b) = _
  rw [inductionUnitDotColumn_comp, map_smul, BalancedInduction.coefficientEvaluation_apply]
  exact congrArg (fun x => inductionUnitDotSign (k := k) (D.parity i) n • x)
    (BalancedInduction.balance (append D Sc cutoff i) M.toFunctor b P m)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Fixed module endpoints for mate-kernel evaluation

The mate comparison needed by DeformedMatrixComparison, section 4, with both
linear maps valued in the literal restriction-induction module. The existing
coefficient comparison is retained unchanged; its pointwise equality is used
to attach the common target module before applying the maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (i : I) (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

abbrev mateSourceSpace (t : OldCategory D Sc cutoff) : SVec k :=
  ((BalancedInduction.induction (append D Sc cutoff i)).obj
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t

abbrev mateTargetSpace (t : OldCategory D Sc cutoff) : SVec k :=
  ((BalancedInduction.restriction (append D Sc cutoff i)).obj
    ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).obj t

/-- The prescribed mate as a linear map with its two literal module endpoints. -/
def moduleMateLinear (t : OldCategory D Sc cutoff) :
    mateSourceSpace D Sc cutoff i M t →ₗ[k] mateTargetSpace D Sc cutoff i M t :=
  SVec.toLinearMap ((matrixMateComponent D Sc cutoff i M).total t)

/-- Coefficient evaluation with the same literal restriction-induction target. -/
def mateCoefficientEvaluation (v t : OldCategory D Sc cutoff) (m : M.obj v) :
    ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) →ₗ[k]
      mateTargetSpace D Sc cutoff i M t :=
  BalancedInduction.coefficientEvaluation (append D Sc cutoff i) M.toFunctor
    v ((append D Sc cutoff i).obj t) m

/-- Source coefficient evaluation with the literal mate-source dictionary. -/
def mateSourceEvaluation (v t : OldCategory D Sc cutoff) (m : M.obj v) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      mateSourceSpace D Sc cutoff i M t :=
  moduleSourceEvaluation D Sc cutoff i M v t m

def kernelMateEvaluationEndpoint (v t : OldCategory D Sc cutoff) (m : M.obj v) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      mateTargetSpace D Sc cutoff i M t :=
  (mateCoefficientEvaluation D Sc cutoff i M v t m).comp
    (mateKernelComponent D Sc cutoff i v t)

def moduleMateEvaluationEndpoint (v t : OldCategory D Sc cutoff) (m : M.obj v) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      mateTargetSpace D Sc cutoff i M t :=
  (moduleMateLinear D Sc cutoff i M t).comp
    (mateSourceEvaluation D Sc cutoff i M v t m)

@[simp] theorem kernelMateEvaluationEndpoint_apply (v t : OldCategory D Sc cutoff)
    (m : M.obj v) (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    kernelMateEvaluationEndpoint D Sc cutoff i M v t m z =
      mateCoefficientEvaluation D Sc cutoff i M v t m
        (mateKernelComponent D Sc cutoff i v t z) := rfl

@[simp] theorem moduleMateEvaluationEndpoint_apply (v t : OldCategory D Sc cutoff)
    (m : M.obj v) (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    moduleMateEvaluationEndpoint D Sc cutoff i M v t m z =
      moduleMateLinear D Sc cutoff i M t
        (mateSourceEvaluation D Sc cutoff i M v t m z) := rfl

@[simp] theorem mateCoefficientEvaluation_apply (v t : OldCategory D Sc cutoff)
    (m : M.obj v)
    (f : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) :
    mateCoefficientEvaluation D Sc cutoff i M v t m f =
      BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v f m := rfl

/-- Total evaluation is exposed only after both literal endpoints have been fixed. -/
theorem moduleMateLinear_apply (t : OldCategory D Sc cutoff)
    (z : mateSourceSpace D Sc cutoff i M t) :
    moduleMateLinear D Sc cutoff i M t z =
      (matrixMateComponent D Sc cutoff i M).total t z := rfl

@[simp] theorem mateSourceEvaluation_apply (v t : OldCategory D Sc cutoff)
    (m : M.obj v) (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    mateSourceEvaluation D Sc cutoff i M v t m z =
      moduleSourceEvaluation D Sc cutoff i M v t m z := rfl

theorem mateSourceEvaluation_tensor (v s t : OldCategory D Sc cutoff) (m : M.obj v)
    (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : v ⟶ (append D Sc cutoff i).obj s) :
    mateSourceEvaluation D Sc cutoff i M v t m
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
      BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M).toFunctor
          s g (M.map b m) :=
  IndResKernel.evaluate_tensor (append D Sc cutoff i) M.toFunctor v t m s g b

/-- The established mate coefficient equality, now between the matching module endpoints. -/
theorem mateEvaluationEndpoints_eq (v t : OldCategory D Sc cutoff) (m : M.obj v) :
    kernelMateEvaluationEndpoint D Sc cutoff i M v t m =
      moduleMateEvaluationEndpoint D Sc cutoff i M v t m := by
  apply BalancedInduction.hom_ext
  intro s g b
  rw [kernelMateEvaluationEndpoint_apply, moduleMateEvaluationEndpoint_apply,
    mateCoefficientEvaluation_apply, mateSourceEvaluation_tensor, moduleMateLinear_apply]
  exact mateKernel_evaluate_tensor D Sc cutoff i M v t m s g b

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Kernel realization of the whole categorical matrices

The arbitrary-module transfer in DeformedMatrixComparison §4 must identify
the entire forward map with the prescribed mate/unit/cap matrix.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
  (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)

local instance matrixEvaluationPi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- The finite kernel map transported into the literal cap target family. -/
def capKernelForward :
    BalancedKernelTensor.Obj (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor →ₗ[k] capMatrixTargetSpace D Sc cutoff i M m t :=
  (negativeKernelCoordinates D Sc cutoff M i m t).toLinearMap.comp
    (BalancedKernelTensor.map M.toFunctor (negativeKernelMap D Sc cutoff i m t))

/-- The prescribed categorical cap matrix on the same kernel quotient source. -/
def capModuleForward :
    BalancedKernelTensor.Obj (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor →ₗ[k] capMatrixTargetSpace D Sc cutoff i M m t :=
  (SVec.toLinearMap (capMatrixComponent D Sc cutoff i M m t)).comp
    (indResKernelCoordinates D Sc cutoff M i t).toLinearMap

theorem indResKernelCoordinates_tensor_moduleSource (v : OldCategory D Sc cutoff)
    (x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) (b : M.obj v) :
    indResKernelCoordinates D Sc cutoff M i t
      (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
        M.toFunctor v x b) = mateSourceEvaluation D Sc cutoff i M v t b x :=
  indResKernelCoordinates_tensor D Sc cutoff M i v t x b

theorem capModuleForward_apply
    (z : BalancedKernelTensor.Obj (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor) (a : Option (Fin m)) :
    capModuleForward D Sc cutoff M i m t z a =
      capMatrixComponent D Sc cutoff i M m t
        (indResKernelCoordinates D Sc cutoff M i t z) a := rfl

theorem capMatrixComponent_apply
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t)
    (a : Option (Fin m)) :
    capMatrixComponent D Sc cutoff i M m t z a =
      (capMatrixEntry D Sc cutoff i M m a).total t z := rfl

theorem capKernelForward_none_tensor (v : OldCategory D Sc cutoff)
    (x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) (b : M.obj v) :
    moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t
      (capKernelForward D Sc cutoff M i m t
        (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
          M.toFunctor v x b) none) =
      mateCoefficientEvaluation D Sc cutoff i M v t b
        (mateKernelComponent D Sc cutoff i v t x) := by
  change moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t
    (negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.map M.toFunctor (negativeKernelMap D Sc cutoff i m t)
        (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
          M.toFunctor v x b)) none) = _
  rw [BalancedKernelTensor.map_tensor, negativeKernelCoordinates_apply,
    BalancedKernelTensor.map_tensor, negativeSlotCoordinates_none]
  change resIndKernelCoordinates D Sc cutoff M i t
    (BalancedKernelTensor.tensor (BalancedKernelTensor.inductionKernel (k := k)
      (append D Sc cutoff i) ((append D Sc cutoff i).obj t)) M.toFunctor v
      ((negativeKernelMap D Sc cutoff i m t).app (op v) x none) b) = _
  have hc := negativeKernelMap_none D Sc cutoff i m v t x
  exact (congrArg (fun g => resIndKernelCoordinates D Sc cutoff M i t
    (BalancedKernelTensor.tensor (BalancedKernelTensor.inductionKernel (k := k)
      (append D Sc cutoff i) ((append D Sc cutoff i).obj t)) M.toFunctor v g b)) hc).trans
    ((resIndKernelCoordinates_tensor D Sc cutoff M i v t _ b).trans
      (mateCoefficientEvaluation_apply D Sc cutoff i M v t b _).symm)

theorem capModuleForward_none
    (z : BalancedKernelTensor.Obj (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor) :
    moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t
      (capModuleForward D Sc cutoff M i m t z none) =
      moduleMateLinear D Sc cutoff i M t
        (indResKernelCoordinates D Sc cutoff M i t z) := by
  exact (congrArg (moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t)
    (capModuleForward_apply D Sc cutoff M i m t z none)).trans
    ((congrArg (moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t)
      (capMatrixComponent_apply D Sc cutoff M i m t _ none)).trans
        ((capMatrixEntry_none_apply D Sc cutoff i M m t _).trans
          (moduleMateLinear_apply D Sc cutoff i M t _).symm))

theorem capKernelForward_some_tensor (v : OldCategory D Sc cutoff)
    (x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) (b : M.obj v)
    (r : Fin m) :
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t
      (capKernelForward D Sc cutoff M i m t
        (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
          M.toFunctor v x b) (some r)) =
      M.map (capKernelComponent D Sc cutoff i r.val v t x) b := by
  change moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t
    (negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.map M.toFunctor (negativeKernelMap D Sc cutoff i m t)
        (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
          M.toFunctor v x b)) (some r)) = _
  rw [BalancedKernelTensor.map_tensor, negativeKernelCoordinates_apply,
    BalancedKernelTensor.map_tensor, negativeSlotCoordinates_some]
  change identityKernelCoordinates D Sc cutoff M t
    (BalancedKernelTensor.tensor (BalancedKernelTensor.inductionKernel (k := k)
      (𝟭 (OldCategory D Sc cutoff)) t) M.toFunctor v
      ((negativeKernelMap D Sc cutoff i m t).app (op v) x (some r)) b) = _
  have hc := negativeKernelMap_some D Sc cutoff i m v t r x
  exact (congrArg (fun g => identityKernelCoordinates D Sc cutoff M t
    (BalancedKernelTensor.tensor (BalancedKernelTensor.inductionKernel (k := k)
      (𝟭 (OldCategory D Sc cutoff)) t) M.toFunctor v g b)) hc).trans
    (identityKernelCoordinates_tensor D Sc cutoff M v t _ b)

theorem capModuleForward_some
    (z : BalancedKernelTensor.Obj (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor) (r : Fin m) :
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t
      (capModuleForward D Sc cutoff M i m t z (some r)) =
      (moduleCapRow D Sc cutoff i M r.val).total t
        (indResKernelCoordinates D Sc cutoff M i t z) := by
  change moduleIsoLinearEquiv
    ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t
    ((capMatrixEntry D Sc cutoff i M m (some r)).total t
      (indResKernelCoordinates D Sc cutoff M i t z)) = _
  exact capMatrixEntry_some_total D Sc cutoff i M t m r _

/-- The whole transported cap matrix is the actual categorical cap matrix. -/
theorem capKernelForward_eq_moduleForward :
    capKernelForward D Sc cutoff M i m t = capModuleForward D Sc cutoff M i m t := by
  apply BalancedKernelTensor.hom_ext
  intro v x b
  change IndResKernel.Component (k := k) (append D Sc cutoff i) v t at x
  funext a
  cases a with
  | none =>
    apply (moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t).injective
    rw [capKernelForward_none_tensor, capModuleForward_none,
      indResKernelCoordinates_tensor_moduleSource]
    exact (kernelMateEvaluationEndpoint_apply D Sc cutoff i M v t b x).symm.trans
      ((LinearMap.congr_fun (mateEvaluationEndpoints_eq D Sc cutoff i M v t b) x).trans
        (moduleMateEvaluationEndpoint_apply D Sc cutoff i M v t b x))
  | some r =>
    apply (moduleIsoLinearEquiv
      ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t).injective
    rw [capKernelForward_some_tensor, capModuleForward_some, indResKernelCoordinates_tensor]
    exact capKernel_evaluate_moduleCapRow D Sc cutoff i M v t b r.val x

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
end

end

section

/-! # Kernel realization of the whole unit-column matrix

The positive-profile arbitrary-module transfer in DeformedMatrixComparison §4,
with the prescribed unscaled unit columns and canonical source parity coordinates.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
  (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)

local instance unitMatrixEvaluationPi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- The coefficient-kernel map with its literal module target. -/
def unitKernelForward :
    BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t))
        M.toFunctor →ₗ[k] mateTargetSpace D Sc cutoff i M t :=
  (resIndKernelCoordinates D Sc cutoff M i t).toLinearMap.comp
    (BalancedKernelTensor.map M.toFunctor (positiveKernelMap D Sc cutoff i m t))

/-- The actual unit matrix with its named source and target superspaces. -/
def unitMatrixLinear : unitMatrixSourceSpace D Sc cutoff i M m t →ₗ[k]
    mateTargetSpace D Sc cutoff i M t :=
  SVec.toLinearMap (unitMatrixComponent D Sc cutoff i M m t)

/-- Source coordinates with the same literal finite superspace dictionary. -/
def unitSourceCoordinatesLinear :
    BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor →ₗ[k]
      unitMatrixSourceSpace D Sc cutoff i M m t :=
  (positiveKernelCoordinates D Sc cutoff M i m t).toLinearMap

/-- The prescribed categorical unit matrix on the same finite kernel source. -/
def unitModuleForward :
    BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t))
        M.toFunctor →ₗ[k] mateTargetSpace D Sc cutoff i M t :=
  (unitMatrixLinear D Sc cutoff M i m t).comp
    (unitSourceCoordinatesLinear D Sc cutoff M i m t)

def unitColumnLinear (n : ℕ) : M.obj t →ₗ[k] mateTargetSpace D Sc cutoff i M t :=
  SVec.toLinearMap ((moduleUnitColumn D Sc cutoff i M n).total t)

theorem unitColumnLinear_apply (n : ℕ) (b : M.obj t) :
    unitColumnLinear D Sc cutoff M i t n b =
      (moduleUnitColumn D Sc cutoff i M n).total t b := rfl

theorem unitModuleForward_apply
    (z : BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor) :
    unitModuleForward D Sc cutoff M i m t z =
      unitMatrixLinear D Sc cutoff M i m t
        (unitSourceCoordinatesLinear D Sc cutoff M i m t z) := rfl

theorem unitMatrixLinear_apply (z : unitMatrixSourceSpace D Sc cutoff i M m t) :
    unitMatrixLinear D Sc cutoff M i m t z =
      unitMatrixComponent D Sc cutoff i M m t z := rfl

theorem positiveKernelCoordinates_linear_apply
    (z : BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor)
    (a : Option (Fin m)) :
    (positiveKernelCoordinates D Sc cutoff M i m t).toLinearMap z a =
      positiveSlotCoordinates D Sc cutoff M i m t a
        (BalancedKernelTensor.map M.toFunctor
          (BalancedKernelTensor.piProjection (positiveKernelFamily D Sc cutoff i m t) a) z) := by
  have h := congrFun (LinearEquiv.coe_toLinearMap
    (positiveKernelCoordinates D Sc cutoff M i m t)) z
  exact (congrArg (fun x : unitMatrixSourceSpace D Sc cutoff i M m t => x a) h).trans
    (positiveKernelCoordinates_apply D Sc cutoff M i m t z a)

theorem unitSourceCoordinatesLinear_slot
    (z : BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor)
    (a : Option (Fin m)) :
    unitSourceCoordinatesLinear D Sc cutoff M i m t z a =
      positiveSlotCoordinates D Sc cutoff M i m t a
        (BalancedKernelTensor.map M.toFunctor
          (BalancedKernelTensor.piProjection (positiveKernelFamily D Sc cutoff i m t) a) z) :=
  positiveKernelCoordinates_linear_apply D Sc cutoff M i m t z a

theorem unitMatrixComponent_apply (z : unitMatrixSourceSpace D Sc cutoff i M m t) :
    unitMatrixComponent D Sc cutoff i M m t z =
      (unitMatrixEntry D Sc cutoff i M m none).total t (z none) +
        ∑ r : Fin m, (unitMatrixEntry D Sc cutoff i M m (some r)).total t (z (some r)) := by
  have h := OddMath.FiniteSuperspace.assembleColumns_apply
    (fun a => (unitMatrixFamily D Sc cutoff i M m a).obj t)
    (mateTargetSpace D Sc cutoff i M t)
    (fun a => (unitMatrixEntry D Sc cutoff i M m a).total t) z
  exact h.trans (Fintype.sum_option _)

theorem unitSlotCoordinates_none
    (z : BalancedKernelTensor.Obj (positiveKernelFamily D Sc cutoff i m t none) M.toFunctor) :
    (unitMatrixEntry D Sc cutoff i M m none).total t
      (positiveSlotCoordinates D Sc cutoff M i m t none z) =
      moduleMateLinear D Sc cutoff i M t (indResKernelCoordinates D Sc cutoff M i t z) := by
  have h := unitMatrixEntry_none_apply D Sc cutoff i M m t
    (positiveSlotCoordinates D Sc cutoff M i m t none z)
  exact h.trans ((moduleMateLinear_apply D Sc cutoff i M t _).symm.trans
    (congrArg (moduleMateLinear D Sc cutoff i M t)
      (positiveSlotCoordinates_none D Sc cutoff M i m t z)))

theorem unitSlotCoordinates_some (r : Fin m)
    (z : BalancedKernelTensor.Obj (positiveKernelFamily D Sc cutoff i m t (some r)) M.toFunctor) :
    (unitMatrixEntry D Sc cutoff i M m (some r)).total t
      (positiveSlotCoordinates D Sc cutoff M i m t (some r) z) =
      unitColumnLinear D Sc cutoff M i t r.val (identityKernelCoordinates D Sc cutoff M t z) := by
  have h := unitMatrixEntry_some_total D Sc cutoff i M t m r
    (positiveSlotCoordinates D Sc cutoff M i m t (some r) z)
  exact h.trans ((unitColumnLinear_apply D Sc cutoff M i t r.val _).symm.trans
    (congrArg (unitColumnLinear D Sc cutoff M i t r.val)
      (positiveSlotCoordinates_some D Sc cutoff M i m t r z)))

theorem unitSourceCoordinatesLinear_tensor (v : OldCategory D Sc cutoff)
    (x : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj (op v))
    (b : M.obj v) (a : Option (Fin m)) :
    unitSourceCoordinatesLinear D Sc cutoff M i m t
      (BalancedKernelTensor.tensor (BalancedKernelTensor.piKernel
        (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor v x b) a =
      positiveSlotCoordinates D Sc cutoff M i m t a
        (BalancedKernelTensor.tensor (positiveKernelFamily D Sc cutoff i m t a)
          M.toFunctor v (x a) b) := by
  rw [unitSourceCoordinatesLinear_slot, BalancedKernelTensor.map_tensor]
  rfl

theorem unitSlotCoordinates_none_tensor (v : OldCategory D Sc cutoff)
    (x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) (b : M.obj v) :
    (unitMatrixEntry D Sc cutoff i M m none).total t
      (positiveSlotCoordinates D Sc cutoff M i m t none
        (BalancedKernelTensor.tensor (positiveKernelFamily D Sc cutoff i m t none)
          M.toFunctor v x b)) =
      moduleMateLinear D Sc cutoff i M t (mateSourceEvaluation D Sc cutoff i M v t b x) := by
  rw [unitSlotCoordinates_none]
  exact congrArg (moduleMateLinear D Sc cutoff i M t)
    (indResKernelCoordinates_tensor_moduleSource D Sc cutoff M i t v x b)

theorem unitSlotCoordinates_some_tensor (v : OldCategory D Sc cutoff) (r : Fin m)
    (h : v ⟶ t) (b : M.obj v) :
    (unitMatrixEntry D Sc cutoff i M m (some r)).total t
      (positiveSlotCoordinates D Sc cutoff M i m t (some r)
        (BalancedKernelTensor.tensor (positiveKernelFamily D Sc cutoff i m t (some r))
          M.toFunctor v h b)) =
      unitColumnLinear D Sc cutoff M i t r.val (M.map h b) := by
  rw [unitSlotCoordinates_some]
  exact congrArg (unitColumnLinear D Sc cutoff M i t r.val)
    (identityKernelCoordinates_tensor D Sc cutoff M v t h b)

theorem unitModuleForward_tensor (v : OldCategory D Sc cutoff)
    (x : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj (op v))
    (b : M.obj v) :
    unitModuleForward D Sc cutoff M i m t
      (BalancedKernelTensor.tensor (BalancedKernelTensor.piKernel
        (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor v x b) =
      moduleMateLinear D Sc cutoff i M t (mateSourceEvaluation D Sc cutoff i M v t b (x none)) +
        ∑ r : Fin m, unitColumnLinear D Sc cutoff M i t r.val (M.map (x (some r)) b) := by
  rw [unitModuleForward_apply, unitMatrixLinear_apply, unitMatrixComponent_apply]
  simp_rw [unitSourceCoordinatesLinear_tensor]
  rw [unitSlotCoordinates_none_tensor]
  exact congrArg (fun y => moduleMateLinear D Sc cutoff i M t
      (mateSourceEvaluation D Sc cutoff i M v t b (x none)) + y)
    (Finset.sum_congr rfl (fun r _ =>
      unitSlotCoordinates_some_tensor D Sc cutoff M i m t v r (x (some r)) b))

theorem unitKernelForward_tensor (v : OldCategory D Sc cutoff)
    (x : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj (op v))
    (b : M.obj v) :
    unitKernelForward D Sc cutoff M i m t
      (BalancedKernelTensor.tensor (BalancedKernelTensor.piKernel
        (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor v x b) =
      mateCoefficientEvaluation D Sc cutoff i M v t b
        (mateKernelComponent D Sc cutoff i v t (x none)) +
        ∑ r : Fin m, mateCoefficientEvaluation D Sc cutoff i M v t b
          (unitKernelComponent D Sc cutoff i r.val v t (x (some r))) := by
  change resIndKernelCoordinates D Sc cutoff M i t
    (BalancedKernelTensor.map M.toFunctor (positiveKernelMap D Sc cutoff i m t)
      (BalancedKernelTensor.tensor (BalancedKernelTensor.piKernel
        (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor v x b)) = _
  rw [BalancedKernelTensor.map_tensor]
  have h := (resIndKernelCoordinates_tensor D Sc cutoff M i v t
    ((positiveKernelMap D Sc cutoff i m t).app (op v) x) b).trans
      (mateCoefficientEvaluation_apply D Sc cutoff i M v t b _).symm
  refine h.trans ?_
  have hc := congrArg (mateCoefficientEvaluation D Sc cutoff i M v t b)
    (positiveKernelMap_apply D Sc cutoff i m v t x)
  refine hc.trans ?_
  rw [map_add, map_sum]

/-- The whole transported unit-column map is the actual categorical unit matrix. -/
theorem unitKernelForward_eq_moduleForward :
    unitKernelForward D Sc cutoff M i m t = unitModuleForward D Sc cutoff M i m t := by
  apply BalancedKernelTensor.hom_ext
  intro v x b
  rw [unitKernelForward_tensor, unitModuleForward_tensor]
  apply congrArg₂ (fun x y => x + y)
  · exact (kernelMateEvaluationEndpoint_apply D Sc cutoff i M v t b (x none)).symm.trans
      ((LinearMap.congr_fun (mateEvaluationEndpoints_eq D Sc cutoff i M v t b) (x none)).trans
        (moduleMateEvaluationEndpoint_apply D Sc cutoff i M v t b (x none)))
  · apply Finset.sum_congr rfl
    intro r _
    exact (mateCoefficientEvaluation_apply D Sc cutoff i M v t b _).trans
      ((unitKernel_evaluate D Sc cutoff i M v t b r.val (x (some r))).trans
        (unitColumnLinear_apply D Sc cutoff M i t r.val _).symm)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
end

end

section

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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Actual finite kernel matrices off their target content -/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem bijective_of_subsingleton {V W : Type u}
    [Subsingleton V] [Subsingleton W] [Nonempty V] (f : V → W) : Function.Bijective f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨Classical.choice inferInstance, Subsingleton.elim _ _⟩⟩

/-- With different contents every finite positive coefficient space vanishes. -/
theorem positiveKernelMap_bijective_of_content_ne (i : I) (m : ℕ)
    (v t : OldCategory D Sc cutoff)
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) :
    Function.Bijective ((positiveKernelMap D Sc cutoff i m t).app (op v)) := by
  have hnone : Subsingleton ((positiveKernelFamily D Sc cutoff i m t none).obj (op v)) := by
    change Subsingleton (IndResKernel.Component (k := k) (append D Sc cutoff i) v t)
    exact indResKernel_subsingleton_of_content_ne D Sc cutoff (append D Sc cutoff i) h
  have hsome (r : Fin m) : Subsingleton ((positiveKernelFamily D Sc cutoff i m t (some r)).obj (op v)) := by
    change Subsingleton (v ⟶ t)
    exact oldCategory_hom_subsingleton_of_content_ne D Sc cutoff h
  have ht : Subsingleton ((BalancedKernelTensor.inductionKernel (k := k)
      (append D Sc cutoff i) ((append D Sc cutoff i).obj t)).obj (op v)) := by
    change Subsingleton ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t)
    exact append_hom_subsingleton_of_content_ne D Sc cutoff i h
  have hs : Subsingleton ((BalancedKernelTensor.piKernel
      (positiveKernelFamily D Sc cutoff i m t)).obj (op v)) := by
    refine ⟨fun x y => ?_⟩
    funext a
    cases a with
    | none => exact hnone.elim _ _
    | some r => exact (hsome r).elim _ _
  exact @bijective_of_subsingleton _ _ hs ht ⟨0⟩ _

/-- With different contents every finite negative coefficient space vanishes. -/
theorem negativeKernelMap_bijective_of_content_ne (i : I) (m : ℕ)
    (v t : OldCategory D Sc cutoff)
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) :
    Function.Bijective ((negativeKernelMap D Sc cutoff i m t).app (op v)) := by
  have hnone : Subsingleton ((negativeKernelFamily D Sc cutoff i m t none).obj (op v)) := by
    change Subsingleton ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t)
    exact append_hom_subsingleton_of_content_ne D Sc cutoff i h
  have hsome (r : Fin m) : Subsingleton ((negativeKernelFamily D Sc cutoff i m t (some r)).obj (op v)) := by
    change Subsingleton (v ⟶ t)
    exact oldCategory_hom_subsingleton_of_content_ne D Sc cutoff h
  have hs : Subsingleton ((IndResKernel.kernel (k := k) (append D Sc cutoff i) t).obj (op v)) := by
    change Subsingleton (IndResKernel.Component (k := k) (append D Sc cutoff i) v t)
    exact indResKernel_subsingleton_of_content_ne D Sc cutoff (append D Sc cutoff i) h
  have ht : Subsingleton ((BalancedKernelTensor.piKernel
      (negativeKernelFamily D Sc cutoff i m t)).obj (op v)) := by
    refine ⟨fun x y => ?_⟩
    funext a
    cases a with
    | none => exact hnone.elim _ _
    | some r => exact (hsome r).elim _ _
  exact @bijective_of_subsingleton _ _ hs ht ⟨0⟩ _

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Coefficient-kernel matrix bijectivity
The target-fixed coefficient-kernel transfer of DeformedMatrixComparison section 4.
Comparisons use literal list endpoints before passing to boxed old objects.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def oddPositiveCoordinates (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff j.1 m ⟨t⟩)).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
        Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  (positiveKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩).trans
    ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m).symm.trans
      (unitFamilyComponentEquiv D Sc cutoff 0 j v t m hm))

private theorem oddPositiveCoordinates_apply (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m)
    (z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff j.1 m ⟨t⟩)).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff))) :
    (oddPositiveCoordinates D Sc cutoff j v t m hm).toFun z =
      (positiveKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) z := by
  classical
  rw [positiveKernelMap_apply]
  change unitFamilyComponentEquiv D Sc cutoff 0 j v t m hm
    ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m).symm
      (positiveKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩ z)) = _
  rw [unitFamilyComponentEquiv_eq]
  simp only [LinearEquiv.apply_symm_apply]
  rw [mateKernelComponent_row]
  apply congrArg₂ (fun x y => x + y)
  · apply congrArg (matrixMateRow D Sc cutoff j.1 v t)
    rfl
  · apply Finset.sum_congr rfl
    intro r _
    rfl

private def oddNegativeCoordinates (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (IndResKernel.kernel (k := k) (append D Sc cutoff j.1) ⟨t⟩).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff j.1 m ⟨t⟩)).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff)) :=
  (kernelSourceCoordinates D Sc cutoff j.1 (op ⟨v⟩) ⟨t⟩).trans
    ((capFamilyComponentEquiv D Sc cutoff 0 j v t m hm).trans
      ((capFamilyComponentCoordinates D Sc cutoff j.1 v t m).trans
        (negativeKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩).symm))

private theorem oddNegativeCoordinates_apply (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (IndResKernel.kernel (k := k) (append D Sc cutoff j.1) ⟨t⟩).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff))) :
    (oddNegativeCoordinates D Sc cutoff j v t m hm).toFun z =
      (negativeKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) z := by
  apply (negativeKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩).injective
  change capFamilyComponentCoordinates D Sc cutoff j.1 v t m
      (capFamilyComponentEquiv D Sc cutoff 0 j v t m hm
        (kernelSourceCoordinates D Sc cutoff j.1 (op ⟨v⟩) ⟨t⟩ z)) = _
  rw [capFamilyComponentEquiv_eq]
  apply Prod.ext
  · rw [negativeKernelCoordinates_fst, negativeKernelMap_none,
      mateKernelComponent_row]
    apply congrArg (matrixMateRow D Sc cutoff j.1 v t)
    rfl
  · funext r
    rw [negativeKernelCoordinates_snd, negativeKernelMap_some,
      capKernelComponent_moduleCapRow]
    apply congrArg ((moduleCapRow D Sc cutoff j.1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total
        (⟨t⟩ : OldCategory D Sc cutoff))
    rfl

private def evenPositiveCoordinates (j : {j : I // D.parity j = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff j.1 m ⟨t⟩)).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
        Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  (positiveKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩).trans
    ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m).symm.trans
      (evenUnitFamilyComponentEquiv D Sc cutoff 0 j v t m hm))

private theorem evenPositiveCoordinates_apply (j : {j : I // D.parity j = 0})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m)
    (z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff j.1 m ⟨t⟩)).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff))) :
    (evenPositiveCoordinates D Sc cutoff j v t m hm).toFun z =
      (positiveKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) z := by
  classical
  rw [positiveKernelMap_apply]
  change evenUnitFamilyComponentEquiv D Sc cutoff 0 j v t m hm
    ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m).symm
      (positiveKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩ z)) = _
  rw [evenUnitFamilyComponentEquiv_eq]
  simp only [LinearEquiv.apply_symm_apply]
  rw [mateKernelComponent_row]
  apply congrArg₂ (fun x y => x + y)
  · apply congrArg (matrixMateRow D Sc cutoff j.1 v t)
    rfl
  · apply Finset.sum_congr rfl
    intro r _
    rfl

private def evenNegativeCoordinates (j : {j : I // D.parity j = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    (IndResKernel.kernel (k := k) (append D Sc cutoff j.1) ⟨t⟩).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff j.1 m ⟨t⟩)).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff)) :=
  (kernelSourceCoordinates D Sc cutoff j.1 (op ⟨v⟩) ⟨t⟩).trans
    ((evenCapFamilyComponentEquiv D Sc cutoff 0 j v t m hm).trans
      ((capFamilyComponentCoordinates D Sc cutoff j.1 v t m).trans
        (negativeKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩).symm))

private theorem evenNegativeCoordinates_apply (j : {j : I // D.parity j = 0})
    (v t : List I) (m : ℕ)
    (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m)
    (z : (IndResKernel.kernel (k := k) (append D Sc cutoff j.1) ⟨t⟩).obj
      (op (⟨v⟩ : OldCategory D Sc cutoff))) :
    (evenNegativeCoordinates D Sc cutoff j v t m hm).toFun z =
      (negativeKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) z := by
  apply (negativeKernelCoordinates D Sc cutoff j.1 m (op ⟨v⟩) ⟨t⟩).injective
  change capFamilyComponentCoordinates D Sc cutoff j.1 v t m
      (evenCapFamilyComponentEquiv D Sc cutoff 0 j v t m hm
        (kernelSourceCoordinates D Sc cutoff j.1 (op ⟨v⟩) ⟨t⟩ z)) = _
  rw [evenCapFamilyComponentEquiv_eq]
  apply Prod.ext
  · rw [negativeKernelCoordinates_fst, negativeKernelMap_none,
      mateKernelComponent_row]
    apply congrArg (matrixMateRow D Sc cutoff j.1 v t)
    rfl
  · funext r
    rw [negativeKernelCoordinates_snd, negativeKernelMap_some,
      capKernelComponent_moduleCapRow]
    apply congrArg ((moduleCapRow D Sc cutoff j.1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) r.val).total
        (⟨t⟩ : OldCategory D Sc cutoff))
    rfl

theorem PositiveKernelMap_bijective_of_height
    (j : {j : I // D.parity j = 1}) (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v.word = outputSDegree D j.1 v.word + m) :
    Function.Bijective ((positiveKernelMap D Sc cutoff j.1 m t).app (op v)) := by
  rcases v with ⟨v⟩
  rcases t with ⟨t⟩
  have heq : (oddPositiveCoordinates D Sc cutoff j v t m hm).toFun =
      (positiveKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) :=
    funext (oddPositiveCoordinates_apply D Sc cutoff j v t m hm)
  rw [← heq]
  exact (oddPositiveCoordinates D Sc cutoff j v t m hm).bijective

theorem NegativeKernelMap_bijective_of_height
    (j : {j : I // D.parity j = 1}) (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : outputSDegree D j.1 v.word = endpointQPDegree D cutoff j.1 v.word + m) :
    Function.Bijective ((negativeKernelMap D Sc cutoff j.1 m t).app (op v)) := by
  rcases v with ⟨v⟩
  rcases t with ⟨t⟩
  have heq : (oddNegativeCoordinates D Sc cutoff j v t m hm).toFun =
      (negativeKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) :=
    funext (oddNegativeCoordinates_apply D Sc cutoff j v t m hm)
  rw [← heq]
  exact (oddNegativeCoordinates D Sc cutoff j v t m hm).bijective

theorem evenPositiveKernelMap_bijective_of_height
    (j : {j : I // D.parity j = 0}) (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v.word = outputSDegree D j.1 v.word + m) :
    Function.Bijective ((positiveKernelMap D Sc cutoff j.1 m t).app (op v)) := by
  rcases v with ⟨v⟩
  rcases t with ⟨t⟩
  have heq : (evenPositiveCoordinates D Sc cutoff j v t m hm).toFun =
      (positiveKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) :=
    funext (evenPositiveCoordinates_apply D Sc cutoff j v t m hm)
  rw [← heq]
  exact (evenPositiveCoordinates D Sc cutoff j v t m hm).bijective

theorem evenNegativeKernelMap_bijective_of_height
    (j : {j : I // D.parity j = 0}) (v t : OldCategory D Sc cutoff) (m : ℕ)
    (hm : outputSDegree D j.1 v.word = endpointQPDegree D cutoff j.1 v.word + m) :
    Function.Bijective ((negativeKernelMap D Sc cutoff j.1 m t).app (op v)) := by
  rcases v with ⟨v⟩
  rcases t with ⟨t⟩
  have heq : (evenNegativeCoordinates D Sc cutoff j v t m hm).toFun =
      (negativeKernelMap D Sc cutoff j.1 m ⟨t⟩).app (op ⟨v⟩) :=
    funext (evenNegativeCoordinates_apply D Sc cutoff j v t m hm)
  rw [← heq]
  exact (evenNegativeCoordinates D Sc cutoff j v t m hm).bijective

private theorem colourParityCases (P : I → Prop)
    (he : ∀ j : {j : I // D.parity j = 0}, P j.1)
    (ho : ∀ j : {j : I // D.parity j = 1}, P j.1) (i : I) : P i := by
  rcases parity_eq_zero_or_one (D.parity i) with hi | hi
  · exact he ⟨i, hi⟩
  · exact ho ⟨i, hi⟩

private theorem positiveKernelMap_bijective_of_height (i : I)
    (v t : OldCategory D Sc cutoff) (m : ℕ) (hm : endpointQPDegree D cutoff i v.word = outputSDegree D i v.word + m) :
    Function.Bijective ((positiveKernelMap D Sc cutoff i m t).app (op v)) :=
  colourParityCases D (fun i => ∀ (v t : OldCategory D Sc cutoff) (m : ℕ),
    endpointQPDegree D cutoff i v.word = outputSDegree D i v.word + m →
      Function.Bijective ((positiveKernelMap D Sc cutoff i m t).app (op v)))
    (evenPositiveKernelMap_bijective_of_height D Sc cutoff)
    (PositiveKernelMap_bijective_of_height D Sc cutoff) i v t m hm

private theorem negativeKernelMap_bijective_of_height (i : I)
    (v t : OldCategory D Sc cutoff) (m : ℕ) (hm : outputSDegree D i v.word = endpointQPDegree D cutoff i v.word + m) :
    Function.Bijective ((negativeKernelMap D Sc cutoff i m t).app (op v)) :=
  colourParityCases D (fun i => ∀ (v t : OldCategory D Sc cutoff) (m : ℕ),
    outputSDegree D i v.word = endpointQPDegree D cutoff i v.word + m →
      Function.Bijective ((negativeKernelMap D Sc cutoff i m t).app (op v)))
    (evenNegativeKernelMap_bijective_of_height D Sc cutoff)
    (NegativeKernelMap_bijective_of_height D Sc cutoff) i v t m hm

/-- The prescribed coefficient matrix is bijective at every source, with one count fixed by target content. -/
theorem positiveKernelMap_bijective (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) (v : OldCategory D Sc cutoff) :
    Function.Bijective ((positiveKernelMap D Sc cutoff i
      (contentUnitCount D cutoff i (t.word : Multiset I)) t).app (op v)) := by
  by_cases hc : (v.word : Multiset I) = (t.word : Multiset I)
  · let vc : OldContentCategory D Sc cutoff t.word := ⟨v, Multiset.coe_eq_coe.mp hc⟩
    have hm := oldContent_unitCount_height D Sc cutoff i t.word hh vc
    change endpointQPDegree D cutoff i v.word = outputSDegree D i v.word +
      contentUnitCount D cutoff i (t.word : Multiset I) at hm
    exact positiveKernelMap_bijective_of_height D Sc cutoff i v t
      (contentUnitCount D cutoff i (t.word : Multiset I)) hm
  · exact positiveKernelMap_bijective_of_content_ne D Sc cutoff i _ v t hc

/-- The prescribed coefficient matrix is bijective at every source, with one count fixed by target content. -/
theorem negativeKernelMap_bijective (i : I) (t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) (v : OldCategory D Sc cutoff) :
    Function.Bijective ((negativeKernelMap D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t).app (op v)) := by
  by_cases hc : (v.word : Multiset I) = (t.word : Multiset I)
  · let vc : OldContentCategory D Sc cutoff t.word := ⟨v, Multiset.coe_eq_coe.mp hc⟩
    have hm := oldContent_capCount_height D Sc cutoff i t.word hh vc
    exact negativeKernelMap_bijective_of_height D Sc cutoff i v t
      (contentCapCount D cutoff i (t.word : Multiset I)) hm
  · exact negativeKernelMap_bijective_of_content_ne D Sc cutoff i _ v t hc

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Prescribed matrix inverses on arbitrary modules

The arbitrary-module inversion step of DeformedMatrixComparison, section 4.
Coefficient-kernel isomorphisms are tensored using the explicit balanced
quotient and transported through the canonical finite shifted coordinates.
The forward maps are the prescribed module matrices. Their independent
evenness implies inverse evenness. No categorical colimit or flatness
hypothesis is used.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

private theorem opComponents {C : Type u} (P : Cᵒᵖ → Prop)
    (h : ∀ v : C, P (op v)) (v : Cᵒᵖ) : P v := by
  rcases v with ⟨v⟩
  exact h v

private def transportedUnitEquiv (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (hb : ∀ v : OldCategory D Sc cutoff,
      Function.Bijective ((positiveKernelMap D Sc cutoff i m t).app (op v))) :
    unitMatrixSourceSpace D Sc cutoff i M m t ≃ₗ[k] mateTargetSpace D Sc cutoff i M t :=
  (positiveKernelCoordinates D Sc cutoff M i m t).symm.trans
    ((BalancedKernelTensor.equivOfBijective M.toFunctor
      (positiveKernelMap D Sc cutoff i m t)
      (opComponents (fun v => Function.Bijective
        ((positiveKernelMap D Sc cutoff i m t).app v)) hb)).trans
        (resIndKernelCoordinates D Sc cutoff M i t))

private def transportedCapEquiv (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (hb : ∀ v : OldCategory D Sc cutoff,
      Function.Bijective ((negativeKernelMap D Sc cutoff i m t).app (op v))) :
    mateSourceSpace D Sc cutoff i M t ≃ₗ[k] capMatrixTargetSpace D Sc cutoff i M m t :=
  (indResKernelCoordinates D Sc cutoff M i t).symm.trans
    ((BalancedKernelTensor.equivOfBijective M.toFunctor
      (negativeKernelMap D Sc cutoff i m t)
      (opComponents (fun v => Function.Bijective
        ((negativeKernelMap D Sc cutoff i m t).app v)) hb)).trans
        (negativeKernelCoordinates D Sc cutoff M i m t))

private theorem transportedUnitEquiv_apply (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (hb : ∀ v : OldCategory D Sc cutoff,
      Function.Bijective ((positiveKernelMap D Sc cutoff i m t).app (op v)))
    (x : unitMatrixSourceSpace D Sc cutoff i M m t) :
    transportedUnitEquiv D Sc cutoff M i m t hb x = unitMatrixComponent D Sc cutoff i M m t x := by
  change resIndKernelCoordinates D Sc cutoff M i t
      (BalancedKernelTensor.map M.toFunctor (positiveKernelMap D Sc cutoff i m t)
        ((positiveKernelCoordinates D Sc cutoff M i m t).symm x)) = _
  calc
    _ = unitKernelForward D Sc cutoff M i m t
        ((positiveKernelCoordinates D Sc cutoff M i m t).symm x) := rfl
    _ = unitModuleForward D Sc cutoff M i m t
        ((positiveKernelCoordinates D Sc cutoff M i m t).symm x) :=
      LinearMap.congr_fun (unitKernelForward_eq_moduleForward D Sc cutoff M i m t) _
    _ = unitMatrixLinear D Sc cutoff M i m t
        (unitSourceCoordinatesLinear D Sc cutoff M i m t
          ((positiveKernelCoordinates D Sc cutoff M i m t).symm x)) :=
      unitModuleForward_apply D Sc cutoff M i m t _
    _ = unitMatrixComponent D Sc cutoff i M m t x := by
      rw [unitMatrixLinear_apply]
      apply congrArg (unitMatrixComponent D Sc cutoff i M m t)
      exact (positiveKernelCoordinates D Sc cutoff M i m t).apply_symm_apply x

private theorem transportedCapEquiv_apply (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (hb : ∀ v : OldCategory D Sc cutoff,
      Function.Bijective ((negativeKernelMap D Sc cutoff i m t).app (op v)))
    (x : mateSourceSpace D Sc cutoff i M t) :
    transportedCapEquiv D Sc cutoff M i m t hb x = capMatrixComponent D Sc cutoff i M m t x := by
  change negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.map M.toFunctor (negativeKernelMap D Sc cutoff i m t)
        ((indResKernelCoordinates D Sc cutoff M i t).symm x)) = _
  have h := LinearMap.congr_fun (capKernelForward_eq_moduleForward D Sc cutoff M i m t)
    ((indResKernelCoordinates D Sc cutoff M i t).symm x)
  change negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.map M.toFunctor (negativeKernelMap D Sc cutoff i m t)
        ((indResKernelCoordinates D Sc cutoff M i t).symm x)) =
    capMatrixComponent D Sc cutoff i M m t
      (indResKernelCoordinates D Sc cutoff M i t
        ((indResKernelCoordinates D Sc cutoff M i t).symm x)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- The prescribed finite unit matrix is invertible on every old supermodule. -/
def moduleUnitMatrixIso (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :
    unitMatrixSourceSpace D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) t ≅
        mateTargetSpace D Sc cutoff i M t :=
  SVec.isoOfLinearEquiv (transportedUnitEquiv D Sc cutoff M i
    (contentUnitCount D cutoff i (t.word : Multiset I)) t
      (positiveKernelMap_bijective D Sc cutoff i t hh))

theorem moduleUnitMatrixIso_hom (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :
    (moduleUnitMatrixIso D Sc cutoff M i t hh).hom =
      unitMatrixComponent D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) t := by
  apply LinearMap.ext
  intro x
  exact transportedUnitEquiv_apply D Sc cutoff M i
    (contentUnitCount D cutoff i (t.word : Multiset I)) t
      (positiveKernelMap_bijective D Sc cutoff i t hh) x

theorem moduleUnitMatrixIso_hom_even (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :
    (moduleUnitMatrixIso D Sc cutoff M i t hh).hom ∈ parity (R := k)
      (unitMatrixSourceSpace D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) t)
      (mateTargetSpace D Sc cutoff i M t) 0 := by
  rw [moduleUnitMatrixIso_hom]
  exact unitMatrixComponent_even D Sc cutoff i M _ t

theorem moduleUnitMatrixIso_inv_even (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :
    (moduleUnitMatrixIso D Sc cutoff M i t hh).inv ∈ parity (R := k)
      (mateTargetSpace D Sc cutoff i M t)
      (unitMatrixSourceSpace D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) t) 0 :=
  Supercategory.inv_mem (moduleUnitMatrixIso D Sc cutoff M i t hh)
    (moduleUnitMatrixIso_hom_even D Sc cutoff M i t hh)

/-- The prescribed finite cap matrix is invertible on every old supermodule. -/
def moduleCapMatrixIso (i : I) (t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) :
    mateSourceSpace D Sc cutoff i M t ≅
      capMatrixTargetSpace D Sc cutoff i M
        (contentCapCount D cutoff i (t.word : Multiset I)) t :=
  SVec.isoOfLinearEquiv (transportedCapEquiv D Sc cutoff M i
    (contentCapCount D cutoff i (t.word : Multiset I)) t
      (negativeKernelMap_bijective D Sc cutoff i t hh))

theorem moduleCapMatrixIso_hom (i : I) (t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) :
    (moduleCapMatrixIso D Sc cutoff M i t hh).hom =
      capMatrixComponent D Sc cutoff i M
        (contentCapCount D cutoff i (t.word : Multiset I)) t := by
  apply LinearMap.ext
  intro x
  exact transportedCapEquiv_apply D Sc cutoff M i
    (contentCapCount D cutoff i (t.word : Multiset I)) t
      (negativeKernelMap_bijective D Sc cutoff i t hh) x

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
end

end

section

/-! # Braid relations under balanced induction

Brundan–Ellis Definition 1.5: two source transformations of the same
parity induce the braid on every module, retaining the superopposite
composition signs. This is used by both the old append and the changing
content-category induction grids.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
/-- A braid of homogeneous source transformations induces the whole module braid. -/
theorem transformComponent_braid
    {k C A : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (T : C ⥤ A) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    {p : ZMod 2} {α β : ∀ s, T.obj s ⟶ T.obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β)
    (hb : ∀ s, α s ≫ β s ≫ α s = β s ≫ α s ≫ β s)
    (M : Superfunctor k C (SVec k)) :
    transformComponent hα M ≫ transformComponent hβ M ≫ transformComponent hα M =
      transformComponent hβ M ≫ transformComponent hα M ≫ transformComponent hβ M := by
  have he : (fun s => (α s ≫ β s) ≫ α s) =
      (fun s => (β s ≫ α s) ≫ β s) := by
    funext s
    simpa only [Category.assoc] using hb s
  have ht : transformComponent ((hα.comp hβ).comp hα) M =
      transformComponent ((hβ.comp hα).comp hβ) M := by
    congr 1
  rw [transformComponent_comp, transformComponent_comp,
    Linear.comp_smul, Linear.comp_smul,
    transformComponent_comp, transformComponent_comp]
  exact congrArg (fun f => _ • (_ • f)) ht

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Homogeneous slides under balanced induction

Brundan–Ellis (1.8): a source dot/crossing slide induces the corresponding
whole module-map slide, with the two superopposite composition signs
cancelling. This supplies the distinct-colour probe relation on direct
induction before its chosen pair flattenings are applied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C A : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  {F G : C ⥤ A}
  [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  [G.Additive] [G.Linear k] [IsSuperfunctor k G]
  {p q : ZMod 2} {x : ∀ v, F.obj v ⟶ F.obj v}
  {c : ∀ v, F.obj v ⟶ G.obj v} {y : ∀ v, G.obj v ⟶ G.obj v}
  (hx : IsSupernatural k p x) (hc : IsSupernatural k q c)
  (hy : IsSupernatural k p y) (a : k)
  (hs : ∀ v, x v ≫ c v = a • (c v ≫ y v))

include hs in
/-- The original scalar remains after both contravariant composition signs. -/
theorem transformLinear_rectangular_slide (M : Superfunctor k C (SVec k)) (w : A) :
    transformLinear hx M w ∘ₗ transformLinear hc M w =
      a • (transformLinear hc M w ∘ₗ transformLinear hy M w) := by
  rw [transformLinear_comp, transformLinear_comp]
  apply hom_ext
  intro v h m
  simp only [LinearMap.smul_apply, transformLinear_tensor]
  change sign k (p * q) • tensor F M.toFunctor v ((x v ≫ c v) ≫ twist k (p + q) h) m =
    a • (sign k (q * p) • tensor F M.toFunctor v ((c v ≫ y v) ≫ twist k (q + p) h) m)
  rw [hs v, Linear.smul_comp, mul_comm q p, add_comm q p]
  simp only [tensor, ← TensorProduct.smul_tmul', map_smul]
  exact smul_comm _ _ _

include hs in
/-- The homogeneous slide holds on entire induced module maps. -/
theorem transformComponent_rectangular_slide (M : Superfunctor k C (SVec k)) :
    transformComponent hc M ≫ transformComponent hx M =
      a • (transformComponent hy M ≫ transformComponent hc M) := by
  apply Superfunctor.hom_ext
  intro r w
  have he := transformLinear_rectangular_slide hx hc hy a hs M w
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp only [Superfunctor.comp_app, Superfunctor.smul_app, transformComponent_app,
      SVec.zmod2_one_add_one, zero_add, add_zero, ↓reduceIte, one_ne_zero, zero_ne_one,
      CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp, smul_zero,
      zero_add, add_zero] <;> exact he

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Sum parity on coefficient-kernel tensors
The ordinary-right kernel transport in DeformedMatrixComparison §4 retains
the sum grading. Grading data is attached to the kernel's existing modules;
no change of coefficient or quotient module structures is made.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams TensorProduct Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
universe u
variable {k : Type u} [CommRing k] {C : Type u} [Category.{u} C]

/-- Parity projectors on the existing coefficient modules. -/
structure CoefficientGrading (K : Cᵒᵖ ⥤ ModuleCat.{u} k) where
  odd : ∀ v : C, K.obj (op v) →ₗ[k] K.obj (op v)
  odd_comp_odd : ∀ v, odd v ∘ₗ odd v = odd v

def coefficientSpace {K : Cᵒᵖ ⥤ ModuleCat.{u} k} (G : CoefficientGrading K) (v : C) : SVec k where
  carrier := K.obj (op v)
  odd := G.odd v
  odd_comp_odd := G.odd_comp_odd v

def coefficientProj {K : Cᵒᵖ ⥤ ModuleCat.{u} k} (G : CoefficientGrading K)
    (v : C) (q : ZMod 2) : K.obj (op v) →ₗ[k] K.obj (op v) :=
  if q = 0 then LinearMap.id - G.odd v else G.odd v

@[simp] theorem coefficientProj_idem {K : Cᵒᵖ ⥤ ModuleCat.{u} k} (G : CoefficientGrading K)
    (v : C) (q : ZMod 2) (x : K.obj (op v)) :
    coefficientProj G v q (coefficientProj G v q x) = coefficientProj G v q x :=
  SVec.proj_proj_apply (coefficientSpace G v) q x

@[simp] theorem coefficientProj_zero_one {K : Cᵒᵖ ⥤ ModuleCat.{u} k} (G : CoefficientGrading K)
    (v : C) (x : K.obj (op v)) :
    coefficientProj G v 0 (coefficientProj G v 1 x) = 0 :=
  SVec.proj_zero_proj_one (coefficientSpace G v) x

@[simp] theorem coefficientProj_one_zero {K : Cᵒᵖ ⥤ ModuleCat.{u} k} (G : CoefficientGrading K)
    (v : C) (x : K.obj (op v)) :
    coefficientProj G v 1 (coefficientProj G v 0 x) = 0 :=
  SVec.proj_one_proj_zero (coefficientSpace G v) x

theorem coefficientProj_add {K : Cᵒᵖ ⥤ ModuleCat.{u} k} (G : CoefficientGrading K)
    (v : C) (x : K.obj (op v)) :
    coefficientProj G v 0 x + coefficientProj G v 1 x = x :=
  SVec.proj_apply_add (coefficientSpace G v) x

@[simp] theorem tensor_add_left (K : Cᵒᵖ ⥤ ModuleCat.{u} k) (M : C ⥤ SVec k)
    (v : C) (x y : K.obj (op v)) (m : M.obj v) :
    tensor K M v (x + y) m = tensor K M v x m + tensor K M v y m := by
  simp [tensor, add_tmul]

@[simp] theorem tensor_add_right (K : Cᵒᵖ ⥤ ModuleCat.{u} k) (M : C ⥤ SVec k)
    (v : C) (x : K.obj (op v)) (m n : M.obj v) :
    tensor K M v x (m + n) = tensor K M v x m + tensor K M v x n := by
  simp [tensor, tmul_add]

@[simp] theorem tensor_zero_left (K : Cᵒᵖ ⥤ ModuleCat.{u} k) (M : C ⥤ SVec k)
    (v : C) (m : M.obj v) : tensor K M v 0 m = 0 := by simp [tensor]
@[simp] theorem tensor_zero_right (K : Cᵒᵖ ⥤ ModuleCat.{u} k) (M : C ⥤ SVec k)
    (v : C) (x : K.obj (op v)) : tensor K M v x 0 = 0 := by simp [tensor]

variable (K : Cᵒᵖ ⥤ ModuleCat.{u} k) (G : CoefficientGrading K) (M : C ⥤ SVec k)

def oddSummand (v : C) :
    (K.obj (op v)) ⊗[k] M.obj v →ₗ[k] Obj K M :=
  inclusion K M v ∘ₗ
    (TensorProduct.map (coefficientProj G v 1) ((M.obj v).proj 0) +
      TensorProduct.map (coefficientProj G v 0) ((M.obj v).proj 1))

@[simp] theorem oddSummand_tmul (v : C) (x : K.obj (op v)) (m : M.obj v) :
    oddSummand K G M v (x ⊗ₜ[k] m) =
      tensor K M v (coefficientProj G v 1 x) ((M.obj v).proj 0 m) +
      tensor K M v (coefficientProj G v 0 x) ((M.obj v).proj 1 m) := by
  change inclusion K M v
    (TensorProduct.map (coefficientProj G v 1) ((M.obj v).proj 0) (x ⊗ₜ[k] m) +
      TensorProduct.map (coefficientProj G v 0) ((M.obj v).proj 1) (x ⊗ₜ[k] m)) = _
  rw [map_add, TensorProduct.map_tmul, TensorProduct.map_tmul]
  rfl

variable [Preadditive C] [Linear k C] [Supercategory k C]
  [K.Additive] [M.Additive] [M.Linear k] [IsSuperfunctor k M]

/-- Ordinary-right source actions have their specified degree. -/
def IsGradedKernel : Prop :=
  ∀ (v w : C) (p : ZMod 2) (a : v ⟶ w),
    a ∈ parity (R := k) v w p →
      ((K.map a.op).hom : coefficientSpace G w ⟶ coefficientSpace G v) ∈
        parity (R := k) (coefficientSpace G w) (coefficientSpace G v) p

variable (hK : IsGradedKernel K G)
include hK

theorem oddSummand_balance (v w : C) (a : v ⟶ w)
    (x : K.obj (op w)) (m : M.obj v) :
    oddSummand K G M v ((K.map a.op x) ⊗ₜ[k] m) =
      oddSummand K G M w (x ⊗ₜ[k] M.map a m) := by
  refine Supercategory.induction_on (R := k) a ?_ (fun p a ha => ?_) ?_
  · simp
  · have hk := hK v w p a ha
    have hm := map_mem M ha
    have k0 := SVec.apply_proj_of_mem hk 0 x
    have k1 := SVec.apply_proj_of_mem hk 1 x
    change (K.map a.op) (coefficientProj G w 0 x) =
      coefficientProj G v (0 + p) ((K.map a.op) x) at k0
    change (K.map a.op) (coefficientProj G w 1 x) =
      coefficientProj G v (1 + p) ((K.map a.op) x) at k1
    have m0 := SVec.apply_proj_of_mem hm 0 m
    have m1 := SVec.apply_proj_of_mem hm 1 m
    rcases parity_eq_zero_or_one p with rfl | rfl
    · simp only [add_zero] at k0 k1 m0 m1
      simp only [oddSummand_tmul, ← k0, ← k1, ← m0, ← m1, balance]
    · simp only [zero_add, SVec.zmod2_one_add_one] at k0 k1 m0 m1
      simp only [oddSummand_tmul, ← k0, ← k1, ← m0, ← m1, balance]
      exact add_comm _ _
  · intro a b ha hb
    have hkadd : K.map (a + b).op = K.map a.op + K.map b.op := K.map_add
    rw [hkadd, M.map_add]
    change oddSummand K G M v (((K.map a.op) x + (K.map b.op) x) ⊗ₜ[k] m) =
      oddSummand K G M w (x ⊗ₜ[k] ((M.map a) m + (M.map b) m))
    simpa only [add_tmul, tmul_add, map_add] using congrArg₂ (· + ·) ha hb

def odd : Obj K M →ₗ[k] Obj K M :=
  lift K M (oddSummand K G M) (oddSummand_balance K G M hK)

@[simp] theorem odd_tensor (v : C) (x : K.obj (op v)) (m : M.obj v) :
    odd K G M hK (tensor K M v x m) =
      tensor K M v (coefficientProj G v 1 x) ((M.obj v).proj 0 m) +
      tensor K M v (coefficientProj G v 0 x) ((M.obj v).proj 1 m) := by
  rw [odd, lift_tensor, oddSummand_tmul]

theorem odd_comp_odd : odd K G M hK ∘ₗ odd K G M hK = odd K G M hK := by
  apply hom_ext
  intro v x m
  simp [SVec.proj_proj_apply]

/-- Sum parity on the same literal balanced quotient. -/
abbrev superspace : SVec k where
  carrier := Obj K M
  odd := odd K G M hK
  odd_comp_odd := odd_comp_odd K G M hK

theorem proj_tensor (q : ZMod 2) (v : C) (x : K.obj (op v)) (m : M.obj v) :
    (superspace K G M hK).proj q (tensor K M v x m) =
      tensor K M v (coefficientProj G v q x) ((M.obj v).proj 0 m) +
      tensor K M v (coefficientProj G v (q + 1) x) ((M.obj v).proj 1 m) := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change tensor K M v x m - odd K G M hK (tensor K M v x m) = _
    rw [odd_tensor]
    have e : tensor K M v x m = tensor K M v
        (coefficientProj G v 0 x + coefficientProj G v 1 x)
        ((M.obj v).proj 0 m + (M.obj v).proj 1 m) := by
      rw [coefficientProj_add, SVec.proj_apply_add]
    rw [e]
    simp only [tensor_add_left, tensor_add_right, zero_add]
    abel
  · simpa only [SVec.proj_one, SVec.zmod2_one_add_one] using odd_tensor K G M hK v x m

/-- Even coefficient-kernel maps preserve the quotient sum grading. -/
theorem map_even {L : Cᵒᵖ ⥤ ModuleCat.{u} k} [L.Additive]
    (H : CoefficientGrading L) (hL : IsGradedKernel L H)
    (e : K ⟶ L)
    (he : ∀ v : C, (e.app (op v)).hom ∈
      parity (R := k) (coefficientSpace G v) (coefficientSpace H v) 0) :
    (map M e : superspace K G M hK ⟶ superspace L H M hL) ∈
      parity (R := k) (superspace K G M hK) (superspace L H M hL) 0 := by
  change ∀ q, map M e ∘ₗ (superspace K G M hK).proj q =
    (superspace L H M hL).proj (q + 0) ∘ₗ map M e
  intro q
  rw [add_zero]
  apply hom_ext
  intro v x m
  change map M e ((superspace K G M hK).proj q (tensor K M v x m)) =
    (superspace L H M hL).proj q (map M e (tensor K M v x m))
  rw [proj_tensor, map_add, map_tensor, map_tensor, map_tensor, proj_tensor]
  have h0 := SVec.apply_proj_of_mem (he v) q x
  have h1 := SVec.apply_proj_of_mem (he v) (q + 1) x
  change (e.app (op v)) (coefficientProj G v q x) =
    coefficientProj H v (q + 0) ((e.app (op v)) x) at h0
  change (e.app (op v)) (coefficientProj G v (q + 1) x) =
    coefficientProj H v ((q + 1) + 0) ((e.app (op v)) x) at h1
  simp only [add_zero] at h0 h1
  rw [h0, h1]

end OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
end

end
