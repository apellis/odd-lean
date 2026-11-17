import OddMath.QuiverHecke.CyclotomicAction.EvenInputMatrix.EvenCapFamilyCoordinates
import OddMath.QuiverHecke.CyclotomicAction.EvenInputMatrix.FiniteKernelTensor

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
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.TensorMatrixCoordinates
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.TensorMatrixCoordinates
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
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Actual finite kernel matrices off their target content -/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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
namespace OddMath.QuiverHecke.ELV.BalancedInduction
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

end OddMath.QuiverHecke.ELV.BalancedInduction
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
namespace OddMath.QuiverHecke.ELV.BalancedInduction
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

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
