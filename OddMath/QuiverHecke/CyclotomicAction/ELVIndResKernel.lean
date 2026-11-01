import OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensor

/-! # The induction-restriction coefficient kernel

The explicit kernel realization needed by DeformedMatrixComparison, section 4.
The double balanced quotient reduces by the covariant representable pairing,
using only quotient lifts and identity insertion. The ordinary-right source
action is precomposition. Grading and the prescribed matrix comparison are
separate from this underlying ground-ring equivalence.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory TensorProduct
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld.IndResKernel
universe u
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D] [Supercategory k D]

/-- Covariant Hom with its existing Hom superspace, retaining every arrow. -/
def homModule (v : D) : D ⥤ SVec k where
  obj := homSVec k D v
  map f := {
    toFun := fun b => b ≫ f
    map_add' := fun _ _ => Preadditive.add_comp _ _ _ _ _ _
    map_smul' := fun _ _ => Linear.smul_comp _ _ _ _ _ _ }
  map_id _ := by ext b; exact Category.comp_id b
  map_comp f g := by ext b; exact (Category.assoc b f g).symm

variable (J : C ⥤ D)

abbrev Component (v t : D) := BalancedInduction.Obj J (J ⋙ homModule (k := k) v) t

def precompose {u v : D} (a : u ⟶ v) (t : D) :
    Component (k := k) J v t →ₗ[k] Component (k := k) J u t :=
  BalancedInduction.lift J (J ⋙ homModule (k := k) v) t
    (fun s => BalancedInduction.inclusion J (J ⋙ homModule (k := k) u) t s ∘ₗ
      TensorProduct.map LinearMap.id (Linear.leftComp k (J.obj s) a)) (by
        intro s s' f g b
        change BalancedInduction.tensor J (J ⋙ homModule (k := k) u) s (J.map f ≫ g) (a ≫ b) =
          BalancedInduction.tensor J (J ⋙ homModule (k := k) u) s' g (a ≫ (b ≫ J.map f))
        rw [BalancedInduction.balance]
        congr 1
        exact Category.assoc a b (J.map f))

@[simp] theorem precompose_tensor {u v : D} (a : u ⟶ v) (t : D)
    (s : C) (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) :
    precompose (k := k) J a t (BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s g b) =
      BalancedInduction.tensor J (J ⋙ homModule (k := k) u) s g (a ≫ b) := by
  rw [precompose, BalancedInduction.lift_tensor]
  rfl

/-- The ordinary-right coefficient presheaf for induction after restriction. -/
def kernel (t : D) : Dᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (Component (k := k) J v.unop t)
  map a := ModuleCat.ofHom (precompose (k := k) J a.unop t)
  map_id v := by
    apply ModuleCat.hom_ext
    apply BalancedInduction.hom_ext
    intro s g b
    change precompose (k := k) J (𝟙 v.unop) t
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) v.unop) s g b) = _
    rw [precompose_tensor, Category.id_comp]
    rfl
  map_comp a b := by
    apply ModuleCat.hom_ext
    apply BalancedInduction.hom_ext
    intro s g h
    change precompose (k := k) J (b.unop ≫ a.unop) t
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) _) s g h) =
      precompose (k := k) J b.unop t (precompose (k := k) J a.unop t
        (BalancedInduction.tensor J (J ⋙ homModule (k := k) _) s g h))
    simp only [precompose_tensor]
    rw [Category.assoc]

variable (M : D ⥤ SVec k) [M.Additive] [M.Linear k]

/-- Evaluate the old representable factor on an arbitrary module element. -/
def evaluate (v t : D) (m : M.obj v) :
    Component (k := k) J v t →ₗ[k] BalancedInduction.Obj J (J ⋙ M) t :=
  BalancedInduction.lift J (J ⋙ homModule (k := k) v) t
    (fun s => BalancedInduction.inclusion J (J ⋙ M) t s ∘ₗ
      TensorProduct.map LinearMap.id
        ((M.mapLinearMap (R := k)).flip m)) (by
        intro s s' f g b
        change BalancedInduction.tensor J (J ⋙ M) s (J.map f ≫ g) (M.map b m) =
          BalancedInduction.tensor J (J ⋙ M) s' g (M.map (b ≫ J.map f) m)
        rw [BalancedInduction.balance, M.map_comp]
        rfl)

@[simp] theorem evaluate_tensor (v t : D) (m : M.obj v)
    (s : C) (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) :
    evaluate J M v t m (BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s g b) =
      BalancedInduction.tensor J (J ⋙ M) s g (M.map b m) := by
  rw [evaluate, BalancedInduction.lift_tensor]
  rfl

theorem evaluate_add (v t : D) (m m' : M.obj v) :
    evaluate J M v t (m + m') = evaluate J M v t m + evaluate J M v t m' := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [evaluate_tensor, LinearMap.add_apply, map_add,
    BalancedInduction.tensor, tmul_add]

theorem evaluate_smul (v t : D) (r : k) (m : M.obj v) :
    evaluate J M v t (r • m) = r • evaluate J M v t m := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [evaluate_tensor, LinearMap.smul_apply, map_smul,
    BalancedInduction.tensor, tmul_smul]

def evaluatePair (v t : D) :
    Component (k := k) J v t →ₗ[k] M.obj v →ₗ[k] BalancedInduction.Obj J (J ⋙ M) t where
  toFun x := {
    toFun := fun m => evaluate J M v t m x
    map_add' := fun m m' => congrArg (fun f => f x) (evaluate_add J M v t m m')
    map_smul' := fun r m => congrArg (fun f => f x) (evaluate_smul J M v t r m) }
  map_add' x x' := by ext m; exact map_add (evaluate J M v t m) x x'
  map_smul' r x := by ext m; exact map_smul (evaluate J M v t m) r x

theorem evaluate_precompose {v w : D} (a : v ⟶ w) (t : D) (m : M.obj v) :
    evaluate J M v t m ∘ₗ precompose (k := k) J a t =
      evaluate J M w t (M.map a m) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, precompose_tensor, evaluate_tensor, M.map_comp]
  rfl

/-- Flatten the two balances by evaluating the representable factor. -/
def forward (t : D) : BalancedKernelTensor.Obj (kernel (k := k) J t) M →ₗ[k]
    BalancedInduction.Obj J (J ⋙ M) t :=
  BalancedKernelTensor.lift (kernel (k := k) J t) M
    (fun v => TensorProduct.lift (evaluatePair J M v t)) (by
      intro v w a x m
      change evaluate J M v t m (precompose (k := k) J a t x) =
        evaluate J M w t (M.map a m) x
      exact congrArg (fun f => f x) (evaluate_precompose (k := k) J M a t m))

@[simp] theorem forward_tensor (t v : D) (x : Component (k := k) J v t) (m : M.obj v) :
    forward J M t (BalancedKernelTensor.tensor (kernel (k := k) J t) M v x m) =
      evaluate J M v t m x := by
  rw [forward, BalancedKernelTensor.lift_tensor]
  rfl

/-- Insert the identity into the representable factor. -/
def identityLift (t : D) (s : C) : (J.obj s ⟶ t) →ₗ[k] Component (k := k) J (J.obj s) t :=
  BalancedInduction.inclusion J (J ⋙ homModule (k := k) (J.obj s)) t s ∘ₗ
    (TensorProduct.mk k (J.obj s ⟶ t) (J.obj s ⟶ J.obj s)).flip (𝟙 _)

@[simp] theorem identityLift_apply (t : D) (s : C) (g : J.obj s ⟶ t) :
    identityLift (k := k) J t s g =
      BalancedInduction.tensor J (J ⋙ homModule (k := k) (J.obj s)) s g (𝟙 _) := rfl

theorem identityLift_balance {s s' : C} (f : s ⟶ s') (t : D) (g : J.obj s' ⟶ t) :
    identityLift (k := k) J t s (J.map f ≫ g) =
      precompose (k := k) J (J.map f) t (identityLift (k := k) J t s' g) := by
  rw [identityLift_apply, identityLift_apply, precompose_tensor,
    BalancedInduction.balance]
  change BalancedInduction.tensor J (J ⋙ homModule (k := k) (J.obj s)) s' g
    (𝟙 _ ≫ J.map f) =
    BalancedInduction.tensor J (J ⋙ homModule (k := k) (J.obj s)) s' g (J.map f ≫ 𝟙 _)
  rw [Category.id_comp, Category.comp_id]

def backward (t : D) : BalancedInduction.Obj J (J ⋙ M) t →ₗ[k]
    BalancedKernelTensor.Obj (kernel (k := k) J t) M :=
  BalancedInduction.lift J (J ⋙ M) t
    (fun s => BalancedKernelTensor.inclusion (kernel (k := k) J t) M (J.obj s) ∘ₗ
      TensorProduct.map (identityLift (k := k) J t s) LinearMap.id) (by
      intro s s' f g m
      change BalancedKernelTensor.tensor (kernel (k := k) J t) M (J.obj s)
        (identityLift (k := k) J t s (J.map f ≫ g)) m =
        BalancedKernelTensor.tensor (kernel (k := k) J t) M (J.obj s')
          (identityLift (k := k) J t s' g) (M.map (J.map f) m)
      rw [identityLift_balance]
      exact BalancedKernelTensor.balance (kernel (k := k) J t) M (J.map f)
        (identityLift (k := k) J t s' g) m)

@[simp] theorem backward_tensor (t : D) (s : C) (g : J.obj s ⟶ t)
    (m : M.obj (J.obj s)) :
    backward J M t (BalancedInduction.tensor J (J ⋙ M) s g m) =
      BalancedKernelTensor.tensor (kernel (k := k) J t) M (J.obj s) (identityLift (k := k) J t s g) m := by
  rw [backward, BalancedInduction.lift_tensor]
  rfl

theorem forward_backward (t : D) : forward J M t ∘ₗ backward J M t = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s g m
  simp only [LinearMap.comp_apply, backward_tensor, forward_tensor,
    identityLift_apply, evaluate_tensor, M.map_id]
  rfl

theorem backward_forward (t : D) : backward J M t ∘ₗ forward J M t = LinearMap.id := by
  apply BalancedKernelTensor.hom_ext
  intro v x m
  have h : backward J M t ∘ₗ evaluate J M v t m =
      BalancedKernelTensor.inclusion (kernel (k := k) J t) M v ∘ₗ
        (TensorProduct.mk k (Component (k := k) J v t) (M.obj v)).flip m := by
    apply BalancedInduction.hom_ext
    intro s g b
    change backward J M t (evaluate J M v t m
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s g b)) =
      BalancedKernelTensor.tensor (kernel (k := k) J t) M v
        (BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s g b) m
    rw [evaluate_tensor, backward_tensor]
    have hb := BalancedKernelTensor.balance (kernel (k := k) J t) M b (identityLift (k := k) J t s g) m
    change BalancedKernelTensor.tensor (kernel (k := k) J t) M v
      (precompose (k := k) J b t (identityLift (k := k) J t s g)) m = _ at hb
    rw [identityLift_apply, precompose_tensor, Category.comp_id] at hb
    exact hb.symm
  change backward J M t (forward J M t
    (BalancedKernelTensor.tensor (kernel (k := k) J t) M v x m)) = _
  rw [forward_tensor]
  exact congrArg (fun f => f x) h

/-- The coefficient kernel of induction-restriction acts on every module by
the existing balanced induction after restriction. No exactness is assumed. -/
def equiv (t : D) : BalancedKernelTensor.Obj (kernel (k := k) J t) M ≃ₗ[k]
    BalancedInduction.Obj J (J ⋙ M) t :=
  LinearEquiv.ofLinearMap (forward J M t) (backward J M t)
    (forward_backward J M t) (backward_forward J M t)

end OddMath.QuiverHecke.ELVOld.IndResKernel
