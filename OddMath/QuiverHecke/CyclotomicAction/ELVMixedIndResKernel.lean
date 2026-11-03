import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernel

/-! # The two-functor induction-restriction coefficient kernel

The explicit kernel realization needed by DeformedActionAssembly, sections 3–4, for Brundan–Ellis (1.12).
The double balanced quotient reduces by the covariant representable pairing,
using only quotient lifts and identity insertion. The ordinary-right source
action is precomposition. Grading and the prescribed matrix comparison are
separate from this underlying ground-ring equivalence.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory TensorProduct
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld.MixedIndResKernel
universe u
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D] [Supercategory k D]

variable (A B : C ⥤ D)

abbrev Component (v t : D) := BalancedInduction.Obj A (B ⋙ IndResKernel.homModule (k := k) v) t

def precompose {u v : D} (a : u ⟶ v) (t : D) :
    Component (k := k) A B v t →ₗ[k] Component (k := k) A B u t :=
  BalancedInduction.lift A (B ⋙ IndResKernel.homModule (k := k) v) t
    (fun s => BalancedInduction.inclusion A (B ⋙ IndResKernel.homModule (k := k) u) t s ∘ₗ
      TensorProduct.map LinearMap.id (Linear.leftComp k (B.obj s) a)) (by
        intro s s' f g b
        change BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) u) s (A.map f ≫ g) (a ≫ b) =
          BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) u) s' g (a ≫ (b ≫ B.map f))
        rw [BalancedInduction.balance]
        congr 1
        exact Category.assoc a b (B.map f))

@[simp] theorem precompose_tensor {u v : D} (a : u ⟶ v) (t : D)
    (s : C) (g : A.obj s ⟶ t) (b : v ⟶ B.obj s) :
    precompose (k := k) A B a t (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) =
      BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) u) s g (a ≫ b) := by
  rw [precompose, BalancedInduction.lift_tensor]
  rfl

/-- The ordinary-right coefficient presheaf for induction after restriction. -/
def kernel (t : D) : Dᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (Component (k := k) A B v.unop t)
  map a := ModuleCat.ofHom (precompose (k := k) A B a.unop t)
  map_id v := by
    apply ModuleCat.hom_ext
    apply BalancedInduction.hom_ext
    intro s g b
    change precompose (k := k) A B (𝟙 v.unop) t
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v.unop) s g b) = _
    rw [precompose_tensor, Category.id_comp]
    rfl
  map_comp a b := by
    apply ModuleCat.hom_ext
    apply BalancedInduction.hom_ext
    intro s g h
    change precompose (k := k) A B (b.unop ≫ a.unop) t
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) _) s g h) =
      precompose (k := k) A B b.unop t (precompose (k := k) A B a.unop t
        (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) _) s g h))
    simp only [precompose_tensor]
    rw [Category.assoc]

variable (M : D ⥤ SVec k) [M.Additive] [M.Linear k]

/-- Evaluate the old representable factor on an arbitrary module element. -/
def evaluate (v t : D) (m : M.obj v) :
    Component (k := k) A B v t →ₗ[k] BalancedInduction.Obj A (B ⋙ M) t :=
  BalancedInduction.lift A (B ⋙ IndResKernel.homModule (k := k) v) t
    (fun s => BalancedInduction.inclusion A (B ⋙ M) t s ∘ₗ
      TensorProduct.map LinearMap.id
        ((M.mapLinearMap (R := k)).flip m)) (by
        intro s s' f g b
        change BalancedInduction.tensor A (B ⋙ M) s (A.map f ≫ g) (M.map b m) =
          BalancedInduction.tensor A (B ⋙ M) s' g (M.map (b ≫ B.map f) m)
        rw [BalancedInduction.balance, M.map_comp]
        rfl)

@[simp] theorem evaluate_tensor (v t : D) (m : M.obj v)
    (s : C) (g : A.obj s ⟶ t) (b : v ⟶ B.obj s) :
    evaluate A B M v t m (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) =
      BalancedInduction.tensor A (B ⋙ M) s g (M.map b m) := by
  rw [evaluate, BalancedInduction.lift_tensor]
  rfl

theorem evaluate_add (v t : D) (m m' : M.obj v) :
    evaluate A B M v t (m + m') = evaluate A B M v t m + evaluate A B M v t m' := by
  apply BalancedInduction.hom_ext
  intro s g b
  change evaluate A B M v t (m + m')
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) =
    evaluate A B M v t m
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) +
    evaluate A B M v t m'
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b)
  rw [evaluate_tensor, evaluate_tensor, evaluate_tensor, map_add]
  simp only [BalancedInduction.tensor, tmul_add, map_add]

theorem evaluate_smul (v t : D) (r : k) (m : M.obj v) :
    evaluate A B M v t (r • m) = r • evaluate A B M v t m := by
  apply BalancedInduction.hom_ext
  intro s g b
  change evaluate A B M v t (r • m)
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) =
    r • evaluate A B M v t m
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b)
  rw [evaluate_tensor, evaluate_tensor, map_smul]
  simp only [BalancedInduction.tensor, tmul_smul, map_smul]

def evaluatePair (v t : D) :
    Component (k := k) A B v t →ₗ[k] M.obj v →ₗ[k] BalancedInduction.Obj A (B ⋙ M) t where
  toFun x := {
    toFun := fun m => evaluate A B M v t m x
    map_add' := fun m m' => congrArg (fun f => f x) (evaluate_add A B M v t m m')
    map_smul' := fun r m => congrArg (fun f => f x) (evaluate_smul A B M v t r m) }
  map_add' x x' := by ext m; exact map_add (evaluate A B M v t m) x x'
  map_smul' r x := by ext m; exact map_smul (evaluate A B M v t m) r x

theorem evaluate_precompose {v w : D} (a : v ⟶ w) (t : D) (m : M.obj v) :
    evaluate A B M v t m ∘ₗ precompose (k := k) A B a t =
      evaluate A B M w t (M.map a m) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, precompose_tensor, evaluate_tensor, M.map_comp]
  rfl

/-- Flatten the two balances by evaluating the representable factor. -/
def forward (t : D) : BalancedKernelTensor.Obj (kernel (k := k) A B t) M →ₗ[k]
    BalancedInduction.Obj A (B ⋙ M) t :=
  BalancedKernelTensor.lift (kernel (k := k) A B t) M
    (fun v => TensorProduct.lift (evaluatePair A B M v t)) (by
      intro v w a x m
      change evaluate A B M v t m (precompose (k := k) A B a t x) =
        evaluate A B M w t (M.map a m) x
      exact congrArg (fun f => f x) (evaluate_precompose (k := k) A B M a t m))

@[simp] theorem forward_tensor (t v : D) (x : Component (k := k) A B v t) (m : M.obj v) :
    forward A B M t (BalancedKernelTensor.tensor (kernel (k := k) A B t) M v x m) =
      evaluate A B M v t m x := by
  rw [forward, BalancedKernelTensor.lift_tensor]
  rfl

/-- Insert the identity into the representable factor. -/
def identityLift (t : D) (s : C) : (A.obj s ⟶ t) →ₗ[k] Component (k := k) A B (B.obj s) t :=
  BalancedInduction.inclusion A (B ⋙ IndResKernel.homModule (k := k) (B.obj s)) t s ∘ₗ
    (TensorProduct.mk k (A.obj s ⟶ t) (B.obj s ⟶ B.obj s)).flip (𝟙 _)

@[simp] theorem identityLift_apply (t : D) (s : C) (g : A.obj s ⟶ t) :
    identityLift (k := k) A B t s g =
      BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) (B.obj s)) s g (𝟙 _) := rfl

theorem identityLift_balance {s s' : C} (f : s ⟶ s') (t : D) (g : A.obj s' ⟶ t) :
    identityLift (k := k) A B t s (A.map f ≫ g) =
      precompose (k := k) A B (B.map f) t (identityLift (k := k) A B t s' g) := by
  rw [identityLift_apply, identityLift_apply, precompose_tensor,
    BalancedInduction.balance]
  change BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) (B.obj s)) s' g
    (𝟙 _ ≫ B.map f) =
    BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) (B.obj s)) s' g (B.map f ≫ 𝟙 _)
  rw [Category.id_comp, Category.comp_id]

def backward (t : D) : BalancedInduction.Obj A (B ⋙ M) t →ₗ[k]
    BalancedKernelTensor.Obj (kernel (k := k) A B t) M :=
  BalancedInduction.lift A (B ⋙ M) t
    (fun s => BalancedKernelTensor.inclusion (kernel (k := k) A B t) M (B.obj s) ∘ₗ
      TensorProduct.map (identityLift (k := k) A B t s) LinearMap.id) (by
      intro s s' f g m
      change BalancedKernelTensor.tensor (kernel (k := k) A B t) M (B.obj s)
        (identityLift (k := k) A B t s (A.map f ≫ g)) m =
        BalancedKernelTensor.tensor (kernel (k := k) A B t) M (B.obj s')
          (identityLift (k := k) A B t s' g) (M.map (B.map f) m)
      rw [identityLift_balance]
      exact BalancedKernelTensor.balance (kernel (k := k) A B t) M (B.map f)
        (identityLift (k := k) A B t s' g) m)

omit [M.Additive] [M.Linear k] in
@[simp] theorem backward_tensor (t : D) (s : C) (g : A.obj s ⟶ t)
    (m : M.obj (B.obj s)) :
    backward A B M t (BalancedInduction.tensor A (B ⋙ M) s g m) =
      BalancedKernelTensor.tensor (kernel (k := k) A B t) M (B.obj s) (identityLift (k := k) A B t s g) m := by
  rw [backward, BalancedInduction.lift_tensor]
  rfl

theorem forward_backward (t : D) : forward A B M t ∘ₗ backward A B M t = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s g m
  simp only [LinearMap.comp_apply, backward_tensor, forward_tensor,
    identityLift_apply, evaluate_tensor, M.map_id]
  rfl

theorem backward_forward (t : D) : backward A B M t ∘ₗ forward A B M t = LinearMap.id := by
  apply BalancedKernelTensor.hom_ext
  intro v x m
  have h : backward A B M t ∘ₗ evaluate A B M v t m =
      BalancedKernelTensor.inclusion (kernel (k := k) A B t) M v ∘ₗ
        (TensorProduct.mk k (Component (k := k) A B v t) (M.obj v)).flip m := by
    apply BalancedInduction.hom_ext
    intro s g b
    change backward A B M t (evaluate A B M v t m
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b)) =
      BalancedKernelTensor.tensor (kernel (k := k) A B t) M v
        (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) m
    rw [evaluate_tensor, backward_tensor]
    have hb := BalancedKernelTensor.balance (kernel (k := k) A B t) M b (identityLift (k := k) A B t s g) m
    change BalancedKernelTensor.tensor (kernel (k := k) A B t) M v
      (precompose (k := k) A B b t (identityLift (k := k) A B t s g)) m = _ at hb
    rw [identityLift_apply, precompose_tensor, Category.comp_id] at hb
    exact hb.symm
  change backward A B M t (forward A B M t
    (BalancedKernelTensor.tensor (kernel (k := k) A B t) M v x m)) = _
  rw [forward_tensor]
  exact congrArg (fun f => f x) h

/-- The coefficient kernel of induction-restriction acts on every module by
the existing balanced induction after restriction. No exactness is assumed. -/
def equiv (t : D) : BalancedKernelTensor.Obj (kernel (k := k) A B t) M ≃ₗ[k]
    BalancedInduction.Obj A (B ⋙ M) t :=
  LinearEquiv.ofLinearMap (forward A B M t) (backward A B M t)
    (forward_backward A B M t) (backward_forward A B M t)

@[simp] theorem equiv_tensor (t v : D) (x : Component (k := k) A B v t) (m : M.obj v) :
    equiv A B M t (BalancedKernelTensor.tensor (kernel (k := k) A B t) M v x m) =
      evaluate A B M v t m x := forward_tensor A B M t v x m

end OddMath.QuiverHecke.ELVOld.MixedIndResKernel
