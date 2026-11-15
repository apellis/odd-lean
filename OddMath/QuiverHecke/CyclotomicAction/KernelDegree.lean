import OddMath.QuiverHecke.HomDimension
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.CentreFinite
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop

/-!
# Kernel degree

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Lower degree bounds for cyclotomic kernels

Finite permutations of the boundary content give a uniform lower source
bound without finiteness of the colour set. Homogeneous sandwiches of the
first-position relation then have a cutoff-dependent lower degree.
-/
noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous)

/-- Different contents have zero full coefficient Hom. -/
theorem hom_eq_zero_of_not_perm (cutoff : I → ℕ) {v w : List I}
    (h : ¬ w.Perm v) (f : hom D Sc cutoff v w) : f = 0 := by
  change f = (0 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ⊗[k]
    ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)))
  refine TensorProduct.inductionOn (motive := fun z => z = 0) f
    (fun a g => ?_) (fun a b ha hb => ?_)
  · rw [QuiverHecke.hom_eq_zero_of_not_perm D Sc h g, TensorProduct.tmul_zero]
  · rw [ha, hb, add_zero]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Balanced tensors of many-object kernels

The kernel-tensor step in DeformedMatrixComparison, section 4: an isomorphism
of ordinary-right coefficient kernels remains an isomorphism after tensoring
with any module. The quotient is constructed explicitly over the ground ring.
No colimit in the category of supernatural module maps is assumed. Parity
shifts belong to the coefficient kernels; compatibility with their gradings
and identification of a particular action kernel are separate statements.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams TensorProduct
open scoped DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
universe u
variable {k : Type u} [CommRing k] {C : Type u} [Category.{u} C]
variable (K : Cᵒᵖ ⥤ ModuleCat k) (M : C ⥤ SVec k)

abbrev Raw := ⨁ v : C, (K.obj (op v)) ⊗[k] M.obj v

def rawTensor (v : C) (x : K.obj (op v)) (m : M.obj v) : Raw K M :=
  DirectSum.lof k C (fun v => (K.obj (op v)) ⊗[k] M.obj v) v (x ⊗ₜ[k] m)

/-- All source arrows occur in the balance, including inhomogeneous arrows. -/
def relations : Submodule k (Raw K M) :=
  Submodule.span k {z | ∃ (v w : C) (a : v ⟶ w)
    (x : K.obj (op w)) (m : M.obj v),
    z = rawTensor K M v (K.map a.op x) m - rawTensor K M w x (M.map a m)}

abbrev Obj := Raw K M ⧸ relations K M

def inclusion (v : C) : (K.obj (op v)) ⊗[k] M.obj v →ₗ[k] Obj K M :=
  (relations K M).mkQ ∘ₗ DirectSum.lof k C
    (fun v => (K.obj (op v)) ⊗[k] M.obj v) v

def tensor (v : C) (x : K.obj (op v)) (m : M.obj v) : Obj K M :=
  inclusion K M v (x ⊗ₜ[k] m)

theorem balance {v w : C} (a : v ⟶ w) (x : K.obj (op w)) (m : M.obj v) :
    tensor K M v (K.map a.op x) m = tensor K M w x (M.map a m) := by
  apply sub_eq_zero.mp
  change (relations K M).mkQ (rawTensor K M v (K.map a.op x) m) -
    (relations K M).mkQ (rawTensor K M w x (M.map a m)) = 0
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨v, w, a, x, m, rfl⟩)

variable {V : Type u} [AddCommGroup V] [Module k V]

def lift (q : ∀ v : C, (K.obj (op v)) ⊗[k] M.obj v →ₗ[k] V)
    (hq : ∀ (v w : C) (a : v ⟶ w) (x : K.obj (op w)) (m : M.obj v),
      q v ((K.map a.op x) ⊗ₜ[k] m) = q w (x ⊗ₜ[k] M.map a m)) :
    Obj K M →ₗ[k] V :=
  (relations K M).liftQ (DirectSum.toModule k C V q) (by
    apply Submodule.span_le.mpr
    rintro z ⟨v, w, a, x, m, rfl⟩
    change (DirectSum.toModule k C V q) _ = 0
    simp only [map_sub, rawTensor, DirectSum.toModule_lof]
    exact sub_eq_zero.mpr (hq v w a x m))

@[simp] theorem lift_tensor
    (q : ∀ v : C, (K.obj (op v)) ⊗[k] M.obj v →ₗ[k] V) (hq)
    (v : C) (x : K.obj (op v)) (m : M.obj v) :
    lift K M q hq (tensor K M v x m) = q v (x ⊗ₜ[k] m) := by
  simp [lift, tensor, inclusion]

@[ext] theorem hom_ext {a b : Obj K M →ₗ[k] V}
    (h : ∀ (v : C) (x : K.obj (op v)) (m : M.obj v),
      a (tensor K M v x m) = b (tensor K M v x m)) : a = b := by
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations K M)) |>.mp
  apply DirectSum.linearMap_ext
  intro v
  apply TensorProduct.ext
  ext x m
  exact h v x m

variable {K} {L P : Cᵒᵖ ⥤ ModuleCat k}

/-- A natural coefficient-kernel map descends through the literal balance. -/
def map (e : K ⟶ L) : Obj K M →ₗ[k] Obj L M :=
  lift K M (fun v => inclusion L M v ∘ₗ
    TensorProduct.map (e.app (op v)).hom LinearMap.id) (by
    intro v w a x m
    have he := congrArg (fun f : K.obj (op w) ⟶ L.obj (op v) => f x)
      (e.naturality a.op)
    change e.app (op v) (K.map a.op x) = L.map a.op (e.app (op w) x) at he
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [he]
    exact balance L M a (e.app (op w) x) m)

@[simp] theorem map_tensor (e : K ⟶ L) (v : C)
    (x : K.obj (op v)) (m : M.obj v) :
    map M e (tensor K M v x m) = tensor L M v (e.app (op v) x) m := by
  rw [map, lift_tensor]
  rfl

@[simp] theorem map_id : map M (𝟙 K) = LinearMap.id := by
  apply hom_ext
  intro v x m
  rw [map_tensor]
  rfl

theorem map_comp (e : K ⟶ L) (f : L ⟶ P) :
    map M (e ≫ f) = map M f ∘ₗ map M e := by
  apply hom_ext
  intro v x m
  simp only [map_tensor, LinearMap.comp_apply]
  rfl

/-- Tensoring a coefficient-kernel natural isomorphism with any module.
This is a quotient-level theorem, with no flatness or projectivity hypothesis. -/
def equiv (e : K ≅ L) : Obj K M ≃ₗ[k] Obj L M :=
  LinearEquiv.ofLinearMap (map M e.hom) (map M e.inv)
    (by rw [← map_comp, e.inv_hom_id, map_id])
    (by rw [← map_comp, e.hom_inv_id, map_id])

@[simp] theorem equiv_tensor (e : K ≅ L) (v : C)
    (x : K.obj (op v)) (m : M.obj v) :
    equiv M e (tensor K M v x m) = tensor L M v (e.hom.app (op v) x) m :=
  map_tensor M e.hom v x m

/-- Bijectivity of the forward components supplies inverse naturality.
No chosen component inverse is assumed natural as an additional hypothesis. -/
def coefficientIso (e : K ⟶ L) (he : ∀ v, Function.Bijective (e.app v)) : K ≅ L :=
  NatIso.ofComponents
    (fun v => (LinearEquiv.ofBijective (e.app v).hom (he v)).toModuleIso)
    (by
      intro v w a
      change K.map a ≫ e.app w = e.app v ≫ L.map a
      exact e.naturality a)

/-- Componentwise bijective natural kernel maps induce quotient equivalences. -/
def equivOfBijective (e : K ⟶ L) (he : ∀ v, Function.Bijective (e.app v)) :
    Obj K M ≃ₗ[k] Obj L M :=
  equiv M (coefficientIso e he)

end OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
end

end

section

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
  change evaluate J M v t (m + m')
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s g b) =
    evaluate J M v t m
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s g b) +
    evaluate J M v t m'
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s g b)
  rw [evaluate_tensor, evaluate_tensor, evaluate_tensor, map_add]
  simp only [BalancedInduction.tensor, tmul_add, map_add]

theorem evaluate_smul (v t : D) (r : k) (m : M.obj v) :
    evaluate J M v t (r • m) = r • evaluate J M v t m := by
  apply BalancedInduction.hom_ext
  intro s g b
  change evaluate J M v t (r • m)
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s g b) =
    r • evaluate J M v t m
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s g b)
  rw [evaluate_tensor, evaluate_tensor, map_smul]
  simp only [BalancedInduction.tensor, tmul_smul, map_smul]

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

omit [M.Additive] [M.Linear k] in
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
end

end

section

/-! # Off-content coefficient-kernel components vanish

A pure IndRes coefficient tensor has arrows v → J(s) → t. When v and t
have different colour content, at least one arrow is zero. Thus the actual
balanced quotient is zero, without finite colours, degree bounds, or a
whole-category/content equivalence. This supplies the zero branch for a
fixed-target finite matrix count on the full old coefficient category.
-/
noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Content conservation descends through the actual old cyclotomic quotient. -/
theorem old_eq_zero_of_not_perm {v t : List I} (h : ¬ t.Perm v)
    (f : Old D Sc cutoff v t) : f = 0 := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective f
  rw [hom_eq_zero_of_not_perm D Sc cutoff h r, map_zero]

theorem old_eq_zero_of_content_ne {v t : List I}
    (h : (v : Multiset I) ≠ (t : Multiset I)) (f : Old D Sc cutoff v t) : f = 0 := by
  apply old_eq_zero_of_not_perm D Sc cutoff (f := f)
  intro hp
  exact h (Multiset.coe_eq_coe.mpr hp.symm)

theorem oldCategory_hom_eq_zero_of_content_ne {v t : OldCategory D Sc cutoff}
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) (f : v ⟶ t) : f = 0 :=
  old_eq_zero_of_content_ne D Sc cutoff h f

theorem append_content_ne (i : I) {v t : List I}
    (h : (v : Multiset I) ≠ (t : Multiset I)) :
    ((v ++ [i] : List I) : Multiset I) ≠ ((t ++ [i] : List I) : Multiset I) := by
  intro he
  apply h
  change (v : Multiset I) + ([i] : Multiset I) = (t : Multiset I) + ([i] : Multiset I) at he
  exact add_right_cancel he

theorem append_hom_eq_zero_of_content_ne (i : I) {v t : OldCategory D Sc cutoff}
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I))
    (f : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) : f = 0 :=
  old_eq_zero_of_content_ne D Sc cutoff (append_content_ne i h) f

theorem oldCategory_hom_subsingleton_of_content_ne {v t : OldCategory D Sc cutoff}
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) : Subsingleton (v ⟶ t) :=
  ⟨fun f g => (oldCategory_hom_eq_zero_of_content_ne D Sc cutoff h f).trans
    (oldCategory_hom_eq_zero_of_content_ne D Sc cutoff h g).symm⟩

theorem append_hom_subsingleton_of_content_ne (i : I) {v t : OldCategory D Sc cutoff}
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) :
    Subsingleton ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) :=
  ⟨fun f g => (append_hom_eq_zero_of_content_ne D Sc cutoff i h f).trans
    (append_hom_eq_zero_of_content_ne D Sc cutoff i h g).symm⟩

/-- Every component of this double coend vanishes off content, for any source functor J. -/
theorem indResKernel_eq_zero_of_content_ne
    {C : Type u} [Category.{u} C] (J : C ⥤ OldCategory D Sc cutoff)
    {v t : OldCategory D Sc cutoff}
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I))
    (z : IndResKernel.Component (k := k) J v t) : z = 0 := by
  classical
  have hz : (LinearMap.id : IndResKernel.Component (k := k) J v t →ₗ[k]
      IndResKernel.Component (k := k) J v t) = 0 := by
    apply BalancedInduction.hom_ext
    intro s g b
    change BalancedInduction.tensor J (J ⋙ IndResKernel.homModule (k := k) v) s g b = 0
    by_cases hs : (v.word : Multiset I) = ((J.obj s).word : Multiset I)
    · have hg : g = 0 := oldCategory_hom_eq_zero_of_content_ne D Sc cutoff
        (fun he => h (hs.trans he)) g
      rw [hg]
      exact BalancedInduction.tensor_zero_left J (J ⋙ IndResKernel.homModule (k := k) v) s b
    · have hb : b = 0 := oldCategory_hom_eq_zero_of_content_ne D Sc cutoff hs b
      rw [hb]
      exact BalancedInduction.tensor_zero_right J (J ⋙ IndResKernel.homModule (k := k) v) s g
  exact LinearMap.congr_fun hz z

theorem indResKernel_subsingleton_of_content_ne
    {C : Type u} [Category.{u} C] (J : C ⥤ OldCategory D Sc cutoff)
    {v t : OldCategory D Sc cutoff}
    (h : (v.word : Multiset I) ≠ (t.word : Multiset I)) :
    Subsingleton (IndResKernel.Component (k := k) J v t) :=
  ⟨fun x y => (indResKernel_eq_zero_of_content_ne D Sc cutoff J h x).trans
    (indResKernel_eq_zero_of_content_ne D Sc cutoff J h y).symm⟩

end OddMath.QuiverHecke.ELVOld
end

end
