import OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensor
import Mathlib.LinearAlgebra.Pi

/-! # Finite coefficient families commute with the literal kernel tensor

The finite Option(Fin m) families of DeformedMatrixComparison may be split
before or after tensoring their coefficient kernels with an arbitrary module.
The maps use explicit coordinate inclusions/projections, and both inverse
identities hold in the balanced quotient. No flatness premise occurs.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams TensorProduct
namespace OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
universe u
variable {k C : Type u} {ι : Type} [CommRing k] [Category.{u} C]
variable (K : ι → Cᵒᵖ ⥤ ModuleCat k)

/-- Pointwise finite product of ordinary-right coefficient kernels. -/
def piKernel : Cᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (∀ a, (K a).obj v)
  map f := ModuleCat.ofHom (LinearMap.piMap (fun a => ((K a).map f).hom))
  map_id v := by
    ext x a
    change ((K a).map (𝟙 v)) (x a) = x a
    rw [(K a).map_id]
    rfl
  map_comp f g := by
    ext x a
    change ((K a).map (f ≫ g)) (x a) = ((K a).map g) (((K a).map f) (x a))
    rw [(K a).map_comp]
    rfl

def piProjection (a : ι) : piKernel K ⟶ K a where
  app _ := ModuleCat.ofHom (LinearMap.proj a)
  naturality _ _ _ := rfl

variable [DecidableEq ι]

def piInjection (a : ι) : K a ⟶ piKernel K where
  app v := ModuleCat.ofHom (LinearMap.single k (fun a => (K a).obj v) a)
  naturality {v w} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext b
    change (Pi.single a ((K a).map f x) : ∀ c, (K c).obj w) b =
      (K b).map f ((Pi.single a x : ∀ c, (K c).obj v) b)
    by_cases h : b = a
    · subst b
      simp
    · simp [h]

theorem piInjection_projection (a : ι) : piInjection K a ≫ piProjection K a = 𝟙 (K a) := by
  ext v x
  change (Pi.single a x : ∀ b, (K b).obj v) a = x
  simp

theorem piInjection_projection_ne (a b : ι) (h : b ≠ a) :
    piInjection K a ≫ piProjection K b = 0 := by
  ext v x
  change (Pi.single a x : ∀ c, (K c).obj v) b = 0
  simp [h]

variable (M : C ⥤ SVec k)

private theorem tensor_zero_left (L : Cᵒᵖ ⥤ ModuleCat k) (v : C) (m : M.obj v) :
    tensor L M v 0 m = 0 := by
  simp only [tensor, zero_tmul, map_zero]

private theorem map_zero (L P : Cᵒᵖ ⥤ ModuleCat k) :
    map M (0 : L ⟶ P) = 0 := by
  apply hom_ext
  intro v x m
  rw [map_tensor]
  exact tensor_zero_left M P v m

private theorem projection_injection (a : ι) :
    map M (piProjection K a) ∘ₗ map M (piInjection K a) = LinearMap.id := by
  rw [← map_comp, piInjection_projection, map_id]

private theorem projection_injection_ne (a b : ι) (h : b ≠ a) :
    map M (piProjection K b) ∘ₗ map M (piInjection K a) = 0 := by
  rw [← map_comp, piInjection_projection_ne K a b h, map_zero]

/-- Coordinate projections on the actual balanced quotients. -/
def toPi : Obj (piKernel K) M →ₗ[k] (∀ a, Obj (K a) M) :=
  LinearMap.pi (fun a => map M (piProjection K a))

omit [DecidableEq ι] in
@[simp] theorem toPi_tensor (v : C) (x : (piKernel K).obj (op v))
    (m : M.obj v) (a : ι) :
    toPi K M (tensor (piKernel K) M v x m) a = tensor (K a) M v (x a) m := by
  exact map_tensor M (piProjection K a) v x m

variable [Fintype ι]

/-- Coordinate inclusions summed in the actual balanced quotient. -/
def fromPi : (∀ a, Obj (K a) M) →ₗ[k] Obj (piKernel K) M :=
  ∑ a, map M (piInjection K a) ∘ₗ LinearMap.proj a

theorem fromPi_toPi : fromPi K M ∘ₗ toPi K M = LinearMap.id := by
  apply hom_ext
  intro v x m
  change (∑ a, map M (piInjection K a) ∘ₗ LinearMap.proj a)
    (toPi K M (tensor (piKernel K) M v x m)) = tensor (piKernel K) M v x m
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    toPi_tensor, map_tensor]
  change (∑ a, inclusion (piKernel K) M v (Pi.single a (x a) ⊗ₜ[k] m)) =
    inclusion (piKernel K) M v (x ⊗ₜ[k] m)
  rw [← map_sum, ← sum_tmul, LinearMap.sum_single_apply]

theorem toPi_fromPi : toPi K M ∘ₗ fromPi K M = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext b
  change toPi K M ((∑ a, map M (piInjection K a) ∘ₗ LinearMap.proj a) x) b = x b
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum,
    toPi, LinearMap.pi_apply]
  calc
    _ = map M (piProjection K b) (map M (piInjection K b) (x b)) := by
      apply Finset.sum_eq_single b
      · intro a _ hab
        exact LinearMap.congr_fun (projection_injection_ne K M a b (Ne.symm hab)) (x a)
      · simp
    _ = x b := LinearMap.congr_fun (projection_injection K M b) (x b)

/-- Finite coefficient products commute with kernel tensor, without flatness. -/
def piEquiv : Obj (piKernel K) M ≃ₗ[k] (∀ a, Obj (K a) M) :=
  LinearEquiv.ofLinearMap (toPi K M) (fromPi K M) (toPi_fromPi K M) (fromPi_toPi K M)

end OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
