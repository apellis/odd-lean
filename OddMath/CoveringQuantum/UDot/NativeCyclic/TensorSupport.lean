import OddMath.CoveringQuantum.Coefficients.Splitting
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! Splittings and tensor injectivity over the covering coefficient ring. -/

noncomputable section
open TensorProduct
namespace OddMath.CoveringQuantum.Coefficients

/-- Semisimplicity is derived from the actual two specialization factors. -/
theorem covering_semisimple : IsSemisimpleRing Ring :=
  splitEquiv.symm.toRingEquiv.isSemisimpleRing

/-- Injections of covering modules split; neither module is assumed free. -/
theorem covering_injection_splits {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module Ring M] [Module Ring N] (f : M →ₗ[Ring] N) (hf : Function.Injective f) :
    ∃ r : N →ₗ[Ring] M, r.comp f = LinearMap.id := by
  let := covering_semisimple
  exact IsSemisimpleModule.extension_property f hf LinearMap.id

/-- Tensoring two injections is valid here because both have derived linear retractions. -/
theorem covering_tensor_injective {M N P Q : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module Ring M] [Module Ring N] [Module Ring P] [Module Ring Q]
    (f : M →ₗ[Ring] P) (g : N →ₗ[Ring] Q)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  obtain ⟨r, hr⟩ := covering_injection_splits f hf
  obtain ⟨s, hs⟩ := covering_injection_splits g hg
  have hcomp : (TensorProduct.map r s).comp (TensorProduct.map f g) = LinearMap.id := by
    rw [← TensorProduct.map_comp, hr, hs, TensorProduct.map_id]
  exact (show Function.LeftInverse (TensorProduct.map r s) (TensorProduct.map f g) from
    fun x => LinearMap.congr_fun hcomp x).injective

/-- Restricted factor injections detect the whole image of the finite-factor tensor,
not just pure tensors. -/
theorem covering_tensor_injOn_range {M N P Q : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module Ring M] [Module Ring N] [Module Ring P] [Module Ring Q]
    (S : Submodule Ring M) (T : Submodule Ring N)
    (f : M →ₗ[Ring] P) (g : N →ₗ[Ring] Q)
    (hf : Function.Injective (f.comp S.subtype))
    (hg : Function.Injective (g.comp T.subtype)) :
    Set.InjOn (TensorProduct.map f g) (LinearMap.range (TensorProduct.mapIncl S T)) := by
  rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ hab
  have hinj := covering_tensor_injective (f.comp S.subtype) (g.comp T.subtype) hf hg
  apply congrArg (TensorProduct.mapIncl S T)
  apply hinj
  simpa only [TensorProduct.mapIncl, TensorProduct.map_comp, LinearMap.comp_apply] using hab

end OddMath.CoveringQuantum.Coefficients
