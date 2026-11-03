import OddMath.QuiverHecke.CyclotomicAction.ELVCapSignNormalization
import Mathlib.Algebra.Module.LinearMap.End

/-! # Dot powers and output parity under comparison maps

The dotted unit and cap rows of DeformedMatrixComparison (1), (2), (5)
require powers of the same signed dot, followed by the prescribed output
parity correction. The rectangular comparison lemmas below apply to the
selected scalar and weighted append maps before coend carriers are specialized.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u

section LinearPowers
variable {k V W : Type u} [CommRing k]
  [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  (C : V →ₗ[k] W) (f : Module.End k V) (g : Module.End k W)

/-- A rectangular intertwiner carries every ordinary power of the given
signed operators to the same power of the target operator. -/
theorem intertwine_pow_apply (h : ∀ x, C (f x) = g (C x)) (n : ℕ) (x : V) :
    C ((f ^ n) x) = (g ^ n) (C x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

/-- The same rectangular power comparison as an equality of linear maps;
only additive commutative monoids are required for the two carriers. -/
theorem intertwine_pow (h : C ∘ₗ f = g ∘ₗ C) (n : ℕ) :
    C ∘ₗ (f ^ n) = (g ^ n) ∘ₗ C := by
  apply LinearMap.ext
  intro x
  exact intertwine_pow_apply C f g (fun x => LinearMap.congr_fun h x) n x

end LinearPowers

section Parity
variable {k : Type u} [CommRing k] (V W : SVec k)
  (C : V →ₗ[k] W) (hC : C ∈ SVec.parityHom V W 0)
include hC

/-- An even comparison preserves the whole output parity involution.
This is an identity of superspace maps, not a claim that parity is an
ordinary bimodule endomorphism. -/
theorem intertwine_sgn (q : ZMod 2) :
    C ∘ₗ V.sgn q = W.sgn q ∘ₗ C := by
  have h := SVec.sgn_comp_of_mem hC q
  simpa only [zero_mul, sign_zero, one_smul, SVec.toLinearMap] using h.symm

/-- The prescribed cap scalar and whole output parity correction commute
with an even comparison of the given signed dot operators. -/
theorem intertwine_capRowSign_apply
    (f : Module.End k V) (g : Module.End k W) (h : C ∘ₗ f = g ∘ₗ C)
    (n : ℕ) (x : V) :
    C (capRowSign (k := k) n • V.sgn ((n + 1 : ℕ) : ZMod 2) ((f ^ n) x)) =
      capRowSign (k := k) n • W.sgn ((n + 1 : ℕ) : ZMod 2) ((g ^ n) (C x)) := by
  rw [map_smul]
  have hs := LinearMap.congr_fun (intertwine_sgn V W C hC ((n + 1 : ℕ) : ZMod 2)) ((f ^ n) x)
  exact congrArg (fun y => capRowSign (k := k) n • y)
    (hs.trans (congrArg (W.sgn ((n + 1 : ℕ) : ZMod 2))
      (intertwine_pow_apply C f g (fun x => LinearMap.congr_fun h x) n x)))

end Parity
end OddMath.QuiverHecke.ELVOld
