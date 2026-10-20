/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.NativeCyclic.CyclicInjectivity
import OddMath.CoveringQuantum.UDot.GlobalTriangular
import OddMath.CoveringQuantum.UDot.TensorGram.JointConvergence

/-!
# Native tensor-family separation on the modified algebra

Strictly positive coroot weights make the released finite-span cyclic bounds
nonvacuous along each fixed difference. Native vacuum evaluation then detects
all right coordinates of an arbitrary element of the original modified algebra.
This concerns each native coproduct separately, not the unital envelope.
-/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.NativeFamily
open Coefficients TensorProduct NativeCyclic GenericTensor NormalizedJointLimit
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent)

local instance : AddCommGroup
    (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi) :=
  TensorProduct.addCommGroup

local instance (Λ Μ : X) : AddCommGroup
    (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ) :=
  TensorProduct.addCommGroup

include hD in
/-- One eventual bound for the whole finite covering-ring span and both coproducts.
Positivity is explicit; the sequence is not assumed cofinal for arbitrary data. -/
theorem finite_span_cyclic_fixed_difference
    (S : Finset (D.serreF Coefficients.q pi ⊗[Coefficients.Ring] D.serreF Coefficients.q pi))
    (ζ ξ : X) (hξ : ∀ i, 0 < D.h i ξ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ i, 0 ≤ D.h i (ζ + n • ξ)) ∧ (∀ i, 0 ≤ D.h i (n • ξ)) ∧
      ∀ s : Bool, Set.InjOn (cyclic D (ζ + n • ξ) (n • ξ) s)
        (Submodule.span Coefficients.Ring
          (S : Set (D.serreF Coefficients.q pi ⊗[Coefficients.Ring]
            D.serreF Coefficients.q pi))) := by
  obtain ⟨B, hB, hinj⟩ := finite_span_cyclic_injective_bound D hD S
  have he := (cofinalPair_tendsto D ζ ξ hξ).eventually
    (jointFilter_eventually_lower D ζ B)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  change (∀ i, B ≤ D.h i (ζ + n • ξ)) ∧ (∀ i, B ≤ D.h i (n • ξ)) at hb
  exact ⟨fun i => hB.trans (hb.1 i), fun i => hB.trans (hb.2 i),
    hinj _ _ hb.1 hb.2⟩

omit [Finite I] in
/-- The actual native action on the vacuum is the cyclic image of the right
coordinate. The regular representation is used only to reconstruct coordinates. -/
theorem cyclic_coordinate_eq_native_vacuum (Λ Μ : X) (s : Bool)
    (x : modified D Coefficients.q pi) :
    cyclic D Λ Μ s (triangularCoordinates D x (Λ - Μ)) =
      tensorModifiedRepresentation D Λ Μ s x
        (toIntegrable D Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D Μ 1) := by
  change tensorRepresentation D Λ Μ s
    (triangularTensor D Coefficients.q pi (Λ - Μ) (triangularCoordinates D x (Λ - Μ)))
      (PolarizationTransport.vac D Λ Μ) = _
  rw [triangularTensor_coordinates, map_mul, Module.End.mul_apply,
    tensorRepresentation_one, PolarizationTransport.project_vac]
  rfl

omit [Finite I] in
/-- Explicit normalization of the right weight for the concrete cofinal family. -/
theorem cyclic_coordinate_fixed_difference (ζ ξ : X) (n : ℕ) (s : Bool)
    (x : modified D Coefficients.q pi) :
    cyclic D (ζ + n • ξ) (n • ξ) s (triangularCoordinates D x ζ) =
      tensorModifiedRepresentation D (ζ + n • ξ) (n • ξ) s x
        (toIntegrable D (ζ + n • ξ) 1 ⊗ₜ[Coefficients.Ring]
          toIntegrable D (n • ξ) 1) := by
  simpa only [add_sub_cancel_right] using
    cyclic_coordinate_eq_native_vacuum D (ζ + n • ξ) (n • ξ) s x

include hD

/-- Kernel zero for each native coproduct along actual dominant members of the
fixed-difference families. The input is an arbitrary original modified element. -/
theorem cofinal_kernel_zero (ξ : X) (hξ : ∀ i, 0 < D.h i ξ) (s : Bool)
    (x : modified D Coefficients.q pi)
    (hx : ∀ (ζ : X) (n : ℕ), (∀ i, 0 ≤ D.h i (ζ + n • ξ)) →
      (∀ i, 0 ≤ D.h i (n • ξ)) →
      tensorModifiedRepresentation D (ζ + n • ξ) (n • ξ) s x = 0) : x = 0 := by
  classical
  have hc : triangularCoordinates D x = 0 := by
    ext ζ
    let z := triangularCoordinates D x ζ
    obtain ⟨N, hN⟩ := finite_span_cyclic_fixed_difference D hD {z} ζ ξ hξ
    obtain ⟨hΛ, hΜ, hinj⟩ := hN N le_rfl
    have hzero : cyclic D (ζ + N • ξ) (N • ξ) s z = 0 := by
      rw [cyclic_coordinate_fixed_difference, hx ζ N hΛ hΜ]
      rfl
    have heq := hinj s (x₁ := z) (x₂ := 0)
      (by
        change z ∈ Submodule.span Coefficients.Ring
          (({z} : Finset _) : Set _)
        exact Submodule.subset_span (Finset.mem_singleton_self z))
      (Submodule.zero_mem _) (hzero.trans (map_zero _).symm)
    exact heq
  rw [← globalTriangular_triangularCoordinates D x, hc, map_zero]

/-- Equality is tested by actual endomorphisms at dominant sequence members,
with the native coproduct fixed before comparing arbitrary modified elements. -/
theorem cofinal_eq_iff (ξ : X) (hξ : ∀ i, 0 < D.h i ξ) (s : Bool)
    (x y : modified D Coefficients.q pi) :
    x = y ↔ ∀ (ζ : X) (n : ℕ), (∀ i, 0 ≤ D.h i (ζ + n • ξ)) →
      (∀ i, 0 ≤ D.h i (n • ξ)) →
      tensorModifiedRepresentation D (ζ + n • ξ) (n • ξ) s x =
        tensorModifiedRepresentation D (ζ + n • ξ) (n • ξ) s y := by
  constructor
  · rintro rfl ζ n hΛ hΜ
    rfl
  · intro h
    apply sub_eq_zero.mp
    apply cofinal_kernel_zero D hD ξ hξ s (x - y)
    intro ζ n hΛ hΜ
    change tensorRepresentation D (ζ + n • ξ) (n • ξ) s
      ((x : CoveringUDot Coefficients.Ring D Coefficients.q pi) -
        (y : CoveringUDot Coefficients.Ring D Coefficients.q pi)) = 0
    rw [map_sub]
    change tensorModifiedRepresentation D (ζ + n • ξ) (n • ξ) s x -
      tensorModifiedRepresentation D (ζ + n • ξ) (n • ξ) s y = 0
    rw [h ζ n hΛ hΜ, sub_self]

/-- All dominant native tensor representations jointly separate the actual
modified algebra, separately for either native coproduct, over the covering ring. -/
theorem dominant_eq_iff (ξ : X) (hξ : ∀ i, 0 < D.h i ξ) (s : Bool)
    (x y : modified D Coefficients.q pi) :
    x = y ↔ ∀ Λ Μ : X, (∀ i, 0 ≤ D.h i Λ) → (∀ i, 0 ≤ D.h i Μ) →
      tensorModifiedRepresentation D Λ Μ s x =
        tensorModifiedRepresentation D Λ Μ s y := by
  constructor
  · rintro rfl Λ Μ hΛ hΜ
    rfl
  · intro h
    exact (cofinal_eq_iff D hD ξ hξ s x y).mpr (fun ζ n => h (ζ + n • ξ) (n • ξ))

/-- The equivalent all-dominant-pairs kernel-zero criterion. -/
theorem dominant_kernel_iff (ξ : X) (hξ : ∀ i, 0 < D.h i ξ) (s : Bool)
    (x : modified D Coefficients.q pi) :
    x = 0 ↔ ∀ Λ Μ : X, (∀ i, 0 ≤ D.h i Λ) → (∀ i, 0 ≤ D.h i Μ) →
      tensorModifiedRepresentation D Λ Μ s x = 0 := by
  simpa only [map_zero] using dominant_eq_iff D hD ξ hξ s x 0

/-- The dependent family of genuine endomorphisms is an injective map. -/
theorem dominant_jointly_injective (ξ : X) (hξ : ∀ i, 0 < D.h i ξ) (s : Bool) :
    Function.Injective (fun x : modified D Coefficients.q pi =>
      fun Λ : {Λ : X // ∀ i, 0 ≤ D.h i Λ} =>
      fun Μ : {Μ : X // ∀ i, 0 ≤ D.h i Μ} =>
        tensorModifiedRepresentation D Λ.val Μ.val s x) := by
  intro x y h
  apply (dominant_eq_iff D hD ξ hξ s x y).mpr
  intro Λ Μ hΛ hΜ
  exact congrFun (congrFun h ⟨Λ, hΛ⟩) ⟨Μ, hΜ⟩

/-- Distinct original elements are separated by one actual dominant pair. -/
theorem dominant_point_separating (ξ : X) (hξ : ∀ i, 0 < D.h i ξ) (s : Bool)
    (x y : modified D Coefficients.q pi) (hxy : x ≠ y) :
    ∃ Λ Μ : X, (∀ i, 0 ≤ D.h i Λ) ∧ (∀ i, 0 ≤ D.h i Μ) ∧
      tensorModifiedRepresentation D Λ Μ s x ≠
        tensorModifiedRepresentation D Λ Μ s y := by
  classical
  by_contra h
  apply hxy
  apply (dominant_eq_iff D hD ξ hξ s x y).mpr
  simpa only [not_exists, not_and, not_not] using h

end OddMath.CoveringQuantum.UDot.GenericVerma.NativeFamily
