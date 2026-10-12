import OddMath.CoveringQuantum.UDot.NativeCyclic.FiniteDetection
import OddMath.CoveringQuantum.Nondegenerate
import OddMath.CoveringQuantum.UDot.VermaLimit
import OddMath.CoveringQuantum.UDot.IntegrablePolarization
import Mathlib.Algebra.Algebra.RestrictScalars

/-! Uniform injectivity of integrable quotients on finite covering-ring spans. -/

noncomputable section
open Filter Module
open scoped Topology
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent)

local instance halfScalarModule : Module (RatFunc ℚ) (D.serreF Coefficients.q pi) :=
  Module.restrictScalars (RatFunc ℚ) Coefficients.Ring _
local instance halfScalarTower : IsScalarTower (RatFunc ℚ) Coefficients.Ring
    (D.serreF Coefficients.q pi) := IsScalarTower.restrictScalars _ _ _

-- Scalar restriction uses the canonical quotient actions.
attribute [-instance] halfScalarModule halfScalarTower

/-- A scalar-field probe, retaining its actual covering-half input and pi factor. -/
def halfProbe (S : Submodule Coefficients.Ring (D.serreF Coefficients.q pi))
    (t : PreF Coefficients.Ring I × {ε : RatFunc ℚ // ε ^ 2 = 1}) : S →ₗ[RatFunc ℚ] RatFunc ℚ :=
  (specialize t.2.1 t.2.2).toLinearMap.comp
    (((D.serreForm Coefficients.q pi pi_sq) (D.toSerreF Coefficients.q pi t.1)).restrictScalars
      (RatFunc ℚ) |>.comp (S.subtype.restrictScalars (RatFunc ℚ)))

/-- Only the first argument is twisted; the second is the original quotient input. -/
def vermaProbe (S : Submodule Coefficients.Ring (D.serreF Coefficients.q pi)) (Λ : X)
    (t : PreF Coefficients.Ring I × {ε : RatFunc ℚ // ε ^ 2 = 1}) : S →ₗ[RatFunc ℚ] RatFunc ℚ :=
  (specialize t.2.1 t.2.2).toLinearMap.comp
    (((polarization D hD Λ)
      (D.toSerreF Coefficients.q pi (diagTwist (polarizationSign D Λ) t.1))).restrictScalars
      (RatFunc ℚ) |>.comp (S.subtype.restrictScalars (RatFunc ℚ)))

include hD in
omit [DecidableEq X] in
theorem halfProbe_separating (S : Submodule Coefficients.Ring (D.serreF Coefficients.q pi))
    (v : S) (hv : ∀ t, halfProbe D S t v = 0) : v = 0 := by
  apply Subtype.ext
  apply (Coefficients.serreForm_nondegenerate D.toSuperCartanDatum hD).2
  intro x
  obtain ⟨w, rfl⟩ := D.toSuperCartanDatum.toSerreF_surjective Coefficients.q pi x
  apply (eq_iff_specialize_eq _ 0).mpr
  exact ⟨by simpa [halfProbe] using hv (w, ⟨1, one_pow 2⟩),
    by simpa [halfProbe] using hv (w, ⟨-1, by norm_num⟩)⟩

theorem vermaProbe_tendsto (S : Submodule Coefficients.Ring (D.serreF Coefficients.q pi))
    (t : PreF Coefficients.Ring I × {ε : RatFunc ℚ // ε ^ 2 = 1}) (v : S) :
    Tendsto (fun Λ => vermaProbe D hD S Λ t v) (coordinateFilter D) (𝓝 (halfProbe D S t v)) := by
  obtain ⟨y, hy⟩ := D.toSuperCartanDatum.toSerreF_surjective Coefficients.q pi
    (v : D.serreF Coefficients.q pi)
  have hh := normalizedPolarization_tendsto D hD t.2.1 t.2.2 t.1 y
  change Tendsto (fun Λ => specialize t.2.1 t.2.2 (polarization D hD Λ
    (D.toSerreF Coefficients.q pi (diagTwist (polarizationSign D Λ) t.1))
    (v : D.serreF Coefficients.q pi))) (coordinateFilter D)
    (𝓝 (specialize t.2.1 t.2.2 (D.serreForm Coefficients.q pi pi_sq
      (D.toSerreF Coefficients.q pi t.1) (v : D.serreF Coefficients.q pi))))
  rw [← hy, SuperCartanDatum.serreForm_toSerreF]
  exact hh

/-- A finite covering submodule is eventually faithfully projected into the
original integrable quotient. No freeness over the split covering ring is assumed. -/
theorem eventually_toIntegrable_injective (S : Submodule Coefficients.Ring
    (D.serreF Coefficients.q pi)) [Module.Finite Coefficients.Ring S] :
    ∀ᶠ Λ in coordinateFilter D, Function.Injective ((toIntegrable D hD Λ).comp S.subtype) := by
  let : Module.Finite (RatFunc ℚ) Coefficients.Ring :=
    Module.Finite.equiv Coefficients.splitEquiv.symm.toLinearEquiv
  let : Module.Finite (RatFunc ℚ) S := Module.Finite.trans Coefficients.Ring S
  have hh := FiniteDetection.eventually_separating (K := RatFunc ℚ) (V := S)
    (coordinateFilter D) (halfProbe D S)
    (vermaProbe D hD S) (halfProbe_separating D hD S) (vermaProbe_tendsto D hD S)
  filter_upwards [hh, eventually_coordinate_lower D 0] with Λ hsep hΛ
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply hsep v
  intro t
  change specialize t.2.1 t.2.2 (polarization D hD Λ _ (v : D.serreF Coefficients.q pi)) = 0
  rw [← integrablePolarization_toIntegrable D hD Λ hΛ, show toIntegrable D hD Λ
    (v : D.serreF Coefficients.q pi) = 0 from hv, map_zero, map_zero]

/-- One common nonnegative coroot bound works for every vector of the fixed
finite covering submodule, not just each vector separately. -/
theorem exists_toIntegrable_injective_bound (S : Submodule Coefficients.Ring
    (D.serreF Coefficients.q pi)) [Module.Finite Coefficients.Ring S] :
    ∃ B : ℤ, 0 ≤ B ∧ ∀ Λ : X, (∀ i, B ≤ D.h i Λ) →
      Function.Injective ((toIntegrable D hD Λ).comp S.subtype) := by
  classical
  let := Fintype.ofFinite I
  have he := eventually_toIntegrable_injective D hD S
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp (Filter.eventually_comap.mp he)
  let B : ℤ := ∑ i : I, |b i|
  refine ⟨B, Finset.sum_nonneg (fun i _ => abs_nonneg (b i)), ?_⟩
  intro Λ hΛ
  apply hb (fun i => D.h i Λ) _ Λ rfl
  intro i
  exact (le_abs_self (b i)).trans ((Finset.single_le_sum
    (fun j _ => abs_nonneg (b j)) (Finset.mem_univ i)).trans (hΛ i))

/-- Actual arbitrary finite input spans over the covering ring, including
zero-divisor coefficients and nonfree submodules. -/
theorem finite_span_toIntegrable_injective_bound
    (s : Finset (D.serreF Coefficients.q pi)) :
    ∃ B : ℤ, 0 ≤ B ∧ ∀ Λ : X, (∀ i, B ≤ D.h i Λ) →
      Set.InjOn (toIntegrable D hD Λ)
        (Submodule.span Coefficients.Ring (s : Set (D.serreF Coefficients.q pi))) := by
  let S := Submodule.span Coefficients.Ring (s : Set (D.serreF Coefficients.q pi))
  obtain ⟨B, hB, hh⟩ := exists_toIntegrable_injective_bound D hD S
  refine ⟨B, hB, fun Λ hΛ x hx y hy hxy => ?_⟩
  exact congrArg Subtype.val (hh Λ hΛ (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)

/-- Nonvacuous cofinal family: positivity is an explicit hypothesis on ξ.
Every sufficiently large member is dominant and faithful on the entire span. -/
theorem finite_span_toIntegrable_injective_sequence
    (s : Finset (D.serreF Coefficients.q pi)) (Λ₀ ξ : X) (hξ : ∀ i, 0 < D.h i ξ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ i, 0 ≤ D.h i (Λ₀ + n • ξ)) ∧
      Set.InjOn (toIntegrable D hD (Λ₀ + n • ξ))
        (Submodule.span Coefficients.Ring (s : Set (D.serreF Coefficients.q pi))) := by
  classical
  let := Fintype.ofFinite I
  obtain ⟨B, hB, hh⟩ := finite_span_toIntegrable_injective_bound D hD s
  let M : ℤ := ∑ i : I, |B - D.h i Λ₀|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨M.toNat, fun n hn => ?_⟩
  have hb (i) : B ≤ D.h i (Λ₀ + n • ξ) := by
    have hi : B - D.h i Λ₀ ≤ M := (le_abs_self _).trans
      (Finset.single_le_sum (fun j _ => abs_nonneg (B - D.h j Λ₀)) (Finset.mem_univ i))
    have hmn : M ≤ (n : ℤ) := by omega
    have hp := hξ i
    simp only [map_add, map_nsmul, nsmul_eq_mul]
    nlinarith
  exact ⟨fun i => hB.trans (hb i), hh _ hb⟩

/-- Two arbitrary finite covering spans are simultaneously faithful along
weights with any fixed difference. This is not yet tensor faithfulness. -/
theorem finite_spans_toIntegrable_fixed_difference
    (s t : Finset (D.serreF Coefficients.q pi)) (ζ ξ : X) (hξ : ∀ i, 0 < D.h i ξ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ i, 0 ≤ D.h i (ζ + n • ξ)) ∧ (∀ i, 0 ≤ D.h i (n • ξ)) ∧
      Set.InjOn (toIntegrable D hD (ζ + n • ξ))
        (Submodule.span Coefficients.Ring (s : Set (D.serreF Coefficients.q pi))) ∧
      Set.InjOn (toIntegrable D hD (n • ξ))
        (Submodule.span Coefficients.Ring (t : Set (D.serreF Coefficients.q pi))) := by
  obtain ⟨N, hN⟩ := finite_span_toIntegrable_injective_sequence D hD s ζ ξ hξ
  obtain ⟨M, hM⟩ := finite_span_toIntegrable_injective_sequence D hD t 0 ξ hξ
  refine ⟨max N M, fun n hn => ?_⟩
  have h₁ := hN n ((le_max_left _ _).trans hn)
  have h₂ := hM n ((le_max_right _ _).trans hn)
  rw [zero_add] at h₂
  exact ⟨h₁.1, h₂.1, h₁.2, h₂.2⟩

end OddMath.CoveringQuantum.UDot.GenericVerma
