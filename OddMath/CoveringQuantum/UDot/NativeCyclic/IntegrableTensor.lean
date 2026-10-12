import OddMath.CoveringQuantum.UDot.NativeCyclic.TensorSupport
import OddMath.CoveringQuantum.UDot.NativeCyclic.IntegrableFinite

/-! Finite-span injectivity for tensors of the original integrable quotient maps. -/

noncomputable section
open TensorProduct
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent)

/-- The tensor of the original integrability-relation quotient maps. This is
not the weight projection endomorphism called `tensorProject`. -/
def toIntegrableTensor (Λ Μ : X) :
    (D.serreF Coefficients.q pi) ⊗[Coefficients.Ring]
      (D.serreF Coefficients.q pi) →ₗ[Coefficients.Ring]
    (IntegrableQuotient D hD Λ) ⊗[Coefficients.Ring] (IntegrableQuotient D hD Μ) :=
  TensorProduct.map (toIntegrable D hD Λ) (toIntegrable D hD Μ)

@[simp] theorem toIntegrableTensor_tmul (Λ Μ : X) (x y : D.serreF Coefficients.q pi) :
    toIntegrableTensor D hD Λ Μ (x ⊗ₜ[Coefficients.Ring] y) =
      toIntegrable D hD Λ x ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ y := rfl

/-- Any finite set of actual tensors, including arbitrary finite sums, has one
bound for injectivity on its ENTIRE covering-ring span. No flatness, freeness,
root independence, or tensor faithfulness is a hypothesis. -/
theorem finite_span_toIntegrableTensor_injective_bound
    (s : Finset ((D.serreF Coefficients.q pi) ⊗[Coefficients.Ring]
      (D.serreF Coefficients.q pi))) :
    ∃ B : ℤ, 0 ≤ B ∧ ∀ Λ Μ : X, (∀ i, B ≤ D.h i Λ) → (∀ i, B ≤ D.h i Μ) →
      Set.InjOn (toIntegrableTensor D hD Λ Μ) (Submodule.span Coefficients.Ring
        (s : Set ((D.serreF Coefficients.q pi) ⊗[Coefficients.Ring]
          (D.serreF Coefficients.q pi)))) := by
  obtain ⟨S, T, hS, hT, hst⟩ := TensorProduct.exists_finite_submodule_of_setFinite
    (R := Coefficients.Ring) (s : Set ((D.serreF Coefficients.q pi) ⊗[Coefficients.Ring]
      (D.serreF Coefficients.q pi))) s.finite_toSet
  let := hS
  let := hT
  obtain ⟨B, hB, hb⟩ := exists_toIntegrable_injective_bound D hD S
  obtain ⟨C, hC, hc⟩ := exists_toIntegrable_injective_bound D hD T
  refine ⟨max B C, hB.trans (le_max_left _ _), fun Λ Μ hΛ hΜ => ?_⟩
  have hinj := covering_tensor_injOn_range S T (toIntegrable D hD Λ)
    (toIntegrable D hD Μ) (hb Λ (fun i => (le_max_left _ _).trans (hΛ i)))
    (hc Μ (fun i => (le_max_right _ _).trans (hΜ i)))
  exact hinj.mono (Submodule.span_le.mpr hst)

/-- Equivalent formulation for any finitely generated submodule of the actual tensor. -/
theorem fg_toIntegrableTensor_injective_bound
    (U : Submodule Coefficients.Ring ((D.serreF Coefficients.q pi) ⊗[Coefficients.Ring]
      (D.serreF Coefficients.q pi))) (hU : U.FG) :
    ∃ B : ℤ, 0 ≤ B ∧ ∀ Λ Μ : X, (∀ i, B ≤ D.h i Λ) → (∀ i, B ≤ D.h i Μ) →
      Set.InjOn (toIntegrableTensor D hD Λ Μ) U := by
  obtain ⟨s, rfl⟩ := hU
  exact finite_span_toIntegrableTensor_injective_bound D hD s

/-- A positive coroot direction makes the fixed-difference tensor family
nonvacuous, with both weights dominant and whole-span injectivity. -/
theorem finite_span_toIntegrableTensor_fixed_difference
    (s : Finset ((D.serreF Coefficients.q pi) ⊗[Coefficients.Ring]
      (D.serreF Coefficients.q pi))) (ζ ξ : X) (hξ : ∀ i, 0 < D.h i ξ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ i, 0 ≤ D.h i (ζ + n • ξ)) ∧ (∀ i, 0 ≤ D.h i (n • ξ)) ∧
      (ζ + n • ξ) - n • ξ = ζ ∧
      Set.InjOn (toIntegrableTensor D hD (ζ + n • ξ) (n • ξ))
        (Submodule.span Coefficients.Ring
        (s : Set ((D.serreF Coefficients.q pi) ⊗[Coefficients.Ring]
          (D.serreF Coefficients.q pi)))) := by
  classical
  let := Fintype.ofFinite I
  obtain ⟨B, hB, hb⟩ := finite_span_toIntegrableTensor_injective_bound D hD s
  let M : ℤ := B + ∑ i : I, |B - D.h i ζ|
  have hBM : B ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => abs_nonneg _))
  refine ⟨M.toNat, fun n hn => ?_⟩
  have hmn : M ≤ (n : ℤ) := by omega
  have hΛ (i) : B ≤ D.h i (ζ + n • ξ) := by
    have hi : B - D.h i ζ ≤ M := (le_abs_self _).trans
      ((Finset.single_le_sum (fun j _ => abs_nonneg (B - D.h j ζ)) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left hB))
    have hp := hξ i
    simp only [map_add, map_nsmul, nsmul_eq_mul]
    nlinarith
  have hΜ (i) : B ≤ D.h i (n • ξ) := by
    have hp := hξ i
    simp only [map_nsmul, nsmul_eq_mul]
    nlinarith
  exact ⟨fun i => hB.trans (hΛ i), fun i => hB.trans (hΜ i),
    add_sub_cancel_right _ _, hb _ _ hΛ hΜ⟩

/-- Every actual nonzero unquotiented tensor survives all sufficiently large
members of each positive fixed-difference family. No assertion that a pure
tensor of two nonzero factors is nonzero is used. -/
theorem nonzero_toIntegrableTensor_fixed_difference
    (z : (D.serreF Coefficients.q pi) ⊗[Coefficients.Ring] (D.serreF Coefficients.q pi))
    (hz : z ≠ 0) (ζ ξ : X) (hξ : ∀ i, 0 < D.h i ξ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ i, 0 ≤ D.h i (ζ + n • ξ)) ∧ (∀ i, 0 ≤ D.h i (n • ξ)) ∧
      toIntegrableTensor D hD (ζ + n • ξ) (n • ξ) z ≠ 0 := by
  classical
  obtain ⟨N, hN⟩ := finite_span_toIntegrableTensor_fixed_difference D hD {z} ζ ξ hξ
  refine ⟨N, fun n hn => ?_⟩
  have hh := hN n hn
  refine ⟨hh.1, hh.2.1, fun hzero => hz (hh.2.2.2 ?_ (Submodule.zero_mem _) ?_)⟩
  · exact Submodule.subset_span (Finset.mem_singleton_self z)
  · simpa only [map_zero] using hzero

/-- Joint separation of unquotiented half-tensors by the actual quotient-tensor
maps along a positive fixed-difference sequence. This is not action separation. -/
theorem toIntegrableTensor_fixed_difference_separating
    (ζ ξ : X) (hξ : ∀ i, 0 < D.h i ξ)
    (x y : (D.serreF Coefficients.q pi) ⊗[Coefficients.Ring] (D.serreF Coefficients.q pi))
    (hxy : ∀ n : ℕ, (∀ i, 0 ≤ D.h i (ζ + n • ξ)) → (∀ i, 0 ≤ D.h i (n • ξ)) →
      toIntegrableTensor D hD (ζ + n • ξ) (n • ξ) x =
        toIntegrableTensor D hD (ζ + n • ξ) (n • ξ) y) : x = y := by
  classical
  obtain ⟨N, hN⟩ := finite_span_toIntegrableTensor_fixed_difference D hD {x, y} ζ ξ hξ
  have hh := hN N le_rfl
  apply hh.2.2.2 _ _ (hxy N hh.1 hh.2.1)
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)

end OddMath.CoveringQuantum.UDot.GenericVerma
