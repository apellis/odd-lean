import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Topology.Instances.Matrix

/-! Finite-dimensional detection by convergent separating linear probes. -/

noncomputable section
open Filter Module
open scoped Topology Matrix
namespace OddMath.CoveringQuantum.FiniteDetection

/-- A separating family of linear probes remains jointly injective on a fixed
finite-dimensional space when its values converge. The finite invertible minor
is derived, not assumed. -/
theorem eventually_separating
    {K V T A : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F : Filter A) (L : T → V →ₗ[K] K) (P : A → T → V →ₗ[K] K)
    (hsep : ∀ v, (∀ t, L t v = 0) → v = 0)
    (hlim : ∀ t v, Tendsto (fun a => P a t v) F (𝓝 (L t v))) :
    ∀ᶠ a in F, ∀ v, (∀ t, P a t v = 0) → v = 0 := by
  classical
  have hs : Submodule.span K (Set.range L) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro v hv
    obtain ⟨t, ht⟩ : ∃ t, L t v ≠ 0 := by
      by_contra! h
      exact hv (hsep v h)
    exact ⟨L t, ⟨t, rfl⟩, ht⟩
  let d := Basis.ofSpan hs.ge
  let := FiniteDimensional.fintypeBasisIndex d
  let b := d.dualBasis.map (Module.evalEquiv K V).symm
  have hd : ∀ i, ∃ t, L t = d i := fun i => Basis.ofSpan_subset hs.ge ⟨i, rfl⟩
  choose t ht using hd
  let M a : Matrix _ _ K := fun i j => P a (t i) (b j)
  have hid (i j) : L (t i) (b j) = (1 : Matrix _ _ K) i j := by
    rw [ht]
    simp [b, Matrix.one_apply, Finsupp.single_apply]
  have hm : Tendsto M F (𝓝 (1 : Matrix _ _ K)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [hid] using hlim (t i) (b j)
  have he : ∀ᶠ a in F, (M a).det ≠ 0 := by
    have hh := (continuous_id.matrix_det.tendsto (1 : Matrix _ _ K)).comp hm
    exact (show Tendsto (fun a => (M a).det) F (𝓝 1) by
      simpa only [Function.comp_def, id_eq, Matrix.det_one] using hh).eventually_ne
      one_ne_zero
  filter_upwards [he] with a ha
  intro v hv
  have hz : M a *ᵥ (fun j => b.repr v j) = 0 := by
    funext i
    have h := congrArg (P a (t i)) (b.sum_repr v)
    simpa only [map_sum, map_smul, smul_eq_mul, M, Matrix.mulVec, dotProduct,
      mul_comm, hv, Pi.zero_apply] using h
  have hc := Matrix.eq_zero_of_mulVec_eq_zero ha hz
  apply b.repr.injective
  ext j
  simpa only [map_zero, Finsupp.zero_apply, Pi.zero_apply] using congrFun hc j

end OddMath.CoveringQuantum.FiniteDetection
