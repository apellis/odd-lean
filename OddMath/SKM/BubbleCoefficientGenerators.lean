/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleCoefficientBasis

/-! # Weights of the actual elementary and exterior coefficient generators -/
noncomputable section
open scoped Classical TensorProduct
namespace OddMath.SKM.SYM
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k]

@[simp] theorem oddExteriorBasis_empty : oddExteriorBasis D k ∅ = 1 := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  change (Finsupp.basisSingleOne : Module.Basis _ k (OddModule D k)).ExteriorAlgebra ∅ = 1
  rw [ExteriorAlgebra.basis_apply_ofCard _ (rfl : (∅ : Finset {i : I // D.parity i = 1}).card = 0)]
  exact ExteriorAlgebra.ιMulti_zero_apply _

@[simp] theorem oddExteriorBasis_singleton (i : {i : I // D.parity i = 1}) :
    oddExteriorBasis D k {i} = ExteriorAlgebra.ι k (Finsupp.single i 1) := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  let b : Module.Basis _ k (OddModule D k) := Finsupp.basisSingleOne
  change b.ExteriorAlgebra {i} = _
  rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_singleton i)]
  let s := Set.powersetCard.ofCard (Finset.card_singleton i)
  have hi : Set.powersetCard.ofFinEmbEquiv.symm s 0 = i := by
    have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s
      (Set.powersetCard.ofFinEmbEquiv.symm s 0)).mp ⟨0, rfl⟩
    exact Finset.mem_singleton.mp hm
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply, s, hi, b]

@[simp] theorem coefficientBasis_delta (i : {i : I // D.parity i = 1}) :
    coefficientBasis D k (0, {i}) = delta D k i := by
  apply (polynomialExteriorEquiv D k).injective
  rw [coefficientBasis_projection, oddExteriorBasis_singleton]
  change MvPolynomial.monomial 0 1 ⊗ₜ[k] ExteriorAlgebra.ι k (Finsupp.single i 1) =
    polynomialExteriorProjection D k (delta D k i)
  rw [polynomialExteriorProjection_delta]
  rfl

@[simp] theorem coefficientBasis_elementary (i : I) (r : ℕ) :
    coefficientBasis D k (Finsupp.single (i, r) 1, ∅) = e D k i r := by
  apply (polynomialExteriorEquiv D k).injective
  rw [coefficientBasis_projection, oddExteriorBasis_empty]
  change MvPolynomial.X (i, r) ⊗ₜ[k] (1 : ExteriorAlgebra k (OddModule D k)) =
    polynomialExteriorProjection D k (e D k i r)
  rw [polynomialExteriorProjection_e]

theorem elementary_mem_coefficientAtLeast (i : I) (r : ℕ) :
    e D k i r ∈ CoefficientAtLeast D k (elementaryWeight D (i, r)) := by
  apply Submodule.subset_span
  refine ⟨(Finsupp.single (i, r) 1, ∅), ?_, coefficientBasis_elementary D k i r⟩
  simp [coefficientWeight]

theorem delta_mem_coefficientAtLeast (i : {i : I // D.parity i = 1}) :
    delta D k i ∈ CoefficientAtLeast D k 1 := by
  apply Submodule.subset_span
  refine ⟨(0, {i}), ?_, coefficientBasis_delta D k i⟩
  simp [coefficientWeight]

theorem coefficientAtLeast_antitone {m n : ℕ} (h : m ≤ n) :
    CoefficientAtLeast D k n ≤ CoefficientAtLeast D k m := by
  apply Submodule.span_mono
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a, h.trans ha, rfl⟩

/-- ELV's even-cutoff coefficient relation has weight one above the cutoff.
The elementary index is zero based: `e i r` denotes `chi_(r+1)`. -/
theorem elvTopRelation_mem_coefficientAtLeast (i : {i : I // D.parity i = 1}) (r : ℕ) :
    delta D k i * e D k i.1 r ∈ CoefficientAtLeast D k (2 * (r + 1) + 1) := by
  have h := coefficientAtLeast_mul D k (delta_mem_coefficientAtLeast D k i)
    (elementary_mem_coefficientAtLeast D k i.1 r)
  simpa [elementaryWeight, i.property, Nat.add_comm] using h

end OddMath.SKM.SYM
