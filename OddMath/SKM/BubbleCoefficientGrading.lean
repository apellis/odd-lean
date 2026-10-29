/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleELVSpecialization
import OddMath.SKM.Grading
import OddMath.SKM.BubbleParity
import Mathlib.Algebra.DirectSum.Decomposition

/-! # Symmetrizer degrees of the polynomial/exterior coefficients

`DeformedGradedAction.md` §1 and Brundan–Ellis (1.31): the integer
grade of abstract SYM, independent of its super parity. The weight ideal
is homogeneous, and finite colour support bounds degree by a multiple of
coefficient weight. No positive-content action or finiteness is asserted.
-/

noncomputable section
open scoped Classical TensorProduct
namespace OddMath.SKM.SYM
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k] (sy : Symmetrizer D)

/-- Integer degree, distinct from coefficient weight and super parity. -/
def coefficientDegree (a : CoefficientIndex D) : ℤ :=
  a.1.sum (fun i n => (n : ℤ) * (2 * sy.d i.1 * elementaryWeight D i)) +
    ∑ i ∈ a.2, 2 * sy.d i.1

theorem coefficientDegree_mul {a b : CoefficientIndex D} (h : Disjoint a.2 b.2) :
    coefficientDegree D sy (a.1 + b.1, a.2 ∪ b.2) =
      coefficientDegree D sy a + coefficientDegree D sy b := by
  have hp : (a.1 + b.1).sum (fun i n => (n : ℤ) * (2 * sy.d i.1 * elementaryWeight D i)) =
      a.1.sum (fun i n => (n : ℤ) * (2 * sy.d i.1 * elementaryWeight D i)) +
      b.1.sum (fun i n => (n : ℤ) * (2 * sy.d i.1 * elementaryWeight D i)) :=
    Finsupp.sum_add_index (by intro i; simp) (by intros; simp [add_mul])
  simp only [coefficientDegree, hp, Finset.sum_union h]
  ring

def coefficientDegreePart (n : ℤ) : Submodule k (SYM D k) :=
  Submodule.span k (coefficientBasis D k '' {a | coefficientDegree D sy a = n})

theorem coefficientDegreePart_internal : DirectSum.IsInternal (coefficientDegreePart D k sy) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · intro n
    rw [coefficientDegreePart]
    simp only [coefficientDegreePart, ← Submodule.span_iUnion, ← Set.image_iUnion]
    apply (coefficientBasis D k).linearIndependent.disjoint_span_image
    rw [Set.disjoint_left]
    intro a ha hb
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at ha hb
    obtain ⟨m, hm, ham⟩ := hb
    exact hm (ham.symm.trans ha)
  · change (⨆ n : ℤ, coefficientDegreePart D k sy n) = ⊤
    simp only [coefficientDegreePart, ← Submodule.span_iUnion, ← Set.image_iUnion]
    have h : (⋃ n : ℤ, {a : CoefficientIndex D | coefficientDegree D sy a = n}) = Set.univ := by
      ext a
      simp
    rw [h, Set.image_univ, (coefficientBasis D k).span_eq]

theorem coefficientDegreePart_mul {m n : ℤ} {x y : SYM D k}
    (hx : x ∈ coefficientDegreePart D k sy m) (hy : y ∈ coefficientDegreePart D k sy n) :
    x * y ∈ coefficientDegreePart D k sy (m + n) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      by_cases h : Disjoint a.2 b.2
      · obtain ⟨c, hc⟩ := coefficientBasis_mul_scalar D k h
        rw [hc]
        apply Submodule.smul_mem
        exact Submodule.subset_span ⟨_, (coefficientDegree_mul D sy h).trans (congrArg₂ (· + ·) ha hb), rfl⟩
      · rw [coefficientBasis_mul_zero D k h]
        exact Submodule.zero_mem _
    | zero => simp
    | add y z _ _ hy hz => simpa only [mul_add] using Submodule.add_mem _ hy hz
    | smul c y _ hy => simpa only [mul_smul_comm] using Submodule.smul_mem _ c hy
  | zero => simp
  | add x z _ _ hx hz => simpa only [add_mul] using Submodule.add_mem _ hx hz
  | smul c x _ hx => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c hx

instance coefficientDegreeGradedAlgebra : GradedAlgebra (coefficientDegreePart D k sy) :=
  { (coefficientDegreePart_internal D k sy).chooseDecomposition with
    one_mem := by
      apply Submodule.subset_span
      refine ⟨(0, ∅), by simp [coefficientDegree], ?_⟩
      apply (polynomialExteriorEquiv D k).injective
      rw [map_one (polynomialExteriorEquiv D k), coefficientBasis_projection, oddExteriorBasis_empty]
      exact (Algebra.TensorProduct.one_def : (1 : PolynomialExterior D k) = 1 ⊗ₜ[k] 1).symm
    mul_mem := fun _ _ _ _ hx hy => coefficientDegreePart_mul D k sy hx hy }

theorem delta_mem_coefficientDegreePart (i : {i : I // D.parity i = 1}) :
    delta D k i ∈ coefficientDegreePart D k sy (2 * sy.d i.1) := by
  apply Submodule.subset_span
  exact ⟨(0, {i}), by simp [coefficientDegree], coefficientBasis_delta D k i⟩

theorem elementary_mem_coefficientDegreePart (i : I) (r : ℕ) :
    e D k i r ∈ coefficientDegreePart D k sy (2 * sy.d i * elementaryWeight D (i, r)) := by
  apply Submodule.subset_span
  exact ⟨(Finsupp.single (i, r) 1, ∅), by simp [coefficientDegree],
    coefficientBasis_elementary D k i r⟩

theorem coefficientDegree_nonneg (a : CoefficientIndex D) : 0 ≤ coefficientDegree D sy a := by
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by linarith [sy.pos i.1]) (Nat.cast_nonneg _))
  · apply Finset.sum_nonneg
    intro i _
    linarith [sy.pos i.1]

/-- A bound on the finitely many dot degrees bounds the degree/weight ratio,
including exterior factors. No identification of weight and degree is made. -/
theorem coefficientDegree_le_weight_mul (M : ℤ) (hM : ∀ i, 2 * sy.d i ≤ M)
    (a : CoefficientIndex D) : coefficientDegree D sy a ≤ M * coefficientWeight D a := by
  unfold coefficientDegree coefficientWeight
  push_cast
  rw [mul_add, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right (hM i.1) (Nat.cast_nonneg (elementaryWeight D i) : (0 : ℤ) ≤ _)
    have h' := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (a.1 i) : (0 : ℤ) ≤ _)
    nlinarith only [h']
  · calc
      ∑ i ∈ a.2, 2 * sy.d i.1 ≤ ∑ _i ∈ a.2, M := Finset.sum_le_sum fun i _ => hM i.1
      _ = M * (a.2.card : ℤ) := by simp [mul_comm]

/-- Finite colour support supplies a uniform bound; it is not an extra hypothesis. -/
theorem exists_coefficientDegree_bound [Finite I] :
    ∃ M : ℤ, 0 ≤ M ∧ ∀ a : CoefficientIndex D,
      coefficientDegree D sy a ≤ M * coefficientWeight D a := by
  let := Fintype.ofFinite I
  let M : ℕ := Finset.univ.sup (fun i => (2 * sy.d i).toNat)
  refine ⟨M, Nat.cast_nonneg _, coefficientDegree_le_weight_mul D sy M ?_⟩
  intro i
  have hi : (2 * sy.d i).toNat ≤ M := Finset.le_sup (f := fun i => (2 * sy.d i).toNat) (Finset.mem_univ i)
  have hi' : ((2 * sy.d i).toNat : ℤ) ≤ M := by exact_mod_cast hi
  omega

theorem coefficientIdeal_degree (N : ℕ) {x : SYM D k}
    (hx : x ∈ coefficientIdeal D k N) (n : ℤ) :
    GradedAlgebra.proj (coefficientDegreePart D k sy) n x ∈ coefficientIdeal D k N := by
  rw [mem_coefficientIdeal_iff] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    have hm : coefficientBasis D k a ∈ coefficientDegreePart D k sy (coefficientDegree D sy a) :=
      Submodule.subset_span ⟨a, rfl, rfl⟩
    rw [GradedAlgebra.proj_apply]
    by_cases h : coefficientDegree D sy a = n
    · subst n
      rw [DirectSum.decompose_of_mem_same _ hm]
      exact Submodule.subset_span ⟨a, ha, rfl⟩
    · rw [DirectSum.decompose_of_mem_ne _ hm h]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

theorem elvCoefficientRelation_degree {cutoff : I → ℕ} {x : SYM D k}
    (hx : ELVCoefficientRelation D k cutoff x) :
    ∃ n, x ∈ coefficientDegreePart D k sy n := by
  rcases hx with ⟨i, r, _, rfl⟩ | ⟨i, _, rfl⟩
  · exact ⟨_, elementary_mem_coefficientDegreePart D k sy i r⟩
  · cases h : cutoff i.1 / 2 with
    | zero => simpa [elvChi, h] using ⟨_, delta_mem_coefficientDegreePart D k sy i⟩
    | succ r =>
      exact ⟨_, coefficientDegreePart_mul D k sy (delta_mem_coefficientDegreePart D k sy i)
        (by simpa [elvChi, h] using elementary_mem_coefficientDegreePart D k sy i.1 r)⟩

private theorem iotaMulti_parity (n : ℕ) (v : Fin n → OddModule D k) :
    ExteriorAlgebra.ιMulti k n v ∈ exteriorParity D k (n : ZMod 2) := by
  induction n with
  | zero => simpa using (SetLike.GradedOne.one_mem : (1 : ExteriorAlgebra k (OddModule D k)) ∈ exteriorParity D k 0)
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    have hv : ExteriorAlgebra.ι k (v 0) ∈ exteriorParity D k 1 :=
      CliffordAlgebra.ι_mem_evenOdd_one (0 : QuadraticForm k (OddModule D k)) (v 0)
    have hh := SetLike.mul_mem_graded hv (ih (Matrix.vecTail v))
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hh

theorem coefficientBasis_mem_parity (a : CoefficientIndex D) :
    polynomialExteriorEquiv D k (coefficientBasis D k a) ∈ polynomialExteriorParity D k (a.2.card : ZMod 2) := by
  rw [coefficientBasis_projection]
  apply Submodule.tmul_mem_baseChange_of_mem
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  let b : Module.Basis _ k (OddModule D k) := Finsupp.basisSingleOne
  change b.ExteriorAlgebra a.2 ∈ exteriorParity D k _
  rw [ExteriorAlgebra.basis_apply_ofCard b (rfl : a.2.card = a.2.card)]
  unfold ExteriorAlgebra.ιMulti_family
  exact iotaMulti_parity D k _ _

theorem coefficientIdeal_parity (N : ℕ) {x : PolynomialExterior D k}
    (hx : (polynomialExteriorEquiv D k).symm x ∈ coefficientIdeal D k N) (p : ZMod 2) :
    (polynomialExteriorEquiv D k).symm (GradedAlgebra.proj (polynomialExteriorParity D k) p x) ∈
      coefficientIdeal D k N := by
  let P : SYM D k →ₗ[k] SYM D k :=
    (polynomialExteriorEquiv D k).symm.toLinearMap.comp
      ((GradedAlgebra.proj (polynomialExteriorParity D k) p).comp
        (polynomialExteriorEquiv D k).toLinearMap)
  have hP : ∀ a ∈ CoefficientAtLeast D k N, P a ∈ CoefficientAtLeast D k N := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨b, hb, rfl⟩ := ha
      change (polynomialExteriorEquiv D k).symm
        (GradedAlgebra.proj (polynomialExteriorParity D k) p
          (polynomialExteriorEquiv D k (coefficientBasis D k b))) ∈ _
      rw [GradedAlgebra.proj_apply]
      by_cases h : (b.2.card : ZMod 2) = p
      · subst p
        rw [DirectSum.decompose_of_mem_same _ (coefficientBasis_mem_parity D k b),
          AlgEquiv.symm_apply_apply]
        exact Submodule.subset_span ⟨b, hb, rfl⟩
      · rw [DirectSum.decompose_of_mem_ne _ (coefficientBasis_mem_parity D k b) h, map_zero]
        exact Submodule.zero_mem _
    | zero => simpa only [map_zero] using (Submodule.zero_mem (CoefficientAtLeast D k N))
    | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha
  rw [mem_coefficientIdeal_iff] at hx ⊢
  simpa only [P, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply]
    using hP _ hx

end OddMath.SKM.SYM
