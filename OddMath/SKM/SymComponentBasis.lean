/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleCoefficientBasis
import OddMath.SKM.DimensionFormula

/-!
# Monomial bases of the homogeneous components of `SYM`

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2: the coefficient algebra
`SYM` of (1.21)–(1.22) is graded by degree and parity, and the graded superdimension of `SYM`
is the factor `S` in Theorem 12.1, equation (dum). Each generator `e_{i,r}` has degree
`deg e_{i,r}` and parity `0`, each `δ_i` (`i` odd) has degree `2 d_i` and parity `1`.

The monomials of `SYM.coefficientBasis` (a polynomial monomial in the `e_{i,r}` times an
exterior monomial in the `δ_i`) are homogeneous, with bidegree `coefficientBidegree`. This file
proves that the monomials of bidegree `z` form a basis of the homogeneous component
`SYM.component sy k z` (`componentBasis`), over every commutative ring. Consequently
`dim SYM_z` is the number of monomials of bidegree `z` (`finrank_component`), and the
coefficients of the graded superdimension `S = symDimension` count monomials
(`symDimension_coeff_eq_card`). This is the coefficientwise form of the product
`S = ∏_{i even} ∏_{r ≥ 1} (1 - q_i^{2r})⁻¹ · ∏_{i odd} (1 + π q_i²) ∏_{r ≥ 1} (1 - q_i^{4r})⁻¹`
(ERRATA [BE2] 8).
-/

noncomputable section
open scoped Classical
namespace OddMath.SKM.SYM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
variable (sy : Symmetrizer D)

/-- Degree and parity of a coefficient monomial: the polynomial part contributes the degrees
of its elementary generators, each odd colour of the exterior part contributes degree
`2 d_i` and parity `1`. -/
def coefficientBidegree (η : CoefficientIndex D) : ℤ × ZMod 2 :=
  (η.1.sum (fun a n => (n : ℤ) * symGenDegree D sy (Sum.inl a)) +
      ∑ i ∈ η.2, symGenDegree D sy (Sum.inr i),
    (η.2.card : ZMod 2))

theorem coefficientBidegree_add {a b : CoefficientIndex D} (h : Disjoint a.2 b.2) :
    coefficientBidegree sy (a.1 + b.1, a.2 ∪ b.2) =
      coefficientBidegree sy a + coefficientBidegree sy b := by
  refine Prod.ext ?_ ?_
  · simp only [coefficientBidegree, Prod.fst_add]
    rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring),
      Finset.sum_union h]
    ring
  · simp only [coefficientBidegree, Prod.snd_add]
    rw [Finset.card_union_of_disjoint h, Nat.cast_add]

/-- The index of a single generator in the monomial basis. -/
def genIndex : SYMGen D → CoefficientIndex D
  | .inl a => (Finsupp.single a 1, ∅)
  | .inr i => (0, {i})

theorem coefficientBidegree_genIndex (g : SYMGen D) :
    coefficientBidegree sy (genIndex g) = (symGenDegree D sy g, symGenParity g) := by
  cases g <;> simp [genIndex, coefficientBidegree, symGenParity]

variable (k : Type w) [CommRing k]

theorem oddExteriorBasis_empty : oddExteriorBasis D k ∅ = 1 := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  change (Finsupp.basisSingleOne : Module.Basis {i : I // D.parity i = 1} k
    (OddModule D k)).ExteriorAlgebra ∅ = 1
  rw [ExteriorAlgebra.basis_apply_ofCard _ Finset.card_empty]
  simp [ExteriorAlgebra.ιMulti_family]

theorem oddExteriorBasis_singleton (i : {i : I // D.parity i = 1}) :
    oddExteriorBasis D k {i} = ExteriorAlgebra.ι k (Finsupp.single i 1) := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  change (Finsupp.basisSingleOne : Module.Basis {i : I // D.parity i = 1} k
    (OddModule D k)).ExteriorAlgebra {i} = _
  rw [ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton i)]
  have hv : ∀ j : Fin 1, (Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (Finset.card_singleton i))) j = i :=
    fun j => Finset.orderEmbOfFin_singleton i j
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply, hv]

theorem coefficientBasis_zero : coefficientBasis D k (0, ∅) = 1 := by
  apply (polynomialExteriorEquiv D k).injective
  simp only [coefficientBasis_projection, map_one, oddExteriorBasis_empty]
  rfl

/-- Each generator is a vector of the monomial basis. -/
theorem ι_eq_coefficientBasis (g : SYMGen D) : ι D k g = coefficientBasis D k (genIndex g) := by
  apply (polynomialExteriorEquiv D k).injective
  rcases g with ⟨i, n⟩ | i
  · simp only [genIndex, coefficientBasis_projection, oddExteriorBasis_empty]
    exact polynomialExteriorProjection_e D k i n
  · simp only [genIndex, coefficientBasis_projection, oddExteriorBasis_singleton]
    exact polynomialExteriorProjection_delta D k i

/-- The words in the generators span `SYM`. -/
theorem span_range_word : Submodule.span k (Set.range (word (D := D) k)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective k (SYMRel D k) x
  induction x using FreeAlgebra.induction with
  | grade0 r =>
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨[], by simp [word]⟩)
  | grade1 g => exact Submodule.subset_span ⟨[g], by simp [word, ι]⟩
  | mul a b ha hb =>
      rw [map_mul]
      have h := Submodule.mul_mem_mul ha hb
      rw [Submodule.span_mul_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨l', rfl⟩, rfl⟩
      exact ⟨l ++ l', by simp [word, List.map_append, List.prod_append]⟩
  | add a b ha hb =>
      rw [map_add]
      exact add_mem ha hb

/-- The span of the monomials of bidegree `z`. -/
def coefficientSpan (z : ℤ × ZMod 2) : Submodule k (SYM D k) :=
  Submodule.span k (coefficientBasis D k '' {η | coefficientBidegree sy η = z})

theorem coefficientBasis_mul_mem {η : CoefficientIndex D} {y : SYM D k} {z : ℤ × ZMod 2}
    (hy : y ∈ coefficientSpan sy k z) :
    coefficientBasis D k η * y ∈ coefficientSpan sy k (coefficientBidegree sy η + z) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨θ, hθ, rfl⟩ := hx
      simp only [Set.mem_ofPred_eq] at hθ
      by_cases h : Disjoint η.2 θ.2
      · obtain ⟨c, hc⟩ := coefficientBasis_mul_scalar D k h
        rw [hc]
        refine Submodule.smul_mem _ c (Submodule.subset_span ⟨_, ?_, rfl⟩)
        show coefficientBidegree sy (η.1 + θ.1, η.2 ∪ θ.2) = _
        rw [coefficientBidegree_add sy h, hθ]
      · rw [coefficientBasis_mul_zero D k h]
        exact zero_mem _
  | zero =>
      rw [mul_zero]
      exact zero_mem _
  | add x y _ _ hx hy =>
      rw [mul_add]
      exact add_mem hx hy
  | smul r x _ hx =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hx

theorem word_mem_coefficientSpan (l : List (SYMGen D)) :
    word k l ∈ coefficientSpan sy k (wordBidegree sy l) := by
  induction l with
  | nil =>
      refine Submodule.subset_span ⟨(0, ∅), ?_, ?_⟩
      · show coefficientBidegree sy (0, ∅) = wordBidegree sy []
        simp [coefficientBidegree, wordBidegree]
      · rw [coefficientBasis_zero]
        simp [word]
  | cons g l ih =>
      have hw : word k (g :: l) = ι D k g * word k l := by simp [word]
      have hb : wordBidegree sy (g :: l) =
          (symGenDegree D sy g, symGenParity g) + wordBidegree sy l := by
        simp [wordBidegree]
      rw [hw, hb, ι_eq_coefficientBasis, ← coefficientBidegree_genIndex sy g]
      exact coefficientBasis_mul_mem sy k ih

theorem component_le_coefficientSpan (z : ℤ × ZMod 2) :
    component sy k z ≤ coefficientSpan sy k z := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨l, hl, rfl⟩
  have h : wordBidegree sy l = z := hl
  rw [← h]
  exact word_mem_coefficientSpan sy k l

/-- Each monomial lies in the homogeneous component of its bidegree. -/
theorem coefficientBasis_mem_component (η : CoefficientIndex D) :
    coefficientBasis D k η ∈ component sy k (coefficientBidegree sy η) := by
  generalize hz : coefficientBidegree sy η = z
  have htop : coefficientBasis D k η ∈ ⨆ w, component sy k w := by
    have hle : Submodule.span k (Set.range (word (D := D) k)) ≤ ⨆ w, component sy k w :=
      Submodule.span_le.mpr (by
        rintro _ ⟨l, rfl⟩
        exact Submodule.mem_iSup_of_mem (wordBidegree sy l)
          (Submodule.subset_span ⟨l, rfl, rfl⟩))
    rw [span_range_word] at hle
    exact hle Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp htop
  let W : Submodule k (SYM D k) :=
    Submodule.span k (coefficientBasis D k '' {θ | coefficientBidegree sy θ ≠ z})
  have hW : ∀ w, w ≠ z → component sy k w ≤ W := fun w hw =>
    (component_le_coefficientSpan sy k w).trans (Submodule.span_mono (Set.image_mono
      fun θ hθ => by
        simp only [Set.mem_ofPred_eq] at hθ ⊢
        rw [hθ]
        exact hw))
  have hrest : (f.erase z).sum (fun _ x => x) ∈ W := by
    refine Submodule.finsuppSum_mem k W (f.erase z) _ (fun w hw => ?_)
    have hwz : w ≠ z := by
      rintro rfl
      exact hw (Finsupp.erase_same)
    rw [Finsupp.erase_ne hwz]
    exact hW w hwz (hf w)
  have hsplit : coefficientBasis D k η = f z + (f.erase z).sum (fun _ x => x) := by
    rw [← hsum]
    exact (Finsupp.add_sum_erase' f z (fun _ x => x) (fun _ => rfl)).symm
  have hmem : (f.erase z).sum (fun _ x => x) ∈ coefficientSpan sy k z := by
    have he : (f.erase z).sum (fun _ x => x) = coefficientBasis D k η - f z := by
      rw [hsplit]
      abel
    rw [he]
    exact sub_mem (Submodule.subset_span ⟨η, hz, rfl⟩) (component_le_coefficientSpan sy k z (hf z))
  have hdisj := (coefficientBasis D k).linearIndependent.disjoint_span_image
    (s := {θ | coefficientBidegree sy θ = z}) (t := {θ | coefficientBidegree sy θ ≠ z})
    (Set.disjoint_left.mpr fun _ h1 h2 => h2 h1)
  have h0 := (Submodule.disjoint_def.mp hdisj) _ hmem hrest
  rw [hsplit, h0, add_zero]
  exact hf z

theorem component_eq_coefficientSpan (z : ℤ × ZMod 2) :
    component sy k z = coefficientSpan sy k z := by
  refine le_antisymm (component_le_coefficientSpan sy k z) (Submodule.span_le.mpr ?_)
  rintro _ ⟨η, hη, rfl⟩
  have h : coefficientBidegree sy η = z := hη
  rw [← h]
  exact coefficientBasis_mem_component sy k η

theorem span_range_coefficientBasis (z : ℤ × ZMod 2) :
    Submodule.span k (Set.range fun η : {η : CoefficientIndex D // coefficientBidegree sy η = z} =>
      coefficientBasis D k η.1) = component sy k z := by
  rw [component_eq_coefficientSpan, coefficientSpan, Set.image_eq_range]
  rfl

/-- **The monomials of bidegree `z` form a basis of the homogeneous component `SYM_z`**,
over every commutative ring. -/
def componentBasis (z : ℤ × ZMod 2) :
    Module.Basis {η : CoefficientIndex D // coefficientBidegree sy η = z} k (component sy k z) :=
  (Module.Basis.span ((coefficientBasis D k).linearIndependent.comp Subtype.val
    Subtype.val_injective)).map (LinearEquiv.ofEq _ _ (span_range_coefficientBasis sy k z))

@[simp] theorem componentBasis_apply (z : ℤ × ZMod 2)
    (η : {η : CoefficientIndex D // coefficientBidegree sy η = z}) :
    (componentBasis sy k z η : SYM D k) = coefficientBasis D k η.1 := by
  simp [componentBasis]

/-- The homogeneous components of `SYM` are free modules. -/
theorem free_component (z : ℤ × ZMod 2) : Module.Free k (component sy k z) :=
  Module.Free.of_basis (componentBasis sy k z)

/-- **`dim SYM_z` counts monomials of bidegree `z`**, over every field. In particular it does
not depend on the field. -/
theorem finrank_component (K : Type w) [Field K] (z : ℤ × ZMod 2) :
    Module.finrank K (component sy K z) =
      Nat.card {η : CoefficientIndex D // coefficientBidegree sy η = z} :=
  Module.finrank_eq_nat_card_basis (componentBasis sy K z)

end OddMath.SKM.SYM

namespace OddMath.SKM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}

/-- **The graded superdimension of `SYM`, coefficientwise**: with `π ↦ σ`, the coefficient of
`q^n` in `S = symDimension` is `Σ_p σ^p · #{monomials of degree n and parity p}`. Expanding
the product of ERRATA [BE2] 8 monomial by monomial gives the same count. -/
theorem symDimension_coeff_eq_card (sy : Symmetrizer D) (K : Type w) [Field K] (σ : ℚ)
    (n : ℤ) :
    (symDimension sy K σ).coeff n = ∑ p : ZMod 2, σ ^ p.val *
      (Nat.card {η : SYM.CoefficientIndex D // SYM.coefficientBidegree sy η = (n, p)} : ℚ) := by
  rw [symDimension_coeff]
  simp_rw [SYM.finrank_component]

end OddMath.SKM
