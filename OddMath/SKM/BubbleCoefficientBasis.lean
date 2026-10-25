/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubblePolynomialExterior
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Independent coefficient monomials and their weights

Supporting the weighted coefficient-separation step of research issue #345,
using the abstract coefficient presentation of Brundan–Ellis (1.21)–(1.22).
This basis concerns the abstract coefficient algebra, not its diagrammatic image.
-/

noncomputable section
open scoped Classical TensorProduct
namespace OddMath.SKM.SYM
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k]

abbrev CoefficientIndex := ((I × ℕ) →₀ ℕ) × Finset {i : I // D.parity i = 1}

/-- A basis of the full coefficient algebra. The chosen order only fixes
the signs of exterior monomials; it adds no hypothesis on the colour set. -/
def coefficientBasis : Module.Basis (CoefficientIndex D) k (SYM D k) := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  exact ((MvPolynomial.basisMonomials (I × ℕ) k).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis {i : I // D.parity i = 1} k (OddModule D k)).ExteriorAlgebra).map
      (polynomialExteriorEquiv D k).symm.toLinearEquiv

/-- The exterior basis uses the same fixed well-order as `coefficientBasis`. -/
def oddExteriorBasis : Module.Basis (Finset {i : I // D.parity i = 1}) k
    (ExteriorAlgebra k (OddModule D k)) := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  exact (Finsupp.basisSingleOne : Module.Basis {i : I // D.parity i = 1} k (OddModule D k)).ExteriorAlgebra

@[simp] theorem coefficientBasis_projection (a : CoefficientIndex D) :
    polynomialExteriorEquiv D k (coefficientBasis D k a) =
      MvPolynomial.monomial a.1 1 ⊗ₜ[k] oddExteriorBasis D k a.2 := by
  simp [coefficientBasis, oddExteriorBasis, Module.Basis.tensorProduct_apply',
    MvPolynomial.coe_basisMonomials]

 theorem oddExteriorBasis_mul_zero {s t : Finset {i : I // D.parity i = 1}}
    (h : ¬Disjoint s t) : oddExteriorBasis D k s * oddExteriorBasis D k t = 0 := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  exact ExteriorAlgebra.basis_mul_of_not_disjoint
    (Finsupp.basisSingleOne : Module.Basis {i : I // D.parity i = 1} k (OddModule D k))
    (Set.powersetCard.ofCard (rfl : s.card = s.card))
    (Set.powersetCard.ofCard (rfl : t.card = t.card)) h

 theorem oddExteriorBasis_mul_scalar {s t : Finset {i : I // D.parity i = 1}}
    (h : Disjoint s t) : ∃ c : k,
      oddExteriorBasis D k s * oddExteriorBasis D k t = c • oddExteriorBasis D k (s ∪ t) := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  let ss := Set.powersetCard.ofCard (rfl : s.card = s.card)
  let tt := Set.powersetCard.ofCard (rfl : t.card = t.card)
  have he := ExteriorAlgebra.basis_mul_of_disjoint
    (Finsupp.basisSingleOne : Module.Basis {i : I // D.parity i = 1} k (OddModule D k)) ss tt h
  refine ⟨((Set.powersetCard.permOfDisjoint (s := ss) (t := tt) h).sign : ℤ), ?_⟩
  simpa only [oddExteriorBasis, ss, tt, Set.powersetCard.disjUnion, Set.powersetCard.ofCard,
    Finset.disjUnion_eq_union, Units.smul_def, Int.cast_smul_eq_zsmul] using he

 theorem coefficientBasis_mul_zero {a b : CoefficientIndex D} (h : ¬Disjoint a.2 b.2) :
    coefficientBasis D k a * coefficientBasis D k b = 0 := by
  apply (polynomialExteriorEquiv D k).injective
  simp only [map_mul, coefficientBasis_projection, Algebra.TensorProduct.tmul_mul_tmul,
    oddExteriorBasis_mul_zero D k h, TensorProduct.tmul_zero, map_zero]

 theorem coefficientBasis_mul_scalar {a b : CoefficientIndex D} (h : Disjoint a.2 b.2) :
    ∃ c : k, coefficientBasis D k a * coefficientBasis D k b =
      c • coefficientBasis D k (a.1 + b.1, a.2 ∪ b.2) := by
  obtain ⟨c, hc⟩ := oddExteriorBasis_mul_scalar D k h
  refine ⟨c, ?_⟩
  apply (polynomialExteriorEquiv D k).injective
  simp only [map_mul, map_smul, coefficientBasis_projection, Algebra.TensorProduct.tmul_mul_tmul,
    MvPolynomial.monomial_mul_monomial, one_mul, hc, TensorProduct.tmul_smul]

/-- Dot weight of an elementary coefficient. Odd-colour elementary generators
represent even powers of the odd dot. -/
def elementaryWeight (a : I × ℕ) : ℕ :=
  if D.parity a.1 = 0 then a.2 + 1 else 2 * (a.2 + 1)

def coefficientWeight (a : CoefficientIndex D) : ℕ :=
  a.1.sum (fun i n => n * elementaryWeight D i) + a.2.card

/-- Coefficient monomials supported in weight at most `d`. -/
def CoefficientAtMost (d : ℕ) : Submodule k (SYM D k) :=
  Submodule.span k (coefficientBasis D k '' {a | coefficientWeight D a ≤ d})

/-- Coefficient monomials supported in weight at least `d`. -/
def CoefficientAtLeast (d : ℕ) : Submodule k (SYM D k) :=
  Submodule.span k (coefficientBasis D k '' {a | d ≤ coefficientWeight D a})

theorem disjoint_coefficientAtMost_coefficientAtLeast {d N : ℕ} (h : d < N) :
    Disjoint (CoefficientAtMost D k d) (CoefficientAtLeast D k N) := by
  apply (coefficientBasis D k).linearIndependent.disjoint_span_image
  rw [Set.disjoint_left]
  intro a ha hb
  simp only [Set.mem_ofPred_eq] at ha hb
  omega

/-- Every abstract coefficient has a finite weight bound, with both polynomial
and exterior factors included. -/
theorem exists_coefficientAtMost (x : SYM D k) : ∃ d, x ∈ CoefficientAtMost D k d := by
  let c := (coefficientBasis D k).repr x
  let d := c.support.sup (coefficientWeight D)
  refine ⟨d, ?_⟩
  rw [← (coefficientBasis D k).linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨a, Finset.le_sup (f := coefficientWeight D) ha, rfl⟩

 theorem coefficientWeight_mul {a b : CoefficientIndex D} (h : Disjoint a.2 b.2) :
    coefficientWeight D (a.1 + b.1, a.2 ∪ b.2) = coefficientWeight D a + coefficientWeight D b := by
  have hp : (a.1 + b.1).sum (fun i n => n * elementaryWeight D i) =
      a.1.sum (fun i n => n * elementaryWeight D i) + b.1.sum (fun i n => n * elementaryWeight D i) :=
    Finsupp.sum_add_index (by intro i; simp) (by intros; simp [add_mul])
  simp only [coefficientWeight, hp, Finset.card_union_of_disjoint h]
  omega

 theorem coefficientBasis_mul_mem_high {a b : CoefficientIndex D} {m n : ℕ}
    (ha : m ≤ coefficientWeight D a) (hb : n ≤ coefficientWeight D b) :
    coefficientBasis D k a * coefficientBasis D k b ∈ CoefficientAtLeast D k (m + n) := by
  by_cases hd : Disjoint a.2 b.2
  · obtain ⟨c, hc⟩ := coefficientBasis_mul_scalar D k hd
    rw [hc]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨(a.1 + b.1, a.2 ∪ b.2), ?_, rfl⟩
    change m + n ≤ coefficientWeight D (a.1 + b.1, a.2 ∪ b.2)
    rw [coefficientWeight_mul D hd]
    omega
  · rw [coefficientBasis_mul_zero D k hd]
    exact Submodule.zero_mem _

/-- The full polynomial/exterior coefficient weight is multiplicative, with
no exceptional collapse of mixed odd products hidden in the filtration. -/
theorem coefficientAtLeast_mul {m n : ℕ} {x y : SYM D k}
    (hx : x ∈ CoefficientAtLeast D k m) (hy : y ∈ CoefficientAtLeast D k n) :
    x * y ∈ CoefficientAtLeast D k (m + n) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      exact coefficientBasis_mul_mem_high D k ha hb
    | zero => simp
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x z _ _ hx hz =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hz
  | smul c x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hx

 theorem mem_coefficientAtLeast_zero (x : SYM D k) : x ∈ CoefficientAtLeast D k 0 := by
  rw [← (coefficientBasis D k).linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨a, Nat.zero_le _, rfl⟩

 theorem coefficientAtLeast_mul_left {n : ℕ} (x : SYM D k) {y : SYM D k}
    (hy : y ∈ CoefficientAtLeast D k n) : x * y ∈ CoefficientAtLeast D k n := by
  simpa only [zero_add] using coefficientAtLeast_mul D k (mem_coefficientAtLeast_zero D k x) hy

 theorem coefficientAtLeast_mul_right {n : ℕ} {x : SYM D k} (y : SYM D k)
    (hx : x ∈ CoefficientAtLeast D k n) : x * y ∈ CoefficientAtLeast D k n := by
  simpa only [add_zero] using coefficientAtLeast_mul D k hx (mem_coefficientAtLeast_zero D k y)

/-- High coefficient weight defines an actual two-sided ideal of the
noncommutative polynomial/exterior algebra. -/
def coefficientIdeal (N : ℕ) : TwoSidedIdeal (SYM D k) :=
  TwoSidedIdeal.mk' (CoefficientAtLeast D k N)
    (Submodule.zero_mem _) (fun hx hy => Submodule.add_mem _ hx hy)
    (fun hx => Submodule.neg_mem _ hx)
    (fun {x _} hy => coefficientAtLeast_mul_left D k x hy)
    (fun {_ y} hx => coefficientAtLeast_mul_right D k y hx)

/-- Weight truncations of the full coefficient algebra detect its bounded
part; independent exterior products participate in the same basis argument. -/
theorem coefficient_weight_quotient_injective {d N : ℕ} (hN : d < N) :
    Function.Injective (fun x : CoefficientAtMost D k d =>
      (coefficientIdeal D k N).ringCon.mk' (x : SYM D k)) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hmem : (x : SYM D k) - y ∈ CoefficientAtLeast D k N := Quotient.exact hxy
  exact Submodule.disjoint_def.mp
    (disjoint_coefficientAtMost_coefficientAtLeast D k hN) _
    (Submodule.sub_mem _ x.property y.property) hmem

end OddMath.SKM.SYM
