/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.SignDeterminant
import OddMath.CoveringQuantum.Coefficients.FormSplitting

/-!
# The left radical of the form on `U̇` at `π = -1`

If `x ∈ U̇` pairs to zero at `π = -1` with every element under the positive modified form, then
the negative-fiber component `negativeIdempotent • x` vanishes, provided some weight pairs
positively with every simple coroot. Write `x` as a combination of matched normal words
`F_a 1_ζ E_b`; on the negative fiber each of them is a `ℚ(q)`-combination of matched normal words
over a fixed spanning set `W` (`SignExpansion.exists_spans`), and the Gram matrix of these at
`π = -1` is invertible in each column (`SignDeterminant.det_signGram_ne_zero`), while different
columns are orthogonal. Hence all coefficients vanish.

This is the `π = -1` half of the nondegeneracy of the form on `U̇` (Brundan–Ellis,
arXiv:1701.04133v2, Theorem 10.1) without the bar-consistency hypothesis (10.2). The argument
is ours.
-/

noncomputable section
open Matrix
namespace OddMath.CoveringQuantum.UDot.SignRadical
open PreF Coefficients TensorProduct GenericVerma MixedGram NegativeComparison MixedNormalized
open SignSpanning SignExpansion SignDeterminant NormalizedMixedComparison PolarizationTransport
open BarDerivatives TensorPositive Reciprocal PositiveComparison

/-- The sign idempotent of `π ↦ -1` is the negative-fiber idempotent. -/
theorem signIdempotent_neg_one : signIdempotent (-1) = negativeIdempotent := by
  apply split_injective
  rw [signIdempotent, map_mul, map_add, map_mul, split_algebraMap, split_algebraMap, split_pi,
    map_one, split_negativeIdempotent]
  ext <;> norm_num

variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

theorem smul_mul_eq (x y : CoveringUDot Coefficients.Ring D Coefficients.q pi) :
    negativeIdempotent • (x * y) = (negativeIdempotent • x) * (negativeIdempotent • y) := by
  rw [smul_mul_smul_comm, negativeIdempotent_mul_self]

/-- A matched normal word lies in the block of its weights. -/
theorem pairWord_mem_block {W : Finset (List I)} (ζ : X) (t : Pair W) :
    ((pairWord D ζ t : modified D Coefficients.q pi) :
        CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈
      block D Coefficients.q pi (ζ + halfWeight D true (wordWeight t.2.1) +
        halfWeight D false (wordWeight t.1.1)) ζ := by
  rw [pairWord, algebraWord_normalWord, normalWord]
  exact mul_mem_block D Coefficients.q pi (halfWord_mem_block D Coefficients.q pi false _ _)
    (halfWord_mem_block D Coefficients.q pi true _ _)

/-- Matched normal words in different columns are orthogonal. -/
theorem positiveModifiedForm_pairWord_of_ne {W : Finset (List I)} {ζ ζ' : X} (h : ζ ≠ ζ')
    (t t' : Pair W) :
    GenericTensor.positiveModifiedForm D (pairWord D ζ t) (pairWord D ζ' t') = 0 :=
  GenericTensor.positiveModifiedForm_orthogonal D _ _ _ _ _ _ (pairWord_mem_block D ζ t)
    (pairWord_mem_block D ζ' t') (Or.inr h)

/-- **Column expansion.** On the negative fiber, a matched normal word of bounded length is a
`ℚ(q)`-combination of the matched normal words over `W` in the same column. -/
theorem pairWord_expansion {L : ℕ} {W : Finset (List I)} (hW : Spans D L W) (ζ : X)
    (a b : List I) (ha : a.length ≤ L) (hb : b.length ≤ L) :
    ∃ d : Pair W → RatFunc ℚ, negativeIdempotent • algebraWord D ζ (neg a ++ pos b) =
      ∑ t, algebraMap (RatFunc ℚ) Coefficients.Ring (d t) • negativeIdempotent • pairWord D ζ t := by
  classical
  obtain ⟨c, hc, hca⟩ := hW a ha
  obtain ⟨c', hc', hcb⟩ := hW b hb
  refine ⟨fun t ↦ c t.1.1 * c' t.2.1, ?_⟩
  apply Subtype.ext
  simp only [SetLike.val_smul, AddSubmonoidClass.coe_finsetSum, algebraWord_normalWord,
    normalWord]
  have key (positive : Bool) (μ : X) (w : List I) :
      negativeIdempotent • halfWord D Coefficients.q pi positive w μ =
        halfMap D Coefficients.q pi positive μ
          (negativeIdempotent • D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
    rw [map_smul, halfMap_monomial]
  rw [smul_mul_eq, key, key, hca, hcb, map_sum, map_sum, ← Finset.sum_coe_sort W,
    ← Finset.sum_coe_sort W, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun w' _ ↦ ?_
  by_cases h : c' w' = 0
  · simp [h]
  rw [← (hc' w' h).2]
  simp only [LinearMap.map_smul, halfMap_monomial, map_mul]
  rw [smul_mul_smul_comm, ← smul_mul_eq, mul_smul]

/-- **The left radical at `π = -1`.** If some weight pairs positively with every simple coroot,
an element of `U̇` pairing to zero at `π = -1` with everything under the positive modified form
has vanishing negative-fiber component. -/
theorem negativeIdempotent_smul_eq_zero [Finite I] (hξ : ∃ ξ : X, ∀ i, 0 < D.h i ξ)
    (x : modified D Coefficients.q pi)
    (hx : ∀ y, sgn (GenericTensor.positiveModifiedForm D x y) = 0) :
    negativeIdempotent • x = 0 := by
  classical
  obtain ⟨ξ, hξ⟩ := hξ
  have hmem : (x : CoveringUDot Coefficients.Ring D Coefficients.q pi) ∈
      Submodule.span Coefficients.Ring
        {z | ∃ (a b : List I) (μ : X), z = normalWord D Coefficients.q pi a b μ} := by
    rw [span_normalWords_eq_modified]
    exact x.2
  obtain ⟨n, f, g, hg⟩ := Submodule.mem_span_set'.mp hmem
  choose a b μ hab using fun i ↦ (g i).2
  set L := Finset.univ.sup fun i ↦ max (a i).length (b i).length
  obtain ⟨W, hWL, hdet, hW⟩ := exists_spans D L
  have hlen : ∀ i, (a i).length ≤ L ∧ (b i).length ≤ L := fun i ↦
    max_le_iff.mp (Finset.le_sup (f := fun i ↦ max (a i).length (b i).length)
      (Finset.mem_univ i))
  choose d hd using fun i ↦ pairWord_expansion D hW (μ i) (a i) (b i) (hlen i).1 (hlen i).2
  have hx' : x = ∑ i, f i • algebraWord D (μ i) (neg (a i) ++ pos (b i)) := by
    apply Subtype.ext
    rw [← hg]
    simp only [SetLike.val_smul, AddSubmonoidClass.coe_finsetSum, algebraWord_normalWord, hab]
  have hex : negativeIdempotent • x = ∑ i, ∑ t : Pair W,
      algebraMap (RatFunc ℚ) Coefficients.Ring (sgn (f i) * d i t) •
        negativeIdempotent • pairWord D (μ i) t := by
    rw [hx', Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [negativeIdempotent_smul_smul, hd, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [smul_smul, ← map_mul]
  let v : X → Pair W → RatFunc ℚ := fun ν t ↦ ∑ i, if μ i = ν then sgn (f i) * d i t else 0
  have hv : ∀ ν, v ν = 0 := by
    intro ν
    refine eq_zero_of_vecMul_eq_zero (det_signGram_ne_zero D hW hWL hdet ν ξ hξ)
      (funext fun t' ↦ ?_)
    have h0 := hx (pairWord D ν t')
    rw [← sgn_bilin, hex] at h0
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply,
      smul_eq_mul, map_mul, sgn_algebraMap, sgn_negativeIdempotent, one_mul] at h0
    rw [Pi.zero_apply, ← h0]
    simp only [vecMul, dotProduct, of_apply, v, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun t _ ↦ ?_
    split_ifs with h
    · rw [h]
    · rw [positiveModifiedForm_pairWord_of_ne D h, map_zero, mul_zero, zero_mul]
  have hS : ∀ i ∈ Finset.univ, μ i ∈ Finset.univ.image μ := fun i _ ↦
    Finset.mem_image_of_mem μ (Finset.mem_univ i)
  rw [hex, ← Finset.sum_fiberwise_of_maps_to hS]
  refine Finset.sum_eq_zero fun ν _ ↦ ?_
  calc
    _ = ∑ t : Pair W, algebraMap (RatFunc ℚ) Coefficients.Ring (v ν t) •
          negativeIdempotent • pairWord D ν t := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      simp only [v, ← Finset.sum_filter, map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [(Finset.mem_filter.mp hi).2]
    _ = 0 := by simp [hv ν]

end OddMath.CoveringQuantum.UDot.SignRadical
