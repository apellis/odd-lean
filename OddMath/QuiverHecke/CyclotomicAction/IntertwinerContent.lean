/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerSkewAction
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.Algebra.Ring.TransferInstance

/-!
# Fixed-content restriction of the moving-strand map

KKO I, arXiv:1206.5933v2, Proposition 8.4 uses fixed-content source and
shifted target modules. Their realization inside the height-indexed balanced
quotients is the right image of the cyclotomic content idempotent, not the
entire quotient. The two projection formulas move that idempotent to the
append/prepend corner by balancing. The induction principles show that the
cut representatives generate all of these summands.

`contentCornerQ` restricts the existing Q; its representative formula,
left action, right coefficient action and signed right variable are retained.
No action is transported along an arbitrary equivalence. This is the
fixed-content restriction step, not a new tensor-product equivalence over the
unital content corner algebra. Finite colours, polynomial parity and positive
quotient height are still required; the zero-height case and QP remain open.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification MulOpposite
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The content identity is even in the affine algebra. -/
theorem contentIdempotent_parity (n : ℕ) (β : Multiset I) :
    contentIdempotent D Sc n β ∈ affineParity D Sc n 0 := by
  classical
  unfold contentIdempotent FiniteHomMatrix.localUnit
  apply Submodule.sum_mem
  intro w _ p
  simp only [FiniteHomMatrix.idem, FiniteHomMatrix.single]
  by_cases h : (w, w) = p
  · subst p
    simpa using (Supercategory.id_mem (R := k) (wordObj D Sc w))
  · simp [DFinsupp.single_apply, h]

/-- The cyclotomic content identity remains even. -/
theorem cyclotomicContentIdempotent_parity (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (β : Multiset I) :
    cyclotomicContentIdempotent D Sc a n β ∈ cyclotomicParity D Sc a ha n 0 :=
  cyclotomicMk_parity D Sc a ha n (contentIdempotent_parity D Sc (n + 1) β)

variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

/-- The append content identity acts as identity on the moving-strand element. -/
theorem appendContent_mul_contentMove (i : I) (n : ℕ) (β : Multiset I) :
    appendAlgebra D Sc i n (contentIdempotent D Sc n β) * contentMove D Sc i n β =
      contentMove D Sc i n β := by
  classical
  rw [contentMove, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  change appendLinear D Sc i n
    (∑ t ∈ Finset.univ.filter (fun t : Word I n => wordContent t = β),
      FiniteHomMatrix.idem t) * _ = _
  rw [map_sum, Finset.sum_mul, Finset.sum_eq_single w]
  · simp only [FiniteHomMatrix.idem, appendLinear_single]
    have hi : appendHom D Sc i w w (𝟙 _) = 𝟙 _ := by
      convert MonoidalSupercategory.id_whiskerRight (R := k)
        (wordObj D Sc w) ((pres D Sc).obj (ob D [i])) using 1 <;> rfl
    rw [hi]
    let f : wordObj D Sc (prependWord i w) ⟶ wordObj D Sc (appendWord i w) :=
      moveHom D Sc i [] w.1
    change FiniteHomMatrix.single (appendWord i w) (appendWord i w) (𝟙 _) *
      FiniteHomMatrix.single (appendWord i w) (prependWord i w) f =
      FiniteHomMatrix.single (appendWord i w) (prependWord i w) f
    rw [FiniteHomMatrix.single_mul_single, Category.comp_id]
  · intro t _ ht
    simp only [FiniteHomMatrix.idem, appendLinear_single]
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => ht (appendWord_injective i n h)) _ _
  · intro h
    exact (h hw).elim

/-- The source content summand is the right image of the coefficient identity. -/
def qSourceContent : Submodule (Hn D Sc (n + 1 + 1))
    (InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
  LinearMap.ker (sourceRightCoefficient D Sc i a n
    (cyclotomicContentIdempotent D Sc a n β) - LinearMap.id)

/-- The target uses the same content cut on the parity-shifted coefficient. -/
def qTargetContent : Submodule (Hn D Sc (n + 1 + 1))
    (InductionAlong.Ind (qCoefficient D Sc i β a ha n).toSVec
      (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) :=
  LinearMap.ker (targetRightCoefficient D Sc i β a ha n
    (cyclotomicContentIdempotent D Sc a n β) - LinearMap.id)

@[simp] theorem mem_qSourceContent (z) : z ∈ qSourceContent D Sc i β a n ↔
    sourceRightCoefficient D Sc i a n (cyclotomicContentIdempotent D Sc a n β) z = z := by
  simp [qSourceContent, LinearMap.mem_ker, sub_eq_zero]

@[simp] theorem mem_qTargetContent (z) : z ∈ qTargetContent D Sc i β a ha n ↔
    targetRightCoefficient D Sc i β a ha n (cyclotomicContentIdempotent D Sc a n β) z = z := by
  simp [qTargetContent, LinearMap.mem_ker, sub_eq_zero]

/-- Q restricts to the content summands of its existing source and shifted target. -/
def contentCornerQ : qSourceContent D Sc i β a n →ₗ[Hn D Sc (n + 1 + 1)]
    qTargetContent D Sc i β a ha n :=
  (parityCyclotomicContentQ D Sc i β a ha n).restrict (by
      intro z hz
      rw [mem_qTargetContent]
      have h := LinearMap.congr_fun (rightCoefficient_Q D Sc i β a ha n
        (cyclotomicContentIdempotent D Sc a n β)) z
      simpa only [LinearMap.comp_apply, (mem_qSourceContent D Sc i β a n z).mp hz] using h)

/-- The source projection is literal multiplication on the coefficient, not identity
on the entire height quotient. -/
theorem sourceContent_project (z) :
    sourceRightCoefficient D Sc i a n (cyclotomicContentIdempotent D Sc a n β) z ∈
      qSourceContent D Sc i β a n := by
  rw [mem_qSourceContent]
  have h := LinearMap.congr_fun (sourceRightCoefficient_mul D Sc i a n
    (cyclotomicContentIdempotent D Sc a n β) (cyclotomicContentIdempotent D Sc a n β)) z
  simpa only [cyclotomicContentIdempotent_sq, LinearMap.comp_apply] using h.symm

/-- Balancing identifies the source projection with the fixed append corner
`a e(β,i)`, using multiplication, not a chosen equivalence. -/
theorem sourceContent_project_tmul
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    sourceRightCoefficient D Sc i a n (cyclotomicContentIdempotent D Sc a n β)
        (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul (op (contentIdempotent D Sc (n + 1) β) • x) b := by
  rw [sourceRightCoefficient_tmul, InductionAlong.Ind.op_smul_tmul]
  congr 1
  rw [← cyclotomicContentIdempotent_central]
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rfl

/-- The shift does not change the action of an even content projector. -/
theorem qCoefficientInsert_content (b : CyclotomicAlgebra D Sc a n) :
    qCoefficientInsert D Sc i β a ha n
        (b * cyclotomicContentIdempotent D Sc a n β) =
      contentIdempotent D Sc (n + 1) β • qCoefficientInsert D Sc i β a ha n b := by
  rw [← cyclotomicContentIdempotent_central]
  have h := qCoefficientInsert_smul D Sc i β a ha n
    (contentIdempotent D Sc (n + 1) β) b
  rw [homMatrixTwist_of_affineParity D Sc _ _ _ _
    (contentIdempotent_parity D Sc (n + 1) β), mul_zero,
    Supercategory.sign_zero, one_smul] at h
  convert h using 1
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rfl

/-- The target projection is the fixed prepend corner `a e(i,β)`, while
retaining the canonical shifted coefficient `π_i^{p(β)} b`. -/
theorem targetContent_project_tmul
    (x : InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    targetRightCoefficient D Sc i β a ha n (cyclotomicContentIdempotent D Sc a n β)
        (InductionAlong.Ind.tmul x (qCoefficientInsert D Sc i β a ha n b)) =
      InductionAlong.Ind.tmul (op (contentIdempotent D Sc (n + 1) β) • x)
        (qCoefficientInsert D Sc i β a ha n b) := by
  rw [targetRightCoefficient_tmul, ← qCoefficientInsert_mul,
    qCoefficientInsert_content, InductionAlong.Ind.op_smul_tmul]

/-- A fixed-content source representative, with its first factor cut by `e(β,i)`. -/
def sourceContentTensor
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) : qSourceContent D Sc i β a n :=
  ⟨InductionAlong.Ind.tmul (op (contentIdempotent D Sc (n + 1) β) • x) b, by
    rw [← sourceContent_project_tmul]
    exact sourceContent_project D Sc i β a n _⟩

/-- The restricted Q is `a e(β,i) ⊗ b ↦ a G_β v ⊗ π_i^{p(β)} b`.
Both the multiplication and the coefficient insertion are the previously constructed maps. -/
@[simp] theorem contentCornerQ_tmul
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    (contentCornerQ D Sc i β a ha n (sourceContentTensor D Sc i β a n x b)).1 =
      InductionAlong.Ind.tmul
        (qPrependCorner D Sc i (n + 1) β
          (InductionAlong.cornerMul (contentMove_intertwines D Sc i (n + 1) β) x))
        (qCoefficientInsert D Sc i β a ha n b) := by
  change InductionAlong.Ind.tmul _ _ = _
  congr 1
  apply Subtype.ext
  change (x.1 * appendAlgebra D Sc i (n + 1) (contentIdempotent D Sc (n + 1) β)) *
      contentMove D Sc i (n + 1) β = x.1 * contentMove D Sc i (n + 1) β
  rw [mul_assoc, appendContent_mul_contentMove]

/-- The canonical shift insertion is onto; no choice of carrier equivalence is used. -/
theorem qCoefficientInsert_surjective :
    Function.Surjective (qCoefficientInsert D Sc i β a ha n) := by
  intro b
  let e := Envelope.ζPow k (D.parity i * contentSumParity D β)
    (SuperBimodule.regular (cyclotomicParity D Sc a ha n))
  refine ⟨e.hom.1 b, ?_⟩
  have h := congrArg (fun f => f.1 b) e.hom_inv_id
  exact h

end OddMath.QuiverHecke
