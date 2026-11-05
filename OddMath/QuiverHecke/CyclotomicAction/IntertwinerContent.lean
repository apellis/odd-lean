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

end OddMath.QuiverHecke
