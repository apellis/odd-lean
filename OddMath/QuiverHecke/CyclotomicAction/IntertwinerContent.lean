/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerSupertensorGrading

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

/-- The shifted target projection is idempotent as well. -/
theorem targetContent_project (z) :
    targetRightCoefficient D Sc i β a ha n (cyclotomicContentIdempotent D Sc a n β) z ∈
      qTargetContent D Sc i β a ha n := by
  rw [mem_qTargetContent]
  have h := LinearMap.congr_fun (targetRightCoefficient_mul D Sc i β a ha n
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

/-- Every cyclotomic coefficient preserves the source content summand. -/
theorem sourceContent_coefficient (c : CyclotomicAlgebra D Sc a n)
    (z) (hz : z ∈ qSourceContent D Sc i β a n) :
    sourceRightCoefficient D Sc i a n c z ∈ qSourceContent D Sc i β a n := by
  rw [mem_qSourceContent] at hz ⊢
  have h := congrArg (fun f => f z) (sourceRightCoefficient_mul D Sc i a n c
    (cyclotomicContentIdempotent D Sc a n β))
  rw [← cyclotomicContentIdempotent_central, sourceRightCoefficient_mul] at h
  simpa only [LinearMap.comp_apply, hz] using h.symm

/-- Every cyclotomic coefficient preserves the shifted target content summand. -/
theorem targetContent_coefficient (c : CyclotomicAlgebra D Sc a n)
    (z) (hz : z ∈ qTargetContent D Sc i β a ha n) :
    targetRightCoefficient D Sc i β a ha n c z ∈ qTargetContent D Sc i β a ha n := by
  rw [mem_qTargetContent] at hz ⊢
  have h := congrArg (fun f => f z) (targetRightCoefficient_mul D Sc i β a ha n c
    (cyclotomicContentIdempotent D Sc a n β))
  rw [← cyclotomicContentIdempotent_central, targetRightCoefficient_mul] at h
  simpa only [LinearMap.comp_apply, hz] using h.symm

/-- The right polynomial variable preserves fixed source content. -/
theorem sourceContent_dot (z) (hz : z ∈ qSourceContent D Sc i β a n) :
    sourceRightDot D Sc i a ha n z ∈ qSourceContent D Sc i β a n := by
  rw [mem_qSourceContent] at hz ⊢
  have h := LinearMap.congr_fun (sourceRightDot_coefficient D Sc i a ha n 0
    (cyclotomicContentIdempotent D Sc a n β)
    (cyclotomicContentIdempotent_parity D Sc a ha n β)) z
  simp only [mul_zero, Supercategory.sign_zero, one_smul] at h
  change sourceRightDot D Sc i a ha n
    (sourceRightCoefficient D Sc i a n (cyclotomicContentIdempotent D Sc a n β) z) =
    sourceRightCoefficient D Sc i a n (cyclotomicContentIdempotent D Sc a n β)
      (sourceRightDot D Sc i a ha n z) at h
  rw [hz] at h
  exact h.symm

/-- The signed first-dot action preserves fixed target content. -/
theorem targetContent_dot (z) (hz : z ∈ qTargetContent D Sc i β a ha n) :
    targetRightDot D Sc i β a ha n z ∈ qTargetContent D Sc i β a ha n := by
  rw [mem_qTargetContent] at hz ⊢
  have h := LinearMap.congr_fun (targetRightDot_coefficient D Sc i β a ha n 0
    (cyclotomicContentIdempotent D Sc a n β)
    (cyclotomicContentIdempotent_parity D Sc a ha n β)) z
  simp only [mul_zero, Supercategory.sign_zero, one_smul] at h
  change targetRightDot D Sc i β a ha n
    (targetRightCoefficient D Sc i β a ha n (cyclotomicContentIdempotent D Sc a n β) z) =
    targetRightCoefficient D Sc i β a ha n (cyclotomicContentIdempotent D Sc a n β)
      (targetRightDot D Sc i β a ha n z) at h
  rw [hz] at h
  exact h.symm

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

/-- Right coefficient multiplication on the fixed source, inherited without transport. -/
def sourceContentRightCoefficient (c : CyclotomicAlgebra D Sc a n) :
    Module.End (Hn D Sc (n + 1 + 1)) (qSourceContent D Sc i β a n) :=
  (sourceRightCoefficient D Sc i a n c).restrict (sourceContent_coefficient D Sc i β a n c)

/-- Right coefficient multiplication on the shifted fixed target. -/
def targetContentRightCoefficient (c : CyclotomicAlgebra D Sc a n) :
    Module.End (Hn D Sc (n + 1 + 1)) (qTargetContent D Sc i β a ha n) :=
  (targetRightCoefficient D Sc i β a ha n c).restrict (targetContent_coefficient D Sc i β a ha n c)

/-- The source variable remains the existing right last-dot operator. -/
def sourceContentRightDot :
    Module.End (Hn D Sc (n + 1 + 1)) (qSourceContent D Sc i β a n) :=
  (sourceRightDot D Sc i a ha n).restrict (sourceContent_dot D Sc i β a ha n)

/-- The target variable remains the signed first-dot and coefficient involution. -/
def targetContentRightDot :
    Module.End (Hn D Sc (n + 1 + 1)) (qTargetContent D Sc i β a ha n) :=
  (targetRightDot D Sc i β a ha n).restrict (targetContent_dot D Sc i β a ha n)

/-- Q commutes with the right coefficient action on the fixed-content carriers. -/
theorem contentCornerQ_rightCoefficient (c : CyclotomicAlgebra D Sc a n)
    (z : qSourceContent D Sc i β a n) :
    contentCornerQ D Sc i β a ha n (sourceContentRightCoefficient D Sc i β a n c z) =
      targetContentRightCoefficient D Sc i β a ha n c (contentCornerQ D Sc i β a ha n z) := by
  apply Subtype.ext
  exact (LinearMap.congr_fun (rightCoefficient_Q D Sc i β a ha n c) z.1).symm

/-- Q commutes with the right polynomial variable on the fixed-content carriers. -/
theorem contentCornerQ_rightDot (z : qSourceContent D Sc i β a n) :
    contentCornerQ D Sc i β a ha n (sourceContentRightDot D Sc i β a ha n z) =
      targetContentRightDot D Sc i β a ha n (contentCornerQ D Sc i β a ha n z) := by
  apply Subtype.ext
  exact (LinearMap.congr_fun (targetRightDot_Q D Sc i β a ha n) z.1).symm

/-- The left module action is also the existing one, with no parity sign inserted. -/
theorem contentCornerQ_left (r : Hn D Sc (n + 1 + 1))
    (z : qSourceContent D Sc i β a n) :
    contentCornerQ D Sc i β a ha n (r • z) = r • contentCornerQ D Sc i β a ha n z :=
  map_smul (contentCornerQ D Sc i β a ha n) r z

/-- The canonical shift insertion is onto; no choice of carrier equivalence is used. -/
theorem qCoefficientInsert_surjective :
    Function.Surjective (qCoefficientInsert D Sc i β a ha n) := by
  intro b
  let e := Envelope.ζPow k (D.parity i * contentSumParity D β)
    (SuperBimodule.regular (cyclotomicParity D Sc a ha n))
  refine ⟨e.hom.1 b, ?_⟩
  have h := congrArg (fun f => f.1 b) e.hom_inv_id
  exact h

/-- Every fixed source element is generated additively by the cut representatives. -/
@[elab_as_elim] theorem sourceContent_induction
    (P : qSourceContent D Sc i β a n → Prop)
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (htmul : ∀ x b, P (sourceContentTensor D Sc i β a n x b))
    (z : qSourceContent D Sc i β a n) : P z := by
  let f : _ →ₗ[Hn D Sc (n + 1 + 1)] qSourceContent D Sc i β a n :=
    (sourceRightCoefficient D Sc i a n (cyclotomicContentIdempotent D Sc a n β)).codRestrict
      _ (sourceContent_project D Sc i β a n)
  have hf : f z.1 = z := Subtype.ext ((mem_qSourceContent D Sc i β a n z.1).mp z.2)
  rw [← hf]
  induction z.1 using InductionAlong.Ind.induction_on with
  | zero => simpa only [map_zero] using hzero
  | add x y hx hy => simpa only [map_add] using hadd (f x) (f y) hx hy
  | tmul x b =>
    have he : f (InductionAlong.Ind.tmul x b) = sourceContentTensor D Sc i β a n x b :=
      Subtype.ext (sourceContent_project_tmul D Sc i β a n x b)
    rw [he]
    exact htmul x b

/-- A fixed target representative, retaining its coefficient parity shift. -/
def targetContentTensor
    (x : InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) : qTargetContent D Sc i β a ha n :=
  ⟨InductionAlong.Ind.tmul (op (contentIdempotent D Sc (n + 1) β) • x)
    (qCoefficientInsert D Sc i β a ha n b), by
      rw [← targetContent_project_tmul]
      exact targetContent_project D Sc i β a ha n _⟩

/-- Every fixed shifted target element is generated by prepend-cut representatives. -/
@[elab_as_elim] theorem targetContent_induction
    (P : qTargetContent D Sc i β a ha n → Prop)
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (htmul : ∀ x b, P (targetContentTensor D Sc i β a ha n x b))
    (z : qTargetContent D Sc i β a ha n) : P z := by
  let f : _ →ₗ[Hn D Sc (n + 1 + 1)] qTargetContent D Sc i β a ha n :=
    (targetRightCoefficient D Sc i β a ha n (cyclotomicContentIdempotent D Sc a n β)).codRestrict
      _ (targetContent_project D Sc i β a ha n)
  have hf : f z.1 = z := Subtype.ext ((mem_qTargetContent D Sc i β a ha n z.1).mp z.2)
  rw [← hf]
  induction z.1 using InductionAlong.Ind.induction_on with
  | zero => simpa only [map_zero] using hzero
  | add x y hx hy => simpa only [map_add] using hadd (f x) (f y) hx hy
  | tmul x b =>
    obtain ⟨b, rfl⟩ := qCoefficientInsert_surjective D Sc i β a ha n b
    have he : f (InductionAlong.Ind.tmul x (qCoefficientInsert D Sc i β a ha n b)) =
        targetContentTensor D Sc i β a ha n x b :=
      Subtype.ext (targetContent_project_tmul D Sc i β a ha n x b)
    rw [he]
    exact htmul x b

/-- The fixed target variable has the prescribed sign and coefficient involution. -/
theorem targetContentRightDot_tmul
    (x : InductionAlong.Corner (prependAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    (targetContentRightDot D Sc i β a ha n (targetContentTensor D Sc i β a ha n x b)).1 =
      InductionAlong.Ind.tmul
        (targetDotCorner D Sc i (n + 1) (op (contentIdempotent D Sc (n + 1) β) • x))
        (Supercategory.sign k (D.parity i * contentSumParity D β) •
          qCoefficientInsert D Sc i β a ha n (rightDotCoefficient D Sc i a ha n b)) := by
  change targetRightDot D Sc i β a ha n (InductionAlong.Ind.tmul _ _) = _
  rw [targetRightDot_tmul, targetDotCoefficient_insert]

end OddMath.QuiverHecke
