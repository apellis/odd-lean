/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContent
import Mathlib.RingTheory.Idempotents

/-!
# Source tensor over the unital content algebra

KKO I, arXiv:1206.5933v2, §8, Proposition 8.4 uses the source
`R(β + αᵢ)e(β,i) ⊗[R(β)] RΛ(β)`. Here the coefficient algebra is
Mathlib's unital idempotent corner, and its action is the restricted
cyclotomic quotient map. The first factor is the append left ideal; its
support in the enlarged content block is proved.

`contentSourceEquiv` compares this tensor with `qSourceContent` by inclusion
and explicit cuts of both representatives. Both composites are proved.
`contentTensorQ_representative` applies the comparison to the prescribed Q.
Finite colours and positive coefficient height remain required. Polynomial
parity is required for Q, not for the source comparison. The shifted target
tensor comparison, zero-height case and QP are not asserted here.
-/

noncomputable section
open Categorification MulOpposite
namespace OddMath.QuiverHecke.ContentTensor
universe u
variable {A B C : Type u} [Ring A] [Ring B] [Ring C]
variable (φ : A →ₙ+* B) (q : A →+* C) (e : A) (he : IsIdempotentElem e)

/-- Inclusion of the unital idempotent corner, forgetting its unit. -/
def inclusion : he.Corner →ₙ+* A where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The coefficient corner has the image idempotent as its unit. -/
abbrev Coefficient := (he.map q).Corner

/-- The quotient map restricted to both unital corners. -/
def quotient : he.Corner →+* Coefficient q e he where
  toFun x := ⟨q x.1, by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨q y, by
      change q e * q y * q e = q x.1
      simpa only [map_mul] using congrArg q hy⟩⟩
  map_one' := Subtype.ext rfl
  map_zero' := Subtype.ext (map_zero q)
  map_add' x y := Subtype.ext (map_add q x.1 y.1)
  map_mul' x y := Subtype.ext (map_mul q x.1 y.1)

instance coefficientModule : Module he.Corner (Coefficient q e he) :=
  Module.compHom _ (quotient q e he)

/-- The inclusion sends the content unit to the appended content idempotent. -/
def append : he.Corner →ₙ+* B := φ.comp (inclusion e he)

/-- The tensor over the unital corner, with its cyclotomic corner coefficient. -/
abbrev Source := InductionAlong.Ind (Coefficient q e he) (append φ e he)

/-- Inclusion of the smaller left ideal into the height left ideal. -/
def cornerIn (x : InductionAlong.Corner (append φ e he)) : InductionAlong.Corner φ :=
  ⟨x.1, by
    change x.1 * φ 1 = x.1
    have hx : x.1 * φ e = x.1 := x.2
    rw [← hx, mul_assoc, ← map_mul, mul_one]⟩

variable (hc : ∀ a, e * a = a * e)

/-- Multiplication by the central content identity, valued in its unital corner. -/
def cut (a : A) : he.Corner := ⟨e * a, a, by
  change e * a * e = e * a
  rw [mul_assoc, ← hc a, ← mul_assoc, he.eq]⟩

@[simp] theorem cut_val (a : A) : (cut e he hc a).1 = e * a := rfl

/-- The coefficient projection is literal multiplication by the quotient identity. -/
def cutCoefficient (c : C) (hqc : ∀ c, q e * c = c * q e) : Coefficient q e he :=
  ⟨q e * c, c, by
    change q e * c * q e = q e * c
    rw [mul_assoc, ← hqc c, ← mul_assoc, (he.map q).eq]⟩

/-- Cut the first factor by the appended content identity. -/
def cutCorner (x : InductionAlong.Corner φ) : InductionAlong.Corner (append φ e he) :=
  ⟨x.1 * φ e, by
    change x.1 * φ e * φ e = x.1 * φ e
    rw [mul_assoc, ← map_mul, he.eq]⟩

section Comparison
variable [Module A C] (hsmul : ∀ (r : A) (b : C), r • b = q r * b)

/-- Forward representative map: include both factors into the height tensor. -/
def forward : Source φ q e he →ₗ[B] InductionAlong.Ind C φ :=
  InductionAlong.Ind.lift
    (fun x b => InductionAlong.Ind.tmul (cornerIn φ e he x) b.1)
    (fun x y b => by
      have h : cornerIn φ e he (x + y) = cornerIn φ e he x + cornerIn φ e he y := rfl
      rw [h]
      exact InductionAlong.Ind.add_tmul (cornerIn φ e he x) (cornerIn φ e he y) b.1)
    (fun x b c => by
      change InductionAlong.Ind.tmul (cornerIn φ e he x) (b.1 + c.1) = _
      exact InductionAlong.Ind.tmul_add (cornerIn φ e he x) b.1 c.1)
    (fun x r b => by
      change InductionAlong.Ind.tmul (op r.1 • cornerIn φ e he x) b.1 =
        InductionAlong.Ind.tmul (cornerIn φ e he x) (q r.1 * b.1)
      rw [InductionAlong.Ind.op_smul_tmul, hsmul])
    (fun r x b => by
      change InductionAlong.Ind.tmul (r • cornerIn φ e he x) b.1 =
        r • InductionAlong.Ind.tmul (cornerIn φ e he x) b.1
      exact (InductionAlong.Ind.smul_tmul r (cornerIn φ e he x) b.1).symm)

variable (hqc : ∀ c, q e * c = c * q e)

/-- Backward representative assignment: cut both factors by the content identities. -/
def backward : InductionAlong.Ind C φ →ₗ[B] Source φ q e he :=
  InductionAlong.Ind.lift
    (fun x b => InductionAlong.Ind.tmul (cutCorner φ e he x) (cutCoefficient q e he b hqc))
    (fun x y b => by
      rw [← InductionAlong.Ind.add_tmul]
      congr 1
      exact Subtype.ext (add_mul _ _ _))
    (fun x b c => by
      rw [← InductionAlong.Ind.tmul_add]
      congr 1
      exact Subtype.ext (mul_add _ _ _))
    (fun x r b => by
      have hx : cutCorner φ e he (op r • x) =
          op (cut e he hc r) • cutCorner φ e he x := by
        apply Subtype.ext
        change x.1 * φ r * φ e = (x.1 * φ e) * φ (e * r)
        rw [mul_assoc, ← map_mul, ← hc r]
        symm
        rw [mul_assoc, ← map_mul, ← mul_assoc, he.eq]
      rw [hx, InductionAlong.Ind.op_smul_tmul]
      congr 1
      apply Subtype.ext
      change q (e * r) * (q e * b) = q e * (r • b)
      rw [hsmul, ← mul_assoc, ← map_mul]
      have h : e * r * e = e * r := by
        rw [mul_assoc, ← hc r, ← mul_assoc, he.eq]
      rw [h, map_mul, mul_assoc])
    (fun r x b => by
      rw [InductionAlong.Ind.smul_tmul]
      congr 1
      exact Subtype.ext (mul_assoc _ _ _))

/-- Including and recutting a content tensor is the identity. -/
theorem backward_forward (z : Source φ q e he) :
    backward φ q e he hc hsmul hqc (forward φ q e he hsmul z) = z := by
  induction z using InductionAlong.Ind.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul x b =>
    change InductionAlong.Ind.tmul (cutCorner φ e he (cornerIn φ e he x))
      (cutCoefficient q e he b.1 hqc) = InductionAlong.Ind.tmul x b
    have hx : cutCorner φ e he (cornerIn φ e he x) = x := Subtype.ext x.2
    have hb : cutCoefficient q e he b.1 hqc = b :=
      Subtype.ext ((Subsemigroup.mem_corner_iff (he.map q)).mp b.2).1
    rw [hx, hb]

/-- The other composite is the content projection, not the identity on all heights. -/
theorem forward_backward_tmul (x : InductionAlong.Corner φ) (b : C) :
    forward φ q e he hsmul
      (backward φ q e he hc hsmul hqc (InductionAlong.Ind.tmul x b)) =
        InductionAlong.Ind.tmul x (q e * b) := by
  change InductionAlong.Ind.tmul (op e • x) (q e * b) = _
  rw [InductionAlong.Ind.op_smul_tmul, hsmul, ← mul_assoc, ← map_mul, he.eq]

end Comparison
end OddMath.QuiverHecke.ContentTensor

namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k) (n : ℕ)

/-- The unital affine algebra of the fixed content, with unit `e(β)`. -/
abbrev ContentAlgebra := (show IsIdempotentElem (contentIdempotent D Sc (n + 1) β)
  from contentIdempotent_sq D Sc (n + 1) β).Corner

/-- KKO I §8 source tensor over the unital fixed-content algebra. The first
factor is the left ideal cut by the append inclusion of its unit, and the second
is the corresponding corner of the existing cyclotomic quotient. -/
abbrev contentSourceTensor := ContentTensor.Source
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
  (cyclotomicMk D Sc a n).toRingHom (contentIdempotent D Sc (n + 1) β)
  (contentIdempotent_sq D Sc (n + 1) β)


/-- The append left ideal is already supported on the enlarged content block. -/
theorem contentSourceCorner_support
    (x : InductionAlong.Corner (ContentTensor.append
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
      (contentIdempotent D Sc (n + 1) β) (contentIdempotent_sq D Sc (n + 1) β))) :
    contentIdempotent D Sc (n + 1 + 1) ({i} + β) * x.1 = x.1 := by
  have hx : x.1 * appendAlgebra D Sc i (n + 1) (contentIdempotent D Sc (n + 1) β) = x.1 := x.2
  calc
    _ = contentIdempotent D Sc (n + 1 + 1) ({i} + β) *
        (x.1 * appendAlgebra D Sc i (n + 1) (contentIdempotent D Sc (n + 1) β)) := congrArg _ hx.symm
    _ = x.1 * (contentIdempotent D Sc (n + 1 + 1) ({i} + β) *
        appendAlgebra D Sc i (n + 1) (contentIdempotent D Sc (n + 1) β)) := by
      rw [← mul_assoc, contentIdempotent_central, mul_assoc]
    _ = x.1 := by rw [contentIdempotent_appendAlgebra, contentIdempotent_sq, hx]

/-- Inclusion of both factors of the fixed-content source tensor. -/
def contentSourceForward : contentSourceTensor D Sc i β a n →ₗ[Hn D Sc (n + 1 + 1)]
    InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)) :=
  ContentTensor.forward _ _ _ _ (fun _ _ => rfl)

/-- The inverse representative assignment cuts the append factor and coefficient. -/
def contentSourceBackward :
    InductionAlong.Ind (CyclotomicAlgebra D Sc a n)
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
    →ₗ[Hn D Sc (n + 1 + 1)] contentSourceTensor D Sc i β a n :=
  ContentTensor.backward _ _ _ _ (contentIdempotent_central D Sc (n + 1) β)
    (fun _ _ => rfl) (cyclotomicContentIdempotent_central D Sc a n β)

/-- The inclusion followed by the cut assignment is identity on the content tensor. -/
theorem contentSourceBackward_forward (z : contentSourceTensor D Sc i β a n) :
    contentSourceBackward D Sc i β a n (contentSourceForward D Sc i β a n z) = z :=
  ContentTensor.backward_forward _ _ _ _ _ _ _ z

/-- On the height tensor the reverse composite is exactly the existing content projector. -/
theorem contentSourceForward_backward (z) :
    contentSourceForward D Sc i β a n (contentSourceBackward D Sc i β a n z) =
      sourceRightCoefficient D Sc i a n (cyclotomicContentIdempotent D Sc a n β) z := by
  induction z using InductionAlong.Ind.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul x b =>
    change ContentTensor.forward _ _ _ _ _ (ContentTensor.backward _ _ _ _ _ _ _ _) = _
    rw [ContentTensor.forward_backward_tmul, sourceRightCoefficient_tmul]
    exact congrArg (InductionAlong.Ind.tmul x)
      (cyclotomicContentIdempotent_central D Sc a n β b)

/-- The forward multiplication/inclusion map takes values in the fixed-content source. -/
theorem contentSourceForward_mem (z : contentSourceTensor D Sc i β a n) :
    contentSourceForward D Sc i β a n z ∈ qSourceContent D Sc i β a n := by
  rw [mem_qSourceContent, ← contentSourceForward_backward, contentSourceBackward_forward]

/-- Explicit two-sided comparison with the fixed-content summand, not a chosen bijection. -/
def contentSourceEquiv : contentSourceTensor D Sc i β a n ≃ₗ[Hn D Sc (n + 1 + 1)]
    qSourceContent D Sc i β a n where
  toFun z := ⟨contentSourceForward D Sc i β a n z, contentSourceForward_mem D Sc i β a n z⟩
  invFun z := contentSourceBackward D Sc i β a n z.1
  left_inv := contentSourceBackward_forward D Sc i β a n
  right_inv z := Subtype.ext ((contentSourceForward_backward D Sc i β a n z.1).trans
    ((mem_qSourceContent D Sc i β a n z.1).mp z.2))
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' r x := Subtype.ext (map_smul _ r x)

/-- The inverse representative cuts both tensor factors. -/
def contentSourceRepresentative
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) : contentSourceTensor D Sc i β a n :=
  contentSourceBackward D Sc i β a n (InductionAlong.Ind.tmul x b)

@[simp] theorem contentSourceEquiv_representative
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    contentSourceEquiv D Sc i β a n (contentSourceRepresentative D Sc i β a n x b) =
      sourceContentTensor D Sc i β a n x b := by
  apply Subtype.ext
  exact (contentSourceForward_backward D Sc i β a n (InductionAlong.Ind.tmul x b)).trans
    (sourceContent_project_tmul D Sc i β a n x b)

/-- The moving-strand map with source tensor over the unital content algebra.
The shifted target remains a fixed-content image, not yet its tensor comparison. -/
def contentTensorQ (ha : CyclotomicPolynomialParity D a) :
    contentSourceTensor D Sc i β a n →ₗ[Hn D Sc (n + 1 + 1)]
      qTargetContent D Sc i β a ha n :=
  (contentCornerQ D Sc i β a ha n).comp (contentSourceEquiv D Sc i β a n).toLinearMap

/-- The comparison preserves the prescribed moving-strand representative formula. -/
theorem contentTensorQ_representative (ha : CyclotomicPolynomialParity D a)
    (x : InductionAlong.Corner (appendAlgebra D Sc i (n + 1) :
      Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    (contentTensorQ D Sc i β a n ha (contentSourceRepresentative D Sc i β a n x b)).1 =
      InductionAlong.Ind.tmul
        (qPrependCorner D Sc i (n + 1) β
          (InductionAlong.cornerMul (contentMove_intertwines D Sc i (n + 1) β) x))
        (qCoefficientInsert D Sc i β a ha n b) := by
  change (contentCornerQ D Sc i β a ha n
    (contentSourceEquiv D Sc i β a n (contentSourceRepresentative D Sc i β a n x b))).1 = _
  rw [contentSourceEquiv_representative, contentCornerQ_tmul]

end OddMath.QuiverHecke
