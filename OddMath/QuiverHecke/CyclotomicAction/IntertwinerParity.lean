/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTensor
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import StringDiagrams.Super.Envelope

/-!
# The parity-shifted coefficient target of the moving-strand map

The coefficient target of KKO I, arXiv:1206.5933v2, Proposition 8.4 is
`Π_i^{p(β)} R^Λ(β)`. We use the existing superbimodule parity shift and its
canonical homogeneous isomorphism. `qCoefficientInsert_smul` proves the
semilinear identity needed to move the involution from the corner action
to that coefficient action. `parityCyclotomicContentQ` is the composition
of this transfer with the already constructed balanced map `contentQ`.

The coefficient parity is proved by `qCoefficientInsert_mem`. This file
does not yet equip the induced tensor carrier with its super grading or
construct the signed right `t_i` actions. In particular it does not assert
full Proposition 8.4, a superbimodule map, or any QP formula. The content
projection, finite-colour hypothesis and positive-height quotient indexing
are unchanged. Polynomial parity is used only for the coefficient grading.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The coefficient superbimodule in KKO I, Proposition 8.4. -/
def qCoefficient (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :=
  Envelope.piPow k (D.parity i * contentSumParity D β)
    (SuperBimodule.regular (cyclotomicParity D Sc a ha n))

instance qCoefficientModule (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    Module (Hn D Sc (n + 1)) (qCoefficient D Sc i β a ha n).toSVec where
  smul r b := (qCoefficient D Sc i β a ha n).lact (cyclotomicMk D Sc a n r) b
  one_smul b := by
    change (qCoefficient D Sc i β a ha n).lact (cyclotomicMk D Sc a n 1) b = b
    rw [map_one, SuperBimodule.lact_one]
    rfl
  mul_smul r s b := by
    change (qCoefficient D Sc i β a ha n).lact (cyclotomicMk D Sc a n (r * s)) b = _
    rw [map_mul, SuperBimodule.lact_mul]
    rfl
  smul_zero r := SVec.hom_map_zero _
  smul_add r b c := SVec.hom_map_add _ b c
  zero_smul b := by
    change (qCoefficient D Sc i β a ha n).lact (cyclotomicMk D Sc a n 0) b = 0
    rw [map_zero, map_zero]
    rfl
  add_smul r s b := by
    change (qCoefficient D Sc i β a ha n).lact (cyclotomicMk D Sc a n (r + s)) b = _
    rw [map_add, map_add]
    rfl

/-- The canonical coefficient insertion, with parity `p(i)p(β)`. -/
def qCoefficientInsert (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    CyclotomicAlgebra D Sc a n →ₗ[k] (qCoefficient D Sc i β a ha n).toSVec :=
  SVec.toLinearMap (Envelope.ζPow k (D.parity i * contentSumParity D β)
    (SuperBimodule.regular (cyclotomicParity D Sc a ha n))).inv.1

/-- The canonical insertion uses the existing parity-shift isomorphism. -/
@[simp] theorem qCoefficientInsert_apply (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (b : CyclotomicAlgebra D Sc a n) :
    qCoefficientInsert D Sc i β a ha n b =
      (Envelope.ζPow k (D.parity i * contentSumParity D β)
        (SuperBimodule.regular (cyclotomicParity D Sc a ha n))).inv.1 b := rfl

/-- The entrywise involution is the scalar sign on a homogeneous element. -/
theorem homMatrixTwist_of_affineParity (n : ℕ) (p q : ZMod 2) (r : Hn D Sc n)
    (hr : r ∈ affineParity D Sc n q) :
    homMatrixTwist D Sc n p r = Supercategory.sign k (p * q) • r := by
  classical
  rw [FiniteHomMatrix.eq_sum_single r, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [homMatrixTwist_single, Supercategory.twist_of_mem p (hr t)]
  exact FiniteHomMatrix.single_smul _ _ _ _

/-- Moving the involution from the corner action to the shifted coefficient. -/
theorem qCoefficientInsert_smul (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (r : Hn D Sc (n + 1))
    (b : CyclotomicAlgebra D Sc a n) :
    qCoefficientInsert D Sc i β a ha n (r • b) =
      homMatrixTwist D Sc (n + 1) (D.parity i * contentSumParity D β) r •
        qCoefficientInsert D Sc i β a ha n b := by
  induction r using SuperBimodule.alg_induction_on (affineParity D Sc (n + 1)) with
  | zero => simp
  | add r s hr hs => simp only [add_smul, map_add, hr, hs]
  | hom p r hr =>
    let V := SuperBimodule.regular (cyclotomicParity D Sc a ha n)
    let e := Envelope.ζPow k (D.parity i * contentSumParity D β) V
    have he : e.inv.1 ∈ Supercategory.parity (R := k) V.toSVec
        (qCoefficient D Sc i β a ha n).toSVec (D.parity i * contentSumParity D β) :=
      SuperBimodule.mem_parity_iff.mp (Envelope.ζPow_inv_mem (R := k)
        (D.parity i * contentSumParity D β) V)
    have hf := (SuperBimodule.isHom_iff_of_mem he).mp e.inv.2
    have h := congrArg (fun f => f b)
      (hf.1 p (cyclotomicMk D Sc a n r) (cyclotomicMk_parity D Sc a ha n hr))
    rw [homMatrixTwist_of_affineParity D Sc _ _ _ _ hr]
    change _ = (qCoefficient D Sc i β a ha n).lact
      (cyclotomicMk D Sc a n (Supercategory.sign k
        ((D.parity i * contentSumParity D β) * p) • r))
      (qCoefficientInsert D Sc i β a ha n b)
    rw [map_smul (cyclotomicMk D Sc a n),
      map_smul (qCoefficient D Sc i β a ha n).lact]
    have hrb : V.lact (cyclotomicMk D Sc a n r) b = r • b := by
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
      rfl
    simp only [mul_comm p, SVec.comp_apply, SVec.smul_apply,
      hrb, qCoefficientInsert_apply, V, e] at h ⊢
    convert h using 1

open Categorification MulOpposite

@[simp] theorem homMatrixTwist_one (n : ℕ) (p : ZMod 2) :
    homMatrixTwist D Sc n p 1 = 1 := by
  have h := (homMatrixTwistAlgebra D Sc n p).map_mul 1 (homMatrixTwist D Sc n p 1)
  change homMatrixTwist D Sc n p (1 * homMatrixTwist D Sc n p 1) =
    homMatrixTwist D Sc n p 1 * homMatrixTwist D Sc n p (homMatrixTwist D Sc n p 1) at h
  simpa only [one_mul, homMatrixTwist_twice, mul_one] using h.symm

/-- The parity twist fixes the corner idempotent. -/
def qPrependCorner (i : I) (n : ℕ) (β : Multiset I) :
    InductionAlong.Corner (twistedPrepend D Sc i n β) →ₗ[Hn D Sc (n + 1)]
      InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) where
  toFun x := ⟨x.1, by
    change x.1 * prependAlgebra D Sc i n 1 = x.1
    have h := x.2
    change x.1 * prependAlgebra D Sc i n (homMatrixTwist D Sc n
      (D.parity i * contentSumParity D β) 1) = x.1 at h
    simpa only [homMatrixTwist_one] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical transfer to the actual parity-shifted coefficient carrier. -/
def qCoefficientTransfer (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    InductionAlong.Ind (CyclotomicAlgebra D Sc a n) (twistedPrepend D Sc i (n + 1) β)
      →ₗ[Hn D Sc (n + 1 + 1)]
    InductionAlong.Ind (qCoefficient D Sc i β a ha n).toSVec
      (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)) :=
  InductionAlong.Ind.lift
    (fun x b => InductionAlong.Ind.tmul (qPrependCorner D Sc i (n + 1) β x)
      (qCoefficientInsert D Sc i β a ha n b))
    (by intros; rw [map_add, InductionAlong.Ind.add_tmul])
    (by intros; rw [map_add, InductionAlong.Ind.tmul_add])
    (by
      intro x r b
      have h : qPrependCorner D Sc i (n + 1) β (op r • x) =
          op (homMatrixTwist D Sc (n + 1) (D.parity i * contentSumParity D β) r) •
            qPrependCorner D Sc i (n + 1) β x := rfl
      rw [h, InductionAlong.Ind.op_smul_tmul, qCoefficientInsert_smul])
    (by intros; rw [map_smul, InductionAlong.Ind.smul_tmul])

/-- The existing quotient-descended map, now with the coefficient shift in its target. -/
def parityCyclotomicContentQ (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :=
  (qCoefficientTransfer D Sc i β a ha n).comp (cyclotomicContentQ D Sc i n β a)

/-- The coefficient insertion has exactly the prescribed parity shift. -/
theorem qCoefficientInsert_mem (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (p : ZMod 2)
    (b : CyclotomicAlgebra D Sc a n) (hb : b ∈ cyclotomicParity D Sc a ha n p) :
    qCoefficientInsert D Sc i β a ha n b ∈
      (qCoefficient D Sc i β a ha n).toSVec.part
        ((D.parity i * contentSumParity D β) + p) := by
  rw [qCoefficientInsert_apply]
  let V := SuperBimodule.regular (cyclotomicParity D Sc a ha n)
  let e := Envelope.ζPow k (D.parity i * contentSumParity D β) V
  have he : e.inv.1 ∈ Supercategory.parity (R := k) V.toSVec
      (qCoefficient D Sc i β a ha n).toSVec (D.parity i * contentSumParity D β) :=
    SuperBimodule.mem_parity_iff.mp (Envelope.ζPow_inv_mem (R := k)
      (D.parity i * contentSumParity D β) V)
  have hb' : b ∈ V.toSVec.part p :=
    (SuperBimodule.mem_regularSVec_part_iff _).mpr hb
  have h := SVec.apply_mem_part he hb'
  simp only [add_comm] at h ⊢
  convert h using 1

/-- The refined map retains the actual moving-strand representative. -/
@[simp] theorem parityCyclotomicContentQ_tmul (i : I) (β : Multiset I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (x : InductionAlong.Corner
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    parityCyclotomicContentQ D Sc i β a ha n (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul
        (qPrependCorner D Sc i (n + 1) β
          (InductionAlong.cornerMul (contentMove_intertwines D Sc i (n + 1) β) x))
        (qCoefficientInsert D Sc i β a ha n b) := rfl

end OddMath.QuiverHecke
