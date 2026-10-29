/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentCorner
import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyRho

/-!
# The append Mackey map on a cyclotomic content corner

This instantiates the source coefficient module of `AppendMackeySource.md` §4 and
restricts the map to the left append idempotent, as required by
`DeformedMackeyBoundary.md` (1). The cyclotomic annihilation and constant-parity
conditions are proved for the content corner, not supplied as hypotheses.
The unchanged right coefficient action satisfies the source transport field `P_r`.
These are ordinary cyclotomic polynomial coefficients; no exterior deformation is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Categorification.InductionAlong Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
open SKM (zsign)
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I) (i : I)

/-- The parity of the moving cyclotomic crossing on content `β`. -/
def appendContentParity : ZMod 2 :=
  (a i).natDegree • D.parity i + D.parity i * (β.map D.parity).sum

omit [Fintype I] in
/-- The corrected source-dot sign depends only on content, not on the cutoff. -/
@[simp] theorem appendSourceSign_contentParity :
    appendSourceSign D a i (appendContentParity D a β i) =
      D.parity i * (β.map D.parity).sum := by
  simp [appendSourceSign, appendContentParity]

omit [Fintype I] in
theorem appendQ_eq_contentParity (t : Word I (n + 1)) (ht : wordContent t = β) :
    appendQ D a i t.1 = appendContentParity D a β i := by
  subst β
  rfl

/-- The old cyclotomic ideal annihilates its content corner. -/
theorem contentCorner_cyclotomic_smul (r : Hn D Sc (n + 1))
    (hr : r ∈ cyclotomicIdeal D Sc a n) (m : CyclotomicContentCorner D Sc a n β) :
    r • m = 0 := by
  apply contentCornerVal_injective D Sc a n β
  change cyclotomicMk D Sc a n r * contentCornerVal D Sc a n β m = 0
  have h : cyclotomicMk D Sc a n r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [h, zero_mul]

/-- A word of the wrong content acts by zero on the corner. -/
theorem contentCorner_word_smul_of_ne (t : Word I (n + 1))
    (ht : wordContent t ≠ β) (m : CyclotomicContentCorner D Sc a n β) :
    FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t)) • m = 0 := by
  have he : FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t)) *
      contentIdempotent D Sc (n + 1) β = 0 := by
    unfold contentIdempotent FiniteHomMatrix.localUnit
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro s hs
    apply FiniteHomMatrix.single_mul_single_of_ne
    intro h
    subst s
    exact ht (Finset.mem_filter.mp hs).2
  apply contentCornerVal_injective D Sc a n β
  change cyclotomicMk D Sc a n _ * contentCornerVal D Sc a n β m = 0
  rw [← contentCornerVal_e_mul D Sc a n β m, ← mul_assoc]
  change (cyclotomicMk D Sc a n _ * cyclotomicMk D Sc a n _) * _ = 0
  rw [← map_mul, he, map_zero, zero_mul]

/-- The constant-parity condition needed for `appendMackeyMap`. -/
theorem contentCorner_appendQ_smul (t : Word I (n + 1))
    (ht : appendQ D a i t.1 ≠ appendContentParity D a β i)
    (m : CyclotomicContentCorner D Sc a n β) :
    FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t)) • m = 0 :=
  contentCorner_word_smul_of_ne D Sc a n β t
    (fun h => ht (appendQ_eq_contentParity D a n β i t h)) m

local notation "B" => CyclotomicContentCorner D Sc a n β
local notation "eps" => appendContentParity D a β i
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "L" => Ind B (prependTwist D Sc i n eps)

/-- The left append-idempotent part of twisted prepend induction. -/
def appendContentSource : AddSubgroup L where
  carrier := {z | (ψ 1 : Hn D Sc (n + 1 + 1)) • z = z}
  zero_mem' := smul_zero _
  add_mem' hz hw := (smul_add _ _ _).trans (congrArg₂ (· + ·) hz hw)
  neg_mem' hz := (smul_neg _ _).trans (congrArg Neg.neg hz)

variable (ha : CyclotomicPolynomialParity D a)

/-- The prescribed multiplier `z ⊗ b ↦ z W ⊗ b`, on the two content corners. -/
def appendContentP : appendContentSource D Sc a n β i →+
    appendTensorFixed D Sc i n B :=
  AddMonoidHom.codRestrict
    ((appendMackeyMap D Sc (i := i) (n := n) (ε := eps) (N := B) ha (contentCorner_cyclotomic_smul D Sc a n β)
      (contentCorner_appendQ_smul D Sc a n β i)).toAddMonoidHom.comp
        (appendContentSource D Sc a n β i).subtype) _ fun z => by
    change (ψ 1 : Hn D Sc (n + 1 + 1)) • _ = _
    let P := appendMackeyMap D Sc (i := i) (n := n) (ε := eps) (N := B) ha (contentCorner_cyclotomic_smul D Sc a n β)
      (contentCorner_appendQ_smul D Sc a n β i)
    exact (P.map_smul (ψ 1) z.1).symm.trans (congrArg P z.2)

/-- The unchanged right coefficient action on the source corner. -/
def appendContentSourceRightMul (b : B) :
    appendContentSource D Sc a n β i →+ appendContentSource D Sc a n β i :=
  AddMonoidHom.codRestrict
    ((Ind.map (φ := prependTwist D Sc i n eps)
      (appendCoefficientMulRight D Sc n B b)).toAddMonoidHom.comp
        (appendContentSource D Sc a n β i).subtype) _ fun z => by
    change (ψ 1 : Hn D Sc (n + 1 + 1)) • _ = _
    let R := Ind.map (φ := prependTwist D Sc i n eps) (appendCoefficientMulRight D Sc n B b)
    exact (R.map_smul (ψ 1) z.1).symm.trans (congrArg R z.2)

/-- The source transport field `P_r`, with the right action of
`appendContentMackeyTarget` and no extra annihilation assumptions. -/
theorem appendContentP_rightMul (b : B) (z : appendContentSource D Sc a n β i) :
    appendContentP D Sc a n β i ha (appendContentSourceRightMul D Sc a n β i b z) =
      appendTensorRightMul D Sc i n B b (appendContentP D Sc a n β i ha z) := by
  apply Subtype.ext
  let P := appendMackeyMap D Sc (i := i) (n := n) (ε := eps) (N := B) ha (contentCorner_cyclotomic_smul D Sc a n β)
    (contentCorner_appendQ_smul D Sc a n β i)
  change P (Ind.map (appendCoefficientMulRight D Sc n B b) z.1) =
    Ind.map (appendCoefficientMulRight D Sc n B b) (P z.1)
  dsimp only [P]
  induction z.1 using Ind.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => rw [Ind.map_tmul, appendMackeyMap_tmul, appendMackeyMap_tmul, Ind.map_tmul]

/-- The first-dot operator with the constant content sign. -/
def appendContentRho : appendContentSource D Sc a n β i →+
    appendContentSource D Sc a n β i :=
  zsign ℤ (appendSourceSign D a i eps) • AddMonoidHom.codRestrict
    ((appendSourceDot D Sc i n eps (contentCornerParity D Sc a n β i ha).toAddMonoidHom
      (contentCornerParity_smul D Sc a n β i ha)).toAddMonoidHom.comp
        (appendContentSource D Sc a n β i).subtype) (appendContentSource D Sc a n β i) fun z => by
    change (ψ 1 : Hn D Sc (n + 1 + 1)) • _ = _
    let R := appendSourceDot D Sc i n eps (contentCornerParity D Sc a n β i ha).toAddMonoidHom
      (contentCornerParity_smul D Sc a n β i ha)
    exact (R.map_smul (ψ 1) z.1).symm.trans (congrArg R z.2)

/-- The exact source transport field `P_ρ` for the cyclotomic content corner. -/
theorem appendContentP_rho (z : appendContentSource D Sc a n β i) :
    appendContentP D Sc a n β i ha (appendContentRho D Sc a n β i ha z) =
      (appendContentMackeyTarget D Sc a n β i ha).Rt
        (appendContentP D Sc a n β i ha z) := by
  apply Subtype.ext
  let P := appendMackeyMap D Sc (i := i) (n := n) (ε := eps) (N := B) ha
    (contentCorner_cyclotomic_smul D Sc a n β) (contentCorner_appendQ_smul D Sc a n β i)
  let θ := (contentCornerParity D Sc a n β i ha).toAddMonoidHom
  let hθ := contentCornerParity_smul D Sc a n β i ha
  change P (zsign ℤ (appendSourceSign D a i eps) • appendSourceDot D Sc i n eps θ hθ z.1) =
    appendTensorRightDot D Sc i n B θ hθ (P z.1)
  have h := appendMackeyMap_appendSourceDot D Sc i n eps θ hθ ha
    (contentCorner_cyclotomic_smul D Sc a n β) (contentCorner_appendQ_smul D Sc a n β i) z.1
  change P (appendSourceDot D Sc i n eps θ hθ z.1) =
    zsign ℤ (appendSourceSign D a i eps) • appendTensorRightDot D Sc i n B θ hθ (P z.1) at h
  rw [map_zsmul, h, smul_smul, ← zsign_add_eq, CharTwo.add_self_eq_zero]
  simp [zsign]

end OddMath.QuiverHecke
