/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.PrependEquivalence

/-!
# Balanced prepend coordinates

The explicit balanced extension (9) of `PrependCoordinates.md` descends the
whole affine corner coordinates to any unital left old-algebra module.
`prependTensorEquiv` is additive: no ground-ring action is installed on the
integral quotient. Both maps are prescribed on representatives, and both
round trips use the proved affine coordinate equivalence, not flatness.
The shifted cyclotomic specialization and its commuting right action are
provided in `PrependCoefficientCoordinates`.
-/

noncomputable section
open Categorification
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (n : ℕ) (M : Type w) [AddCommGroup M] [Module (Hn D Sc n) M]
local notation "C" => InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n+1))
local notation "T" => InductionAlong.Ind M (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n+1))
/-- The finite sum of the prescribed elementary tensors. -/
def prependTensorForward : ((PrependShuffle n × ℕ) →₀ M) →+ T :=
  Finsupp.liftAddHom fun q =>
    { toFun := fun y => InductionAlong.Ind.tmul (prependPBWCorner D Sc i q.1 q.2 1) y
      map_zero' := InductionAlong.Ind.tmul_zero _
      map_add' := InductionAlong.Ind.tmul_add _ }
/-- The forward map is the literal finite sum, including multiterm families. -/
theorem prependTensorForward_apply (x : (PrependShuffle n × ℕ) →₀ M) :
    prependTensorForward D Sc i n M x =
      x.sum (fun q y => InductionAlong.Ind.tmul (prependPBWCorner D Sc i q.1 q.2 1) y) :=
  Finsupp.liftAddHom_apply _ _

/-- Balanced coordinate extraction using the proved right-old-algebra law. -/
def prependTensorBackward : T →+ ((PrependShuffle n × ℕ) →₀ M) :=
  InductionAlong.Ind.liftAdd
    (fun z y => Finsupp.mapRange (fun b : Hn D Sc n => b • y) (zero_smul _ y)
      ((prependCoordinateEquiv D Sc i n).symm z))
    (by intros; ext q; simp [add_smul])
    (by intros; ext q; simp [smul_add])
    (by intros; ext q; simp [prependCoordinateEquiv_symm_right, mul_smul])
@[simp] theorem prependTensorForward_single (q : PrependShuffle n × ℕ) (y : M) :
    prependTensorForward D Sc i n M (Finsupp.single q y) =
      InductionAlong.Ind.tmul (prependPBWCorner D Sc i q.1 q.2 1) y :=
  Finsupp.liftAddHom_apply_single _ _ _
@[simp] theorem prependTensorBackward_tmul (z : C) (y : M) (q : PrependShuffle n × ℕ) :
    prependTensorBackward D Sc i n M (InductionAlong.Ind.tmul z y) q =
      (prependCoordinateEquiv D Sc i n).symm z q • y := rfl

/-- Extracting a finite tensor expansion recovers its coefficients. -/
theorem prependTensorBackward_forward (x : (PrependShuffle n × ℕ) →₀ M) :
    prependTensorBackward D Sc i n M (prependTensorForward D Sc i n M x) = x := by
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add q y x _ _ hx =>
    rw [map_add, map_add, hx, prependTensorForward_single]
    congr 1
    ext p
    rw [prependTensorBackward_tmul, prependCoordinateEquiv_symm_apply]
    change prependCoefficients D Sc i n (prependPBWTerm D Sc i q.1 q.2 1) p • y = _
    rw [prependCoefficients_term]
    by_cases h : q = p
    · subst p; simp
    · simp [Finsupp.single_eq_of_ne' h]

/-- Old-algebra coefficients transfer to the module by balancing. -/
theorem prependTensorForward_coefficients (b : (PrependShuffle n × ℕ) →₀ Hn D Sc n) (y : M) :
    prependTensorForward D Sc i n M
      (Finsupp.mapRange (fun c : Hn D Sc n => c • y) (zero_smul _ y) b) =
      InductionAlong.Ind.tmul (prependCoordinateEquiv D Sc i n b) y := by
  induction b using Finsupp.induction with
  | zero => simp [InductionAlong.Ind.zero_tmul]
  | @single_add q c b _ _ hb =>
    rw [Finsupp.mapRange_add (fun a b => add_smul a b y), map_add,
      map_add, InductionAlong.Ind.add_tmul, hb]
    congr 1
    rw [Finsupp.mapRange_single, prependTensorForward_single,
      ← InductionAlong.Ind.op_smul_tmul]
    congr 1
    apply Subtype.ext
    change prependPBWTerm D Sc i q.1 q.2 1 * prependAlgebra D Sc i n c =
      prependExpansion D Sc i n (Finsupp.single q c)
    rw [prependExpansion_single, ← prependPBWTerm_right, one_mul]

/-- Reassembling extracted coordinates recovers every balanced tensor. -/
theorem prependTensorForward_backward (t : T) :
    prependTensorForward D Sc i n M (prependTensorBackward D Sc i n M t) = t := by
  induction t using InductionAlong.Ind.induction_on with
  | zero => simp
  | add t s ht hs => simp [ht, hs]
  | tmul z y =>
    change prependTensorForward D Sc i n M
      (Finsupp.mapRange (fun c : Hn D Sc n => c • y) (zero_smul _ y)
        ((prependCoordinateEquiv D Sc i n).symm z)) = _
    rw [prependTensorForward_coefficients, LinearEquiv.apply_symm_apply]

/-- Explicit additive coordinates on the existing balanced induction quotient. -/
def prependTensorEquiv : ((PrependShuffle n × ℕ) →₀ M) ≃+ T where
  toFun := prependTensorForward D Sc i n M
  invFun := prependTensorBackward D Sc i n M
  left_inv := prependTensorBackward_forward D Sc i n M
  right_inv := prependTensorForward_backward D Sc i n M
  map_add' := map_add _
end OddMath.QuiverHecke
