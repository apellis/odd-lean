/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendEquivalence

/-!
# Balanced append coordinates

Mirror of `PrependTensorCoordinates.lean` for the append induction: the whole
affine append-corner coordinates descend to the balanced tensor product with any
unital left old-algebra module. `appendTensorEquiv` is additive, prescribed on
representatives, and both round trips use `appendCoordinateEquiv`, not flatness.
See `docs/Nondegeneracy/AppendCoordinates.md` §3.
-/

noncomputable section
open Categorification
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (n : ℕ) (M : Type w) [AddCommGroup M] [Module (Hn D Sc n) M]
local notation "C" =>
  InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n+1))
local notation "T" =>
  InductionAlong.Ind M (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n+1))
/-- The finite sum of the prescribed elementary tensors. -/
def appendTensorForward : ((AppendShuffleAt n × ℕ) →₀ M) →+ T :=
  Finsupp.liftAddHom fun q =>
    { toFun := fun y => InductionAlong.Ind.tmul (appendPBWCorner D Sc i q.1 q.2 1) y
      map_zero' := InductionAlong.Ind.tmul_zero _
      map_add' := InductionAlong.Ind.tmul_add _ }
/-- The forward map is the literal finite sum, including multiterm families. -/
theorem appendTensorForward_apply (x : (AppendShuffleAt n × ℕ) →₀ M) :
    appendTensorForward D Sc i n M x =
      x.sum (fun q y => InductionAlong.Ind.tmul (appendPBWCorner D Sc i q.1 q.2 1) y) :=
  Finsupp.liftAddHom_apply _ _

/-- Balanced coordinate extraction using the proved right-old-algebra law. -/
def appendTensorBackward : T →+ ((AppendShuffleAt n × ℕ) →₀ M) :=
  InductionAlong.Ind.liftAdd
    (fun z y => Finsupp.mapRange (fun b : Hn D Sc n => b • y) (zero_smul _ y)
      ((appendCoordinateEquiv D Sc i n).symm z))
    (by intros; ext q; simp [add_smul])
    (by intros; ext q; simp [smul_add])
    (by intros; ext q; simp [appendCoordinateEquiv_symm_right, mul_smul])
@[simp] theorem appendTensorForward_single (q : AppendShuffleAt n × ℕ) (y : M) :
    appendTensorForward D Sc i n M (Finsupp.single q y) =
      InductionAlong.Ind.tmul (appendPBWCorner D Sc i q.1 q.2 1) y :=
  Finsupp.liftAddHom_apply_single _ _ _
@[simp] theorem appendTensorBackward_tmul (z : C) (y : M) (q : AppendShuffleAt n × ℕ) :
    appendTensorBackward D Sc i n M (InductionAlong.Ind.tmul z y) q =
      (appendCoordinateEquiv D Sc i n).symm z q • y := rfl

/-- Extracting a finite tensor expansion recovers its coefficients. -/
theorem appendTensorBackward_forward (x : (AppendShuffleAt n × ℕ) →₀ M) :
    appendTensorBackward D Sc i n M (appendTensorForward D Sc i n M x) = x := by
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add q y x _ _ hx =>
    rw [map_add, map_add, hx, appendTensorForward_single]
    congr 1
    ext p
    rw [appendTensorBackward_tmul, appendCoordinateEquiv_symm_apply]
    change appendCoefficients D Sc i n (appendPBWTerm D Sc i q.1 q.2 1) p • y = _
    rw [appendCoefficients_term]
    by_cases h : q = p
    · subst p; simp
    · simp [Finsupp.single_eq_of_ne' h]

/-- Old-algebra coefficients transfer to the module by balancing. -/
theorem appendTensorForward_coefficients (b : (AppendShuffleAt n × ℕ) →₀ Hn D Sc n) (y : M) :
    appendTensorForward D Sc i n M
      (Finsupp.mapRange (fun c : Hn D Sc n => c • y) (zero_smul _ y) b) =
      InductionAlong.Ind.tmul (appendCoordinateEquiv D Sc i n b) y := by
  induction b using Finsupp.induction with
  | zero => simp [InductionAlong.Ind.zero_tmul]
  | @single_add q c b _ _ hb =>
    rw [Finsupp.mapRange_add (fun a b => add_smul a b y), map_add,
      map_add, InductionAlong.Ind.add_tmul, hb]
    congr 1
    rw [Finsupp.mapRange_single, appendTensorForward_single,
      ← InductionAlong.Ind.op_smul_tmul]
    congr 1
    apply Subtype.ext
    change appendPBWTerm D Sc i q.1 q.2 1 * appendAlgebra D Sc i n c =
      appendExpansion D Sc i n (Finsupp.single q c)
    rw [appendExpansion_single, ← appendPBWTerm_right, one_mul]

/-- Reassembling extracted coordinates recovers every balanced tensor. -/
theorem appendTensorForward_backward (t : T) :
    appendTensorForward D Sc i n M (appendTensorBackward D Sc i n M t) = t := by
  induction t using InductionAlong.Ind.induction_on with
  | zero => simp
  | add t s ht hs => simp [ht, hs]
  | tmul z y =>
    change appendTensorForward D Sc i n M
      (Finsupp.mapRange (fun c : Hn D Sc n => c • y) (zero_smul _ y)
        ((appendCoordinateEquiv D Sc i n).symm z)) = _
    rw [appendTensorForward_coefficients, LinearEquiv.apply_symm_apply]

/-- Explicit additive coordinates on the existing balanced induction quotient. -/
def appendTensorEquiv : ((AppendShuffleAt n × ℕ) →₀ M) ≃+ T where
  toFun := appendTensorForward D Sc i n M
  invFun := appendTensorBackward D Sc i n M
  left_inv := appendTensorBackward_forward D Sc i n M
  right_inv := appendTensorForward_backward D Sc i n M
  map_add' := map_add _
end OddMath.QuiverHecke
