/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentMackeyMap
import OddMath.QuiverHecke.CyclotomicAction.PrependTwistCoordinates
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Moving-shuffle extraction on the append content source

The source decomposition needed for `DeformedMackeyBoundary.md` (2) and (7),
in the ordinary cyclotomic polynomial setting. Coordinates are the proved
balanced prepend PBW coordinates, not an inverse chosen by dimension counting.
The full moving shuffle lands in the append corner at every old height.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Categorification.InductionAlong
open Categorification.TypeA Equiv
open scoped Classical
namespace OddMath.QuiverHecke

private theorem rotate_inv_block_inr (r : ℕ) (y : Fin r) :
    (finRotate (r + 1))⁻¹
        (blockEquiv (Nat.add_comm 1 r) (Sum.inr y)) = y.castSucc := by
  change (finRotate (r + 1)).symm _ = _
  apply (finRotate (r + 1)).symm_apply_eq.mpr
  change _ = (finRotate (r + 1)) ⟨y.val, by omega⟩
  rw [finRotate_of_lt y.isLt]
  apply Fin.ext
  change 1 + y.val = y.val + 1
  omega

/-- The inverse shuffle moves the first strand to the last position. -/
def longPrependShuffle (r : ℕ) : PrependShuffle r :=
  ⟨finRotate (r + 1), by
    constructor
    · intro x y hxy
      have hx := x.isLt
      have hy := y.isLt
      change x.val < y.val at hxy
      omega
    · intro x y hxy
      dsimp only
      rw [rotate_inv_block_inr, rotate_inv_block_inr]
      exact hxy⟩

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

omit [Fintype I] in
/-- The full moving shuffle has exactly the append target word. -/
theorem prependShuffleTarget_long (i : I) {r : ℕ} (s : Word I r) :
    prependShuffleTarget i (longPrependShuffle r) s = appendWord i s := by
  apply Subtype.ext
  change tgt (i :: s.1) (cw (canWord (r + 1) (finRotate (r + 1))⁻¹)) = s.1 ++ [i]
  refine List.ext_getElem (by simp [s.2]) ?_
  intro p hp₁ hp₂
  have hp : p < r + 1 := by simpa [s.2] using hp₁
  have hq := tgt_cw_getElem
    (validWord_canWord (r + 1) (finRotate (r + 1))⁻¹)
    (t := i :: s.1) (by simp [s.2]) ⟨p, hp⟩
  simp only [wordProd_canWord, inv_inv] at hq
  rw [hq]
  by_cases hpr : p < r
  · simp only [finRotate_of_lt hpr, List.getElem_cons_succ]
    rw [List.getElem_append_left (by simpa [s.2] using hpr)]
  · have he : p = r := by omega
    subst p
    simp only [finRotate_last', List.getElem_cons_zero]
    rw [List.getElem_append_right (by simp [s.2])]
    simp [s.2]

/-- The append projector fixes the moving crossing matrix. -/
theorem appendOne_mul_longPrependShuffleElement (i : I) (r : ℕ) :
    appendAlgebra D Sc i r 1 * prependShuffleElement D Sc i (longPrependShuffle r) =
      prependShuffleElement D Sc i (longPrependShuffle r) := by
  have hs (s : Word I r) (t : Word I (r + 1)) (ht : t = appendWord i s)
      (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc t) :
      appendAlgebra D Sc i r 1 * FiniteHomMatrix.single t (prependWord i s) f =
        FiniteHomMatrix.single t (prependWord i s) f := by
    subst t
    exact appendOne_mul_single D Sc i s (prependWord i s) f
  rw [prependShuffleElement, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => hs s _ (prependShuffleTarget_long i s) _

/-- All first-dot powers of the moving shuffle remain in the append corner. -/
theorem appendOne_mul_longPrependPBWTerm (i : I) (r m : ℕ) (b : Hn D Sc r) :
    appendAlgebra D Sc i r 1 * prependPBWTerm D Sc i (longPrependShuffle r) m b =
      prependPBWTerm D Sc i (longPrependShuffle r) m b := by
  simp only [prependPBWTerm, ← mul_assoc, appendOne_mul_longPrependShuffleElement]

variable (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I) (i : I)
local notation "B" => CyclotomicContentCorner D Sc a n β
local notation "eps" => appendContentParity D a β i
local notation "C" => (PrependShuffle (n + 1) × ℕ) →₀ B
local notation "L" => Ind B (prependTwist D Sc i n eps)
local notation "coord" => prependTwistCoordinates D Sc i n eps B

/-- Read the full moving-shuffle row of the balanced PBW coordinates.
These are input-first-dot coordinates, before the corrected-ρ sign normalization. -/
def appendContentLongExtract : appendContentSource D Sc a n β i →+ (ℕ →₀ B) :=
  (Finsupp.comapDomain.addMonoidHom
    (f := fun m : ℕ => (longPrependShuffle (n + 1), m))
    (fun _ _ h => congrArg Prod.snd h)).comp
      ((coord).symm.toAddMonoidHom.comp (appendContentSource D Sc a n β i).subtype)

/-- Extraction is the literal long-shuffle coefficient. -/
theorem appendContentLongExtract_apply (z : appendContentSource D Sc a n β i) (m : ℕ) :
    appendContentLongExtract D Sc a n β i z m =
      (coord).symm z.1 (longPrependShuffle (n + 1), m) := rfl

/-- A moving PBW tensor satisfies the left append projector without any cutoff assumption. -/
theorem appendContentLong_mem (m : ℕ) (b : B) :
    coord (Finsupp.single (longPrependShuffle (n + 1), m) b) ∈
      appendContentSource D Sc a n β i := by
  change appendAlgebra D Sc i (n + 1) 1 • _ = _
  rw [prependTwistCoordinates_single, Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  exact appendOne_mul_longPrependPBWTerm D Sc i (n + 1) m 1

/-- The prescribed moving crossing followed by input-first-dot powers. -/
def appendContentLongLift : (ℕ →₀ B) →+ appendContentSource D Sc a n β i :=
  Finsupp.liftAddHom fun m =>
    { toFun := fun b => ⟨coord (Finsupp.single (longPrependShuffle (n + 1), m) b),
        appendContentLong_mem D Sc a n β i m b⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun b c => Subtype.ext (by simp) }

/-- On each monomial the lift is the specified PBW tensor, not an arbitrary section. -/
theorem appendContentLongLift_single (m : ℕ) (b : B) :
    (appendContentLongLift D Sc a n β i (Finsupp.single m b)).1 =
      coord (Finsupp.single (longPrependShuffle (n + 1), m) b) := by
  exact congrArg Subtype.val (Finsupp.liftAddHom_apply_single _ m b)

/-- All long-shuffle coefficients are recovered, over the cyclotomic content ring. -/
theorem appendContentLongExtract_lift (f : ℕ →₀ B) :
    appendContentLongExtract D Sc a n β i (appendContentLongLift D Sc a n β i f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    ext l
    rw [appendContentLongExtract_apply, appendContentLongLift_single,
      AddEquiv.symm_apply_apply]
    simp [Finsupp.single_apply]

/-- The short subgroup consists of tensors with vanishing full moving-shuffle row. -/
def appendContentShort : AddSubgroup (appendContentSource D Sc a n β i) :=
  (appendContentLongExtract D Sc a n β i).ker

/-- The kernel criterion in the existing balanced coordinates. -/
theorem mem_appendContentShort_iff (z : appendContentSource D Sc a n β i) :
    z ∈ appendContentShort D Sc a n β i ↔
      ∀ m, (coord).symm z.1 (longPrependShuffle (n + 1), m) = 0 := by
  change appendContentLongExtract D Sc a n β i z = 0 ↔ _
  exact Finsupp.ext_iff

/-- Shortness is equivalent to a finite expansion supported away from the moving shuffle.
The equality is in the original balanced induction, retaining the append projector on `z`. -/
theorem appendContentShort_iff_expansion (z : appendContentSource D Sc a n β i) :
    z ∈ appendContentShort D Sc a n β i ↔
      ∃ f : C, (∀ m, f (longPrependShuffle (n + 1), m) = 0) ∧ coord f = z.1 := by
  rw [mem_appendContentShort_iff]
  constructor
  · intro h
    exact ⟨(coord).symm z.1, h, (coord).apply_symm_apply z.1⟩
  · rintro ⟨f, hf, he⟩ m
    rw [← he, AddEquiv.symm_apply_apply]
    exact hf m

/-- The prescribed moving lifts cover the source modulo the short subgroup. -/
theorem appendContentLong_cover (z : appendContentSource D Sc a n β i) :
    z - appendContentLongLift D Sc a n β i (appendContentLongExtract D Sc a n β i z) ∈
      appendContentShort D Sc a n β i := by
  change appendContentLongExtract D Sc a n β i _ = 0
  rw [map_sub, appendContentLongExtract_lift, sub_self]

/-- Independence of the prescribed moving lifts modulo the short subgroup. -/
theorem appendContentLongLift_short_iff (f : ℕ →₀ B) :
    appendContentLongLift D Sc a n β i f ∈ appendContentShort D Sc a n β i ↔ f = 0 := by
  change appendContentLongExtract D Sc a n β i (appendContentLongLift D Sc a n β i f) = 0 ↔ _
  rw [appendContentLongExtract_lift]

/-- The PBW expansion respects the unchanged right coefficient action. -/
theorem appendContentCoordinates_rightMul (b : B) (f : C) :
    Ind.map (φ := prependTwist D Sc i n eps) (appendCoefficientMulRight D Sc n B b)
        (coord f) =
      coord (Finsupp.mapRange (fun c : B => c * b) (zero_mul b) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.mapRange_zero]
  | add f g hf hg =>
    rw [map_add, LinearMap.map_add, hf, hg,
      Finsupp.mapRange_add (fun c d => add_mul c d b), map_add]
  | single q c =>
    rw [prependTwistCoordinates_single, Ind.map_tmul, Finsupp.mapRange_single,
      prependTwistCoordinates_single]
    rfl

/-- Extraction is right linear over the content corner, with no change of right action. -/
theorem appendContentLongExtract_rightMul (b : B) (z : appendContentSource D Sc a n β i) :
    appendContentLongExtract D Sc a n β i (appendContentSourceRightMul D Sc a n β i b z) =
      CyclotomicAction.BoundaryPolynomial.rsmul b (appendContentLongExtract D Sc a n β i z) := by
  have h := appendContentCoordinates_rightMul D Sc a n β i b ((coord).symm z.1)
  rw [AddEquiv.apply_symm_apply] at h
  ext m
  change (coord).symm
      (Ind.map (φ := prependTwist D Sc i n eps) (appendCoefficientMulRight D Sc n B b) z.1)
        (longPrependShuffle (n + 1), m) = _
  rw [h, AddEquiv.symm_apply_apply]
  rfl

/-- The specified lifts, not just their cosets, respect right coefficients. -/
theorem appendContentLongLift_rightMul (b : B) (f : ℕ →₀ B) :
    appendContentLongLift D Sc a n β i (CyclotomicAction.BoundaryPolynomial.rsmul b f) =
      appendContentSourceRightMul D Sc a n β i b (appendContentLongLift D Sc a n β i f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m c =>
    apply Subtype.ext
    change (appendContentLongLift D Sc a n β i
      (Finsupp.mapRange (fun c : B => c * b) (zero_mul b) (Finsupp.single m c))).1 =
        Ind.map (φ := prependTwist D Sc i n eps) (appendCoefficientMulRight D Sc n B b)
          (appendContentLongLift D Sc a n β i (Finsupp.single m c)).1
    rw [Finsupp.mapRange_single, appendContentLongLift_single, appendContentLongLift_single,
      appendContentCoordinates_rightMul, Finsupp.mapRange_single]

/-- The short subgroup is stable under the unchanged right coefficient action. -/
theorem appendContentShort_rightMul (b : B) (z : appendContentSource D Sc a n β i)
    (hz : z ∈ appendContentShort D Sc a n β i) :
    appendContentSourceRightMul D Sc a n β i b z ∈ appendContentShort D Sc a n β i := by
  change appendContentLongExtract D Sc a n β i _ = 0
  rw [appendContentLongExtract_rightMul, show appendContentLongExtract D Sc a n β i z = 0 from hz,
    map_zero]

end OddMath.QuiverHecke
