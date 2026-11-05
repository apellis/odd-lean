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

end OddMath.QuiverHecke
