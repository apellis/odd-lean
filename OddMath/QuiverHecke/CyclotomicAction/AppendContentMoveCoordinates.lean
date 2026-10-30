/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentBoundary
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContent
import OddMath.QuiverHecke.AppendShuffleRuns

/-!
# Moving-chain tensors and their prepend coordinates

The source lift needed for the longest-coset calculation in
`DeformedBoundaryDivision.md` (6). The chain is the prescribed `contentMove`;
its tensor belongs to the existing append content source. Extraction retains
both the twisted old coefficient and corrected-rho degree sign.

The filtration lemmas discard lower-crossing terms in the full moving row.
The canonical word is identified literally, without an unspecified braid unit.
Evaluation of the chain's leading polynomial and its total sign remains open.
-/
noncomputable section
open CategoryTheory StringDiagrams Categorification Categorification.InductionAlong
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Twisted balancing applies the old parity involution before the coefficient action. -/
theorem prependTwistCoordinates_symm_tmul (i : I) (n : ℕ) (ε : ZMod 2)
    (N : Type w) [AddCommGroup N] [Module (Hn D Sc (n + 1)) N]
    (z : InductionAlong.Corner (prependTwist D Sc i n ε)) (b : N)
    (q : PrependShuffle (n + 1) × ℕ) :
    (prependTwistCoordinates D Sc i n ε N).symm (Ind.tmul z b) q =
      homMatrixTwist D Sc (n + 1) ε
        (prependCoefficients D Sc i (n + 1) z.1 q) • b := by
  change (toTwistModule D Sc (n + 1) ε N).symm
    (prependTensorBackward D Sc i (n + 1) (TwistModule D Sc (n + 1) ε N)
      (prependTwistEquiv D Sc i n ε N (Ind.tmul z b)) q) = _
  rw [prependTwistEquiv_tmul, prependTensorBackward_tmul,
    prependCoordinateEquiv_symm_apply]
  rfl

/-- The prescribed moving chain lies in the right prepend corner. -/
theorem contentMove_mul_prependOne (i : I) (n : ℕ) (β : Multiset I) :
    contentMove D Sc i n β * prependAlgebra D Sc i n 1 =
      contentMove D Sc i n β := by
  rw [contentMove, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  change _ * prependLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ) = _
  rw [FiniteHomMatrix.localUnit, map_sum, Finset.mul_sum, Finset.sum_eq_single s]
  · change _ * prependLinear D Sc i n (FiniteHomMatrix.single s s (𝟙 _)) = _
    rw [prependLinear_single]
    have hid : prependHom D Sc i s s (𝟙 _) = 𝟙 _ := by
      convert MonoidalSupercategory.whiskerLeft_id (R := k)
        ((pres D Sc).obj (ob D [i])) (wordObj D Sc s) using 1 <;> rfl
    rw [hid, FiniteHomMatrix.single_mul_single, Category.id_comp]
  · intro t ht hts
    change _ * prependLinear D Sc i n (FiniteHomMatrix.single t t (𝟙 _)) = 0
    rw [prependLinear_single]
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hts (prependWord_injective i n h.symm)) _ _
  · simp

/-- The prescribed moving chain lies in the left append corner. -/
theorem appendOne_mul_contentMove (i : I) (n : ℕ) (β : Multiset I) :
    appendAlgebra D Sc i n 1 * contentMove D Sc i n β =
      contentMove D Sc i n β := by
  rw [contentMove, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => appendOne_mul_single D Sc i s _ _

variable (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I) (i : I)
local notation "B" => CyclotomicContentCorner D Sc a n β
local notation "eps" => appendContentParity D a β i

/-- The original moving chain in the twisted prepend corner. -/
def appendContentMoveCorner : InductionAlong.Corner (prependTwist D Sc i n eps) :=
  ⟨contentMove D Sc i (n + 1) β, by
    change contentMove D Sc i (n + 1) β * prependTwist D Sc i n eps 1 = _
    rw [prependTwist_one, contentMove_mul_prependOne]⟩

/-- The moving-chain tensor in the prescribed source, with its right coefficient unchanged. -/
def appendContentMoveLift (b : B) : appendContentSource D Sc a n β i :=
  ⟨Ind.tmul (appendContentMoveCorner D Sc a n β i) b, by
    change appendAlgebra D Sc i (n + 1) 1 • _ = _
    rw [Ind.smul_tmul]
    congr 1
    apply Subtype.ext
    exact appendOne_mul_contentMove D Sc i (n + 1) β⟩

/-- Exact extraction of the moving-chain tensor, before evaluation of its affine coefficients. -/
theorem appendContentMoveLift_extract (b : B) (m : ℕ) :
    appendContentRhoExtract D Sc a n β i (appendContentMoveLift D Sc a n β i b) m =
      (SKM.zsign ℤ (D.parity i * Multiset.sum (Multiset.map D.parity β))) ^ m •
        (homMatrixTwist D Sc (n + 1) eps
          (prependCoefficients D Sc i (n + 1) (contentMove D Sc i (n + 1) β)
            (longPrependShuffle (n + 1), m)) • b) := by
  change (SKM.zsign ℤ (D.parity i * Multiset.sum (Multiset.map D.parity β))) ^ m •
    ((prependTwistCoordinates D Sc i n eps B).symm
    (Ind.tmul (appendContentMoveCorner D Sc a n β i) b) _) = _
  rw [prependTwistCoordinates_symm_tmul]
  rfl
end OddMath.QuiverHecke

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Lower-crossing diagrams are spanned by lower-length prepend basis elements. -/
theorem low_le_span_prepend (i : I) (s t : List I) (N : ℕ) :
    Low D Sc (i :: s) t N ≤
      Submodule.span k (prependElt D Sc ''
        {x : PrependIdx i s t | length (s.length + 1) x.perm < N}) := by
  let S := Submodule.span k (prependElt D Sc ''
    {x : PrependIdx i s t | length (s.length + 1) x.perm < N})
  have he : ∀ d, ∀ y : NFIdx (i :: s) t,
      length (s.length + 1) y.1.2 = d → d < N → basisNF D Sc (i :: s) t y ∈ S := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro y hy hd
      obtain ⟨c, hc, hm⟩ := exists_unit_prependElt D Sc y
      have hlow : Submodule.span k
          (basisNF D Sc (i :: s) t ''
            {z | length (s.length + 1) z.1.2 < length (s.length + 1) y.1.2}) ≤ S := by
        apply Submodule.span_le.mpr
        rintro _ ⟨z, hz, rfl⟩
        exact ih _ (hy ▸ hz) z rfl (lt_trans (hy ▸ hz) hd)
      have hp : length (s.length + 1) (PrependIdx.leadEquiv.symm y).perm < N := by
        have h := congrArg (fun z : NFIdx (i :: s) t => z.1.2)
          (PrependIdx.leadEquiv.apply_symm_apply y)
        change (PrependIdx.leadEquiv.symm y).perm = y.1.2 at h
        rw [h, hy]
        exact hd
      have hb : prependElt D Sc (PrependIdx.leadEquiv.symm y) ∈ S :=
        Submodule.subset_span ⟨_, hp, rfl⟩
      obtain ⟨u, hu⟩ := hc
      have hEq : basisNF D Sc (i :: s) t y = (↑u⁻¹ : k) •
          (prependElt D Sc (PrependIdx.leadEquiv.symm y) -
            (prependElt D Sc (PrependIdx.leadEquiv.symm y) - c • basisNF D Sc (i :: s) t y)) := by
        rw [sub_sub_cancel, smul_smul, ← hu, Units.inv_mul, one_smul]
      rw [hEq]
      exact S.smul_mem _ (S.sub_mem hb (hlow hm))
  refine (low_le_span_nf D Sc (i :: s) t N).trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨y, hy, rfl⟩
  exact he _ y rfl hy

/-- Prepend coordinates of length at least the filtration bound vanish. -/
theorem prependBasis_repr_eq_zero_of_low (i : I) (s t : List I) (N : ℕ)
    (h : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t))
    (hh : h ∈ Low D Sc (i :: s) t N) (x : PrependIdx i s t)
    (hx : N ≤ length (s.length + 1) x.perm) :
    (prependBasis D Sc).repr h x = 0 := by
  apply repr_eq_zero_of_mem_span_image (prependBasis D Sc)
    (S := {x : PrependIdx i s t | length (s.length + 1) x.perm < N})
  · simpa only [prependBasis_apply] using low_le_span_prepend D Sc i s t N hh
  · exact not_lt.mpr hx
end OddMath.QuiverHecke

noncomputable section
open Categorification.TypeA Equiv
namespace OddMath.QuiverHecke

/-- The ascending full run is the cyclic rotation. -/
theorem runPerm_zero_eq_rotate (r : ℕ) : runPerm r 0 = finRotate (r + 1) := by
  ext x
  rw [runPerm_val r 0 (Nat.zero_le _)]
  by_cases hx : x.val < r
  · rw [finRotate_of_lt hx]
    simp [hx]
  · have he : x = Fin.last r := Fin.ext (by simp only [Fin.val_last]; omega)
    subst x
    simp

/-- The canonical long word is literally the descending run. -/
theorem canWord_longPrependShuffle (r : ℕ) :
    canWord (r + 1) (longPrependShuffle r).1⁻¹ = descRun 0 r := by
  have he : wordProd (r + 1) (descRun 0 r) = (finRotate (r + 1))⁻¹ := by
    rw [descRun, wordProd_reverse, ← runPerm_zero_eq_rotate]
    rfl
  change canWord (r + 1) (finRotate (r + 1))⁻¹ = _
  rw [← he]
  cases r with
  | zero =>
    apply List.length_eq_zero_iff.mp
    rw [descRun_zero, wordProd, List.map_nil, List.prod_nil,
      length_canWord, Categorification.TypeA.length_one]
  | succ r =>
    have hc : IsCode (0 :: idCode r) := ⟨by simp, isCode_idCode r⟩
    have hw : codeWord (0 :: idCode r) = descRun 0 (r + 1) := by simp [codeWord_cons]
    rw [← hw, canWord_wordProd_codeWord hc (by simp)]

/-- The full moving shuffle has one crossing per old strand. -/
theorem length_longPrependShuffle (r : ℕ) :
    length (r + 1) (longPrependShuffle r).1 = r := by
  rw [← length_inv, ← length_canWord, canWord_longPrependShuffle, length_descRun]

/-- The chronological long chain crosses old strands in their original order. -/
theorem cw_longPrependShuffle (r : ℕ) :
    cw (canWord (r + 1) (longPrependShuffle r).1⁻¹) =
      (List.range r).map PG.cross := by
  have hr : List.range' 0 r = List.range r := by
    induction r with
    | zero => rfl
    | succ r ih => simp only [List.range'_concat, List.range_succ, Nat.zero_add, one_mul, ih]
  simp [canWord_longPrependShuffle, cw, descRun, hr]
end OddMath.QuiverHecke
namespace OddMath.QuiverHecke

/-- Source crossing substitution at even colour: `τ = -T`. This is a
local polynomial identity, not an assertion about descended extraction. -/
theorem movingEven_sourceCrossing {R : Type*} [Ring R] (u v T : R) :
    SignedNilHecke.gEven u v T = (v - u) * (1 - (v - u) * (-T)) := by
  unfold SignedNilHecke.gEven SignedNilHecke.phiEven
  noncomm_ring

/-- Source crossing substitution at odd colour: `τ = T`. -/
theorem movingOdd_sourceCrossing {R : Type*} [Ring R] (u v T : R) :
    OddNilHecke.Intertwiner.element u v T =
      (v ^ 2 - u ^ 2) * ((v - u) - (v ^ 2 - u ^ 2) * T) := by
  unfold OddNilHecke.Intertwiner.element OddNilHecke.Intertwiner.squareDiff
  noncomm_ring

/-- Library even crossing coefficient, obtained from the source comparison. -/
theorem movingEven_crossingCoefficient {R : Type*} [Ring R] (u v T : R) :
    SignedNilHecke.gEven u v T = (v - u) + (v - u) ^ 2 * T := by
  rw [movingEven_sourceCrossing]
  noncomm_ring

/-- Library odd crossing coefficient, obtained from the source comparison. -/
theorem movingOdd_crossingCoefficient {R : Type*} [Ring R] (u v T : R) :
    OddNilHecke.Intertwiner.element u v T =
      (v ^ 2 - u ^ 2) * (v - u) - (v ^ 2 - u ^ 2) ^ 2 * T := by
  rw [movingOdd_sourceCrossing]
  noncomm_ring

open CategoryTheory StringDiagrams Categorification.TypeA
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Every lower-crossing error has zero full moving-shuffle coordinate,
including coordinates with nontrivial old permutations. -/
theorem prependBasis_long_repr_eq_zero_of_low (i : I) (s t : List I)
    (h : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t))
    (hh : h ∈ Low D Sc (i :: s) t s.length) (x : PrependIdx i s t)
    (hx : x.1.2.2.2 = longPrependShuffle s.length) :
    (prependBasis D Sc).repr h x = 0 := by
  apply prependBasis_repr_eq_zero_of_low D Sc i s t s.length h hh x
  rw [PrependIdx.perm, length_prependPermutation]
  simp only [hx, length_longPrependShuffle]
  omega
end OddMath.QuiverHecke
