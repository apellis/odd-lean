/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentShortFactor

/-!
# Projected short-shuffle image

The short-image inclusion needed by `DeformedMackeyBoundary.md` (4)–(5),
for ordinary cyclotomic polynomials. The left projector removes the unwanted
final-colour blocks before the surviving old entries are expanded by append PBW.
The old height is `n + 1`, including at `n = 0`. No full coefficient-superalgebra
extension or reverse inclusion is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Categorification.TypeA
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- A first-dot power acts on any matrix entry with the specified target. -/
theorem firstDot_pow_mul_entry (i : I) {n : ℕ} (s : Word I n)
    (r : Word I (n + 1)) (f : wordObj D Sc r ⟶ wordObj D Sc (prependWord i s))
    (m : ℕ) :
    affineFirstDot D Sc i n ^ m * FiniteHomMatrix.single (prependWord i s) r f =
      FiniteHomMatrix.single (prependWord i s) r (f ≫ inductionFirstDot D Sc i s ^ m) := by
  induction m with
  | zero => simp [End.one_def]
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, affineFirstDot, Finset.sum_mul,
      Finset.sum_eq_single s]
    · simp only [FiniteHomMatrix.single_mul_single]
      congr 1
      rw [pow_succ', End.mul_def, Category.assoc]
    · intro t _ ht
      exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
        (fun h => ht (prependWord_injective i n h)) _ _
    · simp

/-- The moving shuffle acts on any matrix entry with the specified target. -/
theorem prependShuffle_mul_entry (i : I) {n : ℕ} (u : PrependShuffle n)
    (s : Word I n) (r : Word I (n + 1))
    (f : wordObj D Sc r ⟶ wordObj D Sc (prependWord i s)) :
    prependShuffleElement D Sc i u * FiniteHomMatrix.single (prependWord i s) r f =
      FiniteHomMatrix.single (prependShuffleTarget i u s) r
        (f ≫ prependShuffleHom D Sc i u s) := by
  rw [prependShuffleElement, Finset.sum_mul, Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => ht (prependWord_injective i n h)) _ _
  · simp

/-- Expand the multiplier before applying its left corner projector. -/
theorem prependPBW_mul_move_sum (a : I → _root_.Polynomial k) (i : I) (n : ℕ)
    (u : PrependShuffle (n + 1)) (m : ℕ) :
    prependPBWTerm D Sc i u m 1 * appendMoveMatrix D Sc a i n =
      ∑ s : Word I (n + 1), FiniteHomMatrix.single (prependShuffleTarget i u s)
        (appendWord i s) (appendDottedMove D Sc a i s.1 m ≫ prependShuffleHom D Sc i u s) := by
  unfold prependPBWTerm
  have hp : prependAlgebra D Sc i (n + 1) 1 * appendMoveMatrix D Sc a i n =
      appendMoveMatrix D Sc a i n := by
    rw [appendMoveMatrix, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    let w : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (prependWord i s) :=
      appendW D Sc a i s.1
    change prependLinear D Sc i (n + 1)
      (∑ t : Word I (n + 1), FiniteHomMatrix.single t t (𝟙 _)) *
        FiniteHomMatrix.single (prependWord i s) (appendWord i s) w =
          FiniteHomMatrix.single (prependWord i s) (appendWord i s) w
    rw [map_sum, Finset.sum_mul, Finset.sum_eq_single s]
    · rw [prependLinear_single, FiniteHomMatrix.single_mul_single]
      have hid : prependHom D Sc i s s (𝟙 _) = 𝟙 _ :=
        MonoidalSupercategory.whiskerLeft_id (R := k) ((pres D Sc).obj (ob D [i]))
          (wordObj D Sc s)
      rw [hid, Category.comp_id]
    · intro t _ ht
      rw [prependLinear_single]
      exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
        (fun h => ht (prependWord_injective i _ h)) _ _
    · simp
  rw [mul_assoc, hp, appendMoveMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  let w : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (prependWord i s) :=
    appendW D Sc a i s.1
  change (_ * _) * FiniteHomMatrix.single (prependWord i s) (appendWord i s) w = _
  rw [mul_assoc, firstDot_pow_mul_entry, prependShuffle_mul_entry]
  simp only [inductionFirstDot_eq_dotE]
  rfl
/-- The projected short entry vanishes unless the final old colour is the moving colour. -/
theorem projected_short_entry_ne (a : I → _root_.Polynomial k) (i j : I) {n : ℕ}
    (u : PrependShuffle (n + 1)) (hu : u ≠ longPrependShuffle (n + 1))
    (m : ℕ) (s : Word I n) (hj : j ≠ i) :
    appendAlgebra D Sc i (n + 1) 1 *
      FiniteHomMatrix.single (prependShuffleTarget i u (appendWord j s))
        (appendWord i (appendWord j s))
        (appendDottedMove D Sc a i (s.1 ++ [j]) m ≫
          prependShuffleHom D Sc i u (appendWord j s)) = 0 := by
  obtain ⟨h, _⟩ := appendDottedMove_short_factor D Sc a n u hu i j s.1 s.2 m
  let f : wordObj D Sc (appendWord i (appendWord j s)) ⟶
      wordObj D Sc (prependWord i (appendWord j s)) :=
    appendDottedMove D Sc a i (s.1 ++ [j]) m
  change _ * FiniteHomMatrix.single _ _ (f ≫ _) = _
  have he := single_comp_cl_congr D Sc
    (r := appendWord i (appendWord j s)) (s := prependWord i (appendWord j s))
    (t := prependShuffleTarget i u (appendWord j s))
    (t' := appendWord j (prependShortOldTarget i u s)) f (sChain_pl _ _) h
  change _ * FiniteHomMatrix.single _ _ (f ≫ cl D Sc _ _ _ _) = _
  rw [he]
  exact appendOne_mul_single_of_ne D Sc hj _ _ _

/-- The surviving entry is fixed by the left projector. -/
theorem projected_short_entry_self (a : I → _root_.Polynomial k) (i : I) {n : ℕ}
    (u : PrependShuffle (n + 1)) (hu : u ≠ longPrependShuffle (n + 1))
    (m : ℕ) (s : Word I n) :
    appendAlgebra D Sc i (n + 1) 1 * appendShortEntry D Sc a i u m s =
      appendShortEntry D Sc a i u m s := by
  rw [appendShortEntry_factor D Sc a i u hu, ← mul_assoc, ← map_mul, one_mul]

/-- The whole left-projected multiplier is the sum of its surviving entries. -/
theorem projected_short_multiplier_sum (a : I → _root_.Polynomial k) (i : I) (n : ℕ)
    (u : PrependShuffle (n + 1)) (hu : u ≠ longPrependShuffle (n + 1)) (m : ℕ) :
    appendAlgebra D Sc i (n + 1) 1 *
      (prependPBWTerm D Sc i u m 1 * appendMoveMatrix D Sc a i n) =
        ∑ s : Word I n, appendShortEntry D Sc a i u m s := by
  rw [prependPBW_mul_move_sum, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.ofBijective _ (appendWord_pair_bijective n))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single i]
  · exact projected_short_entry_self D Sc a i u hu m s
  · intro j _ hj
    exact projected_short_entry_ne D Sc a i j u hu m s hj
  · simp

/-- Old PBW coefficients pass the final crossing with its parity twist. -/
theorem append_old_mul_crossing_mem (i : I) (n : ℕ) (y : Hn D Sc (n + 1))
    (hy : y * appendAlgebra D Sc i n 1 = y) :
    appendAlgebra D Sc i (n + 1) y * affineLastCrossing D Sc i i n ∈
      (appendLeftSum D Sc i n).range := by
  have htw (r : Hn D Sc n) :
      appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n r) *
          affineLastCrossing D Sc i i n =
        affineLastCrossing D Sc i i n *
          appendAlgebra D Sc i (n + 1)
            (appendAlgebra D Sc i n
              (homMatrixTwist D Sc n (D.parity i * D.parity i) r)) := by
    induction r using SuperBimodule.alg_induction_on (affineParity D Sc n) with
    | zero => simp
    | add r s hr hs => simp only [map_add, add_mul, mul_add, hr, hs]
    | hom p r hr =>
        rw [homMatrixTwist_of_affineParity D Sc _ _ _ _ hr,
          map_smul, map_smul, mul_smul_comm,
          Supercategory.sign_mul, Int.cast_smul_eq_zsmul]
        simpa only [Supercategory.koszulSign_comm (D.parity i * D.parity i) p]
          using affineLastCrossing_intertwines D Sc i i n hr
  obtain ⟨b, hb⟩ := appendExpansion_exists D Sc i n ⟨y, hy⟩
  change appendExpansion D Sc i n b = y at hb
  rw [← hb]
  clear hb hy y
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, map_add, add_mul]
      exact add_mem hf hg
  | single q b =>
      rcases q with ⟨u, m⟩
      obtain ⟨j, rfl⟩ := (appendRunEquiv n).surjective u
      refine ⟨Finsupp.single (j, m)
        (appendAlgebra D Sc i n
          (homMatrixTwist D Sc n (D.parity i * D.parity i) b)), ?_⟩
      simp only [appendLeftSum_single, appendExpansion_single,
        appendRunEquiv_apply, appendPBWTerm, map_mul, mul_assoc, htw]

/-- The projected short multiplier has a concrete finite left-crossing expansion. -/
theorem projected_short_multiplier_factor (a : I → _root_.Polynomial k) (i : I) (n : ℕ)
    (u : PrependShuffle (n + 1)) (hu : u ≠ longPrependShuffle (n + 1)) (m : ℕ) :
    ∃ f : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1),
      appendAlgebra D Sc i (n + 1) 1 *
        (prependPBWTerm D Sc i u m 1 * appendMoveMatrix D Sc a i n) =
          appendLeftSum D Sc i n f := by
  suffices hmem : appendAlgebra D Sc i (n + 1) 1 *
      (prependPBWTerm D Sc i u m 1 * appendMoveMatrix D Sc a i n) ∈
        (appendLeftSum D Sc i n).range by
    obtain ⟨f, hf⟩ := hmem
    exact ⟨f, hf.symm⟩
  rw [projected_short_multiplier_sum D Sc a i n u hu]
  apply AddSubgroup.sum_mem
  intro s _
  rw [appendShortEntry_factor D Sc a i u hu]
  apply append_old_mul_crossing_mem
  rw [appendAlgebra_one_eq_sum, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => ht (appendWord_injective i n h).symm) _ _
  · simp

/-- The prescribed moving map sends every short source into the prescribed crossing range. -/
theorem appendContentP_short_mem (a : I → _root_.Polynomial k) (n : ℕ)
    (β : Multiset I) (i : I) (ha : CyclotomicPolynomialParity D a)
    (z : appendContentSource D Sc a n β i) (hz : z ∈ appendContentShort D Sc a n β i) :
    appendContentP D Sc a n β i ha z ∈
      (appendContentMackeyTarget D Sc a n β i ha).F.range :=
  appendContentP_short_mem_of_factorizations D Sc a n β i ha
    (fun u hu m => projected_short_multiplier_factor D Sc a i n u hu m) z hz

end OddMath.QuiverHecke
