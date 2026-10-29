/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.AppendShuffleRuns
import OddMath.QuiverHecke.CyclotomicAction.AppendCoordinates
import OddMath.QuiverHecke.CyclotomicAction.Square
import OddMath.QuiverHecke.CyclotomicAction.GlobalSlideAlgebra
import OddMath.QuiverHecke.CyclotomicAction.AppendEquivalence
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightDot

/-!
# Factorization of the append moving crossings through the last crossing

On the two-sided append corner, the moving crossing `c_j` of the appended strand to a
position `j` below the last old strand factors as `c_j = ψ(c'_j) τ`, where `τ` is the
equal-colour crossing of the last two strands and `c'_j` is the moving crossing one
level down. This is the identity `c_j = c'_j τ_n` of `AppendCoordinates.md` §4 at the
level of the finite Hom-matrix algebra (Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of
Lemma 8.1, mirror form).
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA MonoidalCategory
open scoped Classical

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- A matrix entry of a positioned word depends only on the word of generators. -/
theorem single_cl_congr {m : ℕ} {s t t' : Word I m} {gs gs' : List PG}
    (h : SChain s.1 (pl s.1 gs) t.1) (h' : SChain s.1 (pl s.1 gs') t'.1) (hg : gs = gs') :
    (FiniteHomMatrix.single t s (cl D Sc s.1 t.1 gs h) : Hn D Sc m) =
      FiniteHomMatrix.single t' s (cl D Sc s.1 t'.1 gs' h') := by
  subst hg
  obtain rfl : t = t' := Subtype.ext ((tgt_eq h).symm.trans (tgt_eq h'))
  rfl

/-- The ascending run one step longer ends with the crossing of the last two old strands. -/
theorem cw_range'_succ {n j : ℕ} (hj : j ≤ n) :
    cw (List.range' j (n + 1 - j)) = [PG.cross n] ++ cw (List.range' j (n - j)) := by
  rw [show n + 1 - j = (n - j) + 1 by omega, List.range'_concat, cw_append]
  simp only [cw, List.reverse_singleton, List.map_singleton,
    List.cons_append, List.nil_append]
  congr 2
  omega

/-- The appended moving crossing on a word with last old colour `a`, as the last crossing
followed by the moving crossing one level down. -/
theorem appendShuffleHom_castSucc (i a : I) {n : ℕ} (j : Fin (n + 1)) (w : Word I n) :
    FiniteHomMatrix.single (appendShuffleTarget i (appendRun (n + 1) j.castSucc) (appendWord a w))
        (appendWord i (appendWord a w))
        (appendShuffleHom D Sc i (appendRun (n + 1) j.castSucc) (appendWord a w)) =
      FiniteHomMatrix.single (appendWord a (appendShuffleTarget i (appendRun n j) w))
        (appendWord i (appendWord a w))
        (inductionLastCrossing D Sc a i w ≫
          appendHom D Sc a _ _ (appendShuffleHom D Sc i (appendRun n j) w)) := by
  have hfits : Fits (appendWord i w).1.length (cw (canWord (n + 1) (appendRun n j).1⁻¹)) := by
    apply fits_cw
    rw [canWord_appendRun]
    intro x hx
    simp only [List.mem_range'_1] at hx
    simp [appendWord]
    omega
  have hR : appendHom D Sc a _ _ (appendShuffleHom D Sc i (appendRun n j) w) =
      cl D Sc ((appendWord i w).1 ++ [a]) ((appendShuffleTarget i (appendRun n j) w).1 ++ [a])
        (cw (canWord (n + 1) (appendRun n j).1⁻¹)) (by
          rw [pl_append_right [a] hfits]
          simpa [appendShuffleTarget, appendWord] using sChain_wh (sChain_pl ((appendWord i w).1)
            (cw (canWord (n + 1) (appendRun n j).1⁻¹))) [] [a]) := by
    change appendShuffleHom D Sc i (appendRun n j) w ▷ (pres D Sc).obj (ob D [a]) = _
    exact cl_whiskerRight D Sc _ _ [a] hfits
  rw [hR, inductionLastCrossing_eq_cl]
  erw [cl_comp]
  unfold appendShuffleHom
  apply single_cl_congr
  rw [canWord_appendRun, canWord_appendRun, Fin.val_castSucc,
    cw_range'_succ (Nat.lt_succ_iff.mp j.2)]
  simp

/-- Words of length `n + 1` are the words `w ++ [a]`. -/
theorem appendWord_pair_bijective (n : ℕ) :
    Function.Bijective (fun p : Word I n × I => appendWord p.2 p.1) := by
  constructor
  · rintro ⟨w, a⟩ ⟨w', a'⟩ h
    have h' := congrArg Subtype.val h
    simp only [appendWord] at h'
    obtain ⟨h₁, h₂⟩ := List.append_inj' h' rfl
    simp only [List.cons.injEq, and_true] at h₂
    rw [Subtype.ext h₁, h₂]
  · intro s
    have hs : s.1 ≠ [] := by
      intro h; have := s.2; rw [h] at this; simp at this
    refine ⟨(⟨s.1.dropLast, by simp [s.2]⟩, s.1.getLast hs), Subtype.ext ?_⟩
    exact List.dropLast_append_getLast hs

theorem appendWord_ne_of_ne {i a : I} (h : a ≠ i) {n : ℕ} (t t' : Word I n) :
    appendWord i t ≠ appendWord a t' := by
  intro e
  have e' := congrArg Subtype.val e
  simp only [appendWord] at e'
  have := (List.append_inj' e' rfl).2
  simp only [List.cons.injEq, and_true] at this
  exact h this.symm

variable [Fintype I]

theorem appendAlgebra_appendAlgebra_one_eq_sum (i : I) (n : ℕ) :
    appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) =
      ∑ w : Word I n, FiniteHomMatrix.single (appendWord i (appendWord i w))
        (appendWord i (appendWord i w)) (𝟙 _) := by
  change appendLinear D Sc i (n + 1)
    (appendLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ)) = _
  rw [FiniteHomMatrix.localUnit, map_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  change appendLinear D Sc i (n + 1)
    (appendLinear D Sc i n (FiniteHomMatrix.single w w (𝟙 _))) = _
  rw [appendLinear_single, appendLinear_single]
  change FiniteHomMatrix.single _ _ (appendEnd D Sc i _ (appendEnd D Sc i w 1)) = _
  rw [map_one, map_one]
  rfl

theorem single_mul_affineLastCrossing (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1 + 1))
    (f : wordObj D Sc (appendWord i (appendWord i s)) ⟶ wordObj D Sc t) :
    FiniteHomMatrix.single t (appendWord i (appendWord i s)) f * affineLastCrossing D Sc i i n =
      FiniteHomMatrix.single t (appendWord i (appendWord i s))
        (inductionLastCrossing D Sc i i s ≫ f) := by
  rw [affineLastCrossing, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n (appendWord_injective i (n + 1) h.symm))) _ _
  · simp

/-- **Left factorization of the moving crossings on the two-sided corner**:
`c_j e = ψ(c'_j) τ` for `j` below the last old strand, with `e = ψ(ψ(1))`, `τ` the
equal-colour last crossing and `c'_j` the moving crossing one level down. -/
theorem appendShuffleElement_castSucc_mul_corner (i : I) (n : ℕ) (j : Fin (n + 1)) :
    appendShuffleElement D Sc i (appendRun (n + 1) j.castSucc) *
        appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) =
      appendAlgebra D Sc i (n + 1) (appendShuffleElement D Sc i (appendRun n j)) *
        affineLastCrossing D Sc i i n := by
  rw [appendAlgebra_appendAlgebra_one_eq_sum, Finset.mul_sum]
  change _ = appendLinear D Sc i (n + 1) (appendShuffleElement D Sc i (appendRun n j)) * _
  conv_rhs => rw [appendShuffleElement, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [appendShuffleElement_mul_single, Category.id_comp, appendShuffleHom_castSucc,
    appendLinear_single, single_mul_affineLastCrossing]

theorem appendAlgebra_one_eq_sum (i : I) (n : ℕ) :
    appendAlgebra D Sc i n 1 =
      ∑ w : Word I n, FiniteHomMatrix.single (appendWord i w) (appendWord i w) (𝟙 _) := by
  change appendLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ) = _
  rw [FiniteHomMatrix.localUnit, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  change appendLinear D Sc i n (FiniteHomMatrix.single w w (𝟙 _)) = _
  rw [appendLinear_single]
  change FiniteHomMatrix.single _ _ (appendEnd D Sc i w 1) = _
  rw [map_one]
  rfl

theorem appendOne_mul_single (i : I) {n : ℕ} (t : Word I n) (s : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc (appendWord i t)) :
    appendAlgebra D Sc i n 1 * FiniteHomMatrix.single (appendWord i t) s f =
      FiniteHomMatrix.single (appendWord i t) s f := by
  rw [appendAlgebra_one_eq_sum, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n h)) _ _
  · simp

theorem appendOne_mul_single_of_ne {i a : I} (h : a ≠ i) {n : ℕ} (t : Word I n)
    (s : Word I (n + 1)) (f : wordObj D Sc s ⟶ wordObj D Sc (appendWord a t)) :
    appendAlgebra D Sc i n 1 * FiniteHomMatrix.single (appendWord a t) s f = 0 := by
  rw [appendAlgebra_one_eq_sum, Finset.sum_mul]
  exact Finset.sum_eq_zero fun w _ =>
    FiniteHomMatrix.single_mul_single_of_ne _ _ _ _ (appendWord_ne_of_ne h w t) _ _

theorem single_mul_appendAppendOne (i : I) {n : ℕ} (t : Word I (n + 1 + 1)) (w : Word I n)
    (f : wordObj D Sc (appendWord i (appendWord i w)) ⟶ wordObj D Sc t) :
    FiniteHomMatrix.single t (appendWord i (appendWord i w)) f *
        appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) =
      FiniteHomMatrix.single t (appendWord i (appendWord i w)) f := by
  rw [appendAlgebra_appendAlgebra_one_eq_sum, Finset.mul_sum, Finset.sum_eq_single w]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n (appendWord_injective i (n + 1) h.symm))) _ _
  · simp

theorem single_mul_appendAppendOne_of_ne {i a : I} (h : a ≠ i) {n : ℕ}
    (t : Word I (n + 1 + 1)) (w : Word I n)
    (f : wordObj D Sc (appendWord i (appendWord a w)) ⟶ wordObj D Sc t) :
    FiniteHomMatrix.single t (appendWord i (appendWord a w)) f *
        appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) = 0 := by
  rw [appendAlgebra_appendAlgebra_one_eq_sum, Finset.mul_sum]
  exact Finset.sum_eq_zero fun w' _ =>
    FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun e => appendWord_ne_of_ne h w' w (appendWord_injective i _ e).symm) _ _

/-- The moving crossings below the last old strand commute with the two corner idempotents:
`ψ(1) c_j = c_j ψ(ψ(1))`. -/
theorem appendOne_mul_appendShuffleElement_castSucc (i : I) (n : ℕ) (j : Fin (n + 1)) :
    appendAlgebra D Sc i (n + 1) 1 * appendShuffleElement D Sc i (appendRun (n + 1) j.castSucc) =
      appendShuffleElement D Sc i (appendRun (n + 1) j.castSucc) *
        appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) := by
  unfold appendShuffleElement
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨⟨w, a⟩, rfl⟩ := (appendWord_pair_bijective n).2 s
  dsimp only
  rw [appendShuffleHom_castSucc D Sc i a j w]
  by_cases h : a = i
  · subst h
    rw [appendOne_mul_single, single_mul_appendAppendOne]
  · rw [appendOne_mul_single_of_ne D Sc h, single_mul_appendAppendOne_of_ne D Sc h]

/-- **Left factorization on the two-sided corner**: `ψ(1) c_j = ψ(c'_j) τ`. -/
theorem appendOne_mul_appendShuffleElement_castSucc_eq (i : I) (n : ℕ) (j : Fin (n + 1)) :
    appendAlgebra D Sc i (n + 1) 1 * appendShuffleElement D Sc i (appendRun (n + 1) j.castSucc) =
      appendAlgebra D Sc i (n + 1) (appendShuffleElement D Sc i (appendRun n j)) *
        affineLastCrossing D Sc i i n := by
  rw [appendOne_mul_appendShuffleElement_castSucc, appendShuffleElement_castSucc_mul_corner]

/-! ## Sliding powers of the last dot through the last crossing -/

/-- Sums `Σ_b ψ(f_b) x^b` with the new dot `x` on the right of the old coefficient. -/
def appendDotSum (i : I) (n : ℕ) : (ℕ →₀ Hn D Sc (n + 1)) →+ Hn D Sc (n + 1 + 1) :=
  Finsupp.liftAddHom fun b =>
    (AddMonoidHom.mulRight (affineLastDot D Sc i (n + 1) ^ b)).comp
      (appendLinear D Sc i (n + 1)).toAddMonoidHom

theorem appendDotSum_single (i : I) (n b : ℕ) (c : Hn D Sc (n + 1)) :
    appendDotSum D Sc i n (Finsupp.single b c) =
      appendAlgebra D Sc i (n + 1) c * affineLastDot D Sc i (n + 1) ^ b := by
  unfold appendDotSum
  simp only [Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.coe_mulRight, LinearMap.toAddMonoidHom_coe]
  rfl

theorem appendDotSum_mul_lastDot (i : I) (n : ℕ) (f : ℕ →₀ Hn D Sc (n + 1)) :
    appendDotSum D Sc i n f * affineLastDot D Sc i (n + 1) =
      appendDotSum D Sc i n (Finsupp.mapDomain Nat.succ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, add_mul, hf, hg, Finsupp.mapDomain_add, map_add]
  | single b c => rw [Finsupp.mapDomain_single, appendDotSum_single, appendDotSum_single,
      pow_succ, mul_assoc]

theorem appendAlgebra_pow_mul (i : I) (n : ℕ) (x d : Hn D Sc n) (m : ℕ) :
    appendAlgebra D Sc i n x ^ m * appendAlgebra D Sc i n d =
      appendAlgebra D Sc i n (x ^ m * d) := by
  induction m generalizing d with
  | zero => simp
  | succ m ih => rw [pow_succ, mul_assoc, ← map_mul, ih, ← mul_assoc, ← pow_succ]

/-- The dot slide `τ x_(n+2) = s x_(n+1) τ - s ψ(ψ(1))` on the equal-colour last crossing. -/
theorem affineLastCrossing_mul_lastDot (i : I) (n : ℕ) :
    affineLastCrossing D Sc i i n * affineLastDot D Sc i (n + 1) =
      Supercategory.koszulSign (D.parity i) (D.parity i) •
          (appendAlgebra D Sc i (n + 1) (affineLastDot D Sc i n) * affineLastCrossing D Sc i i n) -
        Supercategory.koszulSign (D.parity i) (D.parity i) •
          appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) := by
  rw [← affineLastCrossing_slide_right D Sc i n, smul_sub _ _
    (Supercategory.koszulSign (D.parity i) (D.parity i) • _),
    Supercategory.koszulSign_smul_smul]
  abel

/-- **Dot slide through the last crossing**: `τ x_(n+2)^m = s^m x_(n+1)^m τ + Σ_b ψ(f_b) x_(n+2)^b`
with `s` the Koszul sign of the appended colour (`AppendCoordinates.md` §4, (1)). -/
theorem affineLastCrossing_mul_lastDot_pow (i : I) (n m : ℕ) :
    ∃ f : ℕ →₀ Hn D Sc (n + 1),
      affineLastCrossing D Sc i i n * affineLastDot D Sc i (n + 1) ^ m =
        Supercategory.koszulSign (D.parity i) (D.parity i) ^ m •
            (appendAlgebra D Sc i (n + 1) (affineLastDot D Sc i n) ^ m *
              affineLastCrossing D Sc i i n) +
          appendDotSum D Sc i n f := by
  have hτz := affineLastCrossing_mul_lastDot D Sc i n
  set s := Supercategory.koszulSign (D.parity i) (D.parity i)
  set Y := appendAlgebra D Sc i (n + 1) (affineLastDot D Sc i n)
  set τ := affineLastCrossing D Sc i i n
  set z := affineLastDot D Sc i (n + 1)
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨Finsupp.mapDomain Nat.succ f +
      Finsupp.single 0 (-(s ^ (m + 1)) • (affineLastDot D Sc i n ^ m * appendAlgebra D Sc i n 1)),
      ?_⟩
    rw [pow_succ, ← mul_assoc, hf, add_mul, appendDotSum_mul_lastDot, smul_mul_assoc, mul_assoc,
      hτz, mul_sub, mul_smul_comm, mul_smul_comm, ← mul_assoc, ← pow_succ,
      appendAlgebra_pow_mul, map_add, appendDotSum_single, pow_zero, mul_one, map_zsmul,
      smul_sub, smul_smul, smul_smul, ← pow_succ]
    simp only [neg_smul, sub_eq_add_neg]
    abel

/-! ## Spanning the two-sided corner -/

/-- The moving crossing to the top position is the corner idempotent. -/
theorem appendShuffleElement_last (i : I) (n : ℕ) :
    appendShuffleElement D Sc i (appendRun n (Fin.last n)) = appendAlgebra D Sc i n 1 := by
  rw [appendAlgebra_one_eq_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hc : cw (canWord (n + 1) (appendRun n (Fin.last n)).1⁻¹) = [] := by
    rw [canWord_appendRun]; simp
  unfold appendShuffleHom
  refine (single_cl_congr D Sc (s := appendWord i s) (t' := appendWord i s) _ ?_ hc).trans ?_
  · exact sChain_pl _ _
  · exact congrArg _ (cl_nil D Sc _ _)

/-- Sums `Σ ψ(c'_j x^m) τ ψ(b)` of left-crossing terms. -/
def appendLeftSum (i : I) (n : ℕ) :
    ((Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) →+ Hn D Sc (n + 1 + 1) :=
  Finsupp.liftAddHom fun p =>
    (AddMonoidHom.mulLeft (appendAlgebra D Sc i (n + 1)
        (appendShuffleElement D Sc i (appendRun n p.1) * affineLastDot D Sc i n ^ p.2) *
      affineLastCrossing D Sc i i n)).comp (appendLinear D Sc i (n + 1)).toAddMonoidHom

theorem appendLeftSum_single (i : I) (n : ℕ) (j : Fin (n + 1)) (m : ℕ) (b : Hn D Sc (n + 1)) :
    appendLeftSum D Sc i n (Finsupp.single (j, m) b) =
      appendAlgebra D Sc i (n + 1)
          (appendShuffleElement D Sc i (appendRun n j) * affineLastDot D Sc i n ^ m) *
        affineLastCrossing D Sc i i n * appendAlgebra D Sc i (n + 1) b := by
  unfold appendLeftSum
  simp only [Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.coe_mulLeft, LinearMap.toAddMonoidHom_coe]
  rfl

/-- Sums `Σ x^m ψ(b)` with the new dot on the left. -/
def appendPolySum (i : I) (n : ℕ) : (ℕ →₀ Hn D Sc (n + 1)) →+ Hn D Sc (n + 1 + 1) :=
  Finsupp.liftAddHom fun m =>
    (AddMonoidHom.mulLeft (affineLastDot D Sc i (n + 1) ^ m)).comp
      (appendLinear D Sc i (n + 1)).toAddMonoidHom

theorem appendPolySum_single (i : I) (n m : ℕ) (b : Hn D Sc (n + 1)) :
    appendPolySum D Sc i n (Finsupp.single m b) =
      affineLastDot D Sc i (n + 1) ^ m * appendAlgebra D Sc i (n + 1) b := by
  unfold appendPolySum
  simp only [Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.coe_mulLeft, LinearMap.toAddMonoidHom_coe]
  rfl

theorem appendAlgebra_mul_pow (i : I) (n : ℕ) (d x : Hn D Sc n) (m : ℕ) :
    appendAlgebra D Sc i n d * appendAlgebra D Sc i n x ^ m =
      appendAlgebra D Sc i n (d * x ^ m) := by
  induction m generalizing d with
  | zero =>
    rw [pow_zero, pow_zero, mul_one, mul_one]
  | succ m ih => rw [pow_succ', ← mul_assoc, ← map_mul, ih, mul_assoc, ← pow_succ']

/-- Old coefficients move to the right of powers of the new dot, up to parity twists. -/
theorem appendAlgebra_mul_lastDot_pow (i : I) (n : ℕ) (r : Hn D Sc n) (b : ℕ) :
    ∃ r', appendAlgebra D Sc i n r * affineLastDot D Sc i n ^ b =
      affineLastDot D Sc i n ^ b * appendAlgebra D Sc i n r' := by
  induction b generalizing r with
  | zero => exact ⟨r, by simp⟩
  | succ b ih =>
    obtain ⟨r', h⟩ := ih r
    refine ⟨homMatrixTwist D Sc n (D.parity i) r', ?_⟩
    rw [pow_succ, ← mul_assoc, h, mul_assoc, affineLastDot_twist_comm, ← mul_assoc]

theorem appendAlgebra_mul_appendDotSum_mul_mem (i : I) (n : ℕ) (r d : Hn D Sc (n + 1))
    (f : ℕ →₀ Hn D Sc (n + 1)) :
    appendAlgebra D Sc i (n + 1) r * appendDotSum D Sc i n f * appendAlgebra D Sc i (n + 1) d ∈
      (appendPolySum D Sc i n).range := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, mul_add, add_mul]; exact add_mem hf hg
  | single b c =>
    rw [appendDotSum_single, ← mul_assoc, ← map_mul]
    obtain ⟨r', h⟩ := appendAlgebra_mul_lastDot_pow D Sc i (n + 1) (r * c) b
    rw [h, mul_assoc, ← map_mul]
    exact ⟨Finsupp.single b (r' * d), appendPolySum_single D Sc i n b _⟩

theorem appendOne_mul_appendPBWTerm_mem (i : I) (n : ℕ) (u : AppendShuffleAt (n + 1)) (m : ℕ)
    (c : Hn D Sc (n + 1)) :
    appendAlgebra D Sc i (n + 1) 1 * appendPBWTerm D Sc i u m c ∈
      (appendLeftSum D Sc i n).range ⊔ (appendPolySum D Sc i n).range := by
  obtain ⟨j, rfl⟩ := (appendRunEquiv (n + 1)).surjective u
  rw [appendRunEquiv_apply]
  induction j using Fin.lastCases with
  | last =>
    apply AddSubgroup.mem_sup_right
    rw [appendPBWTerm, appendShuffleElement_last, ← mul_assoc, ← mul_assoc, ← map_mul]
    obtain ⟨r', h⟩ := appendAlgebra_mul_lastDot_pow D Sc i (n + 1) (1 * 1) m
    rw [h, mul_assoc, ← map_mul]
    exact ⟨Finsupp.single m (r' * c), appendPolySum_single D Sc i n m _⟩
  | cast j =>
    obtain ⟨f, hf⟩ := affineLastCrossing_mul_lastDot_pow D Sc i n m
    rw [appendPBWTerm, ← mul_assoc, ← mul_assoc, appendOne_mul_appendShuffleElement_castSucc_eq,
      mul_assoc _ (affineLastCrossing D Sc i i n), hf, mul_add, add_mul]
    refine add_mem (AddSubgroup.mem_sup_left ?_) (AddSubgroup.mem_sup_right
      (appendAlgebra_mul_appendDotSum_mul_mem D Sc i n _ _ f))
    rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc, appendAlgebra_mul_pow]
    refine AddSubgroup.zsmul_mem _ (AddMonoidHom.mem_range.mpr ⟨Finsupp.single (j, m) c, ?_⟩) _
    rw [appendLeftSum_single]

/-- **Spanning the two-sided append corner**: every `y` with `ψ(1) y = y = y ψ(1)` is a sum of
left-crossing terms `ψ(c'_j x^m) τ ψ(b)` and polynomial terms `x^m ψ(b)`
(`AppendCoordinates.md` §4). -/
theorem mem_appendLeftSum_sup_appendPolySum (i : I) (n : ℕ) (y : Hn D Sc (n + 1 + 1))
    (hl : appendAlgebra D Sc i (n + 1) 1 * y = y) (hr : y * appendAlgebra D Sc i (n + 1) 1 = y) :
    y ∈ (appendLeftSum D Sc i n).range ⊔ (appendPolySum D Sc i n).range := by
  obtain ⟨b, hb⟩ := (appendCoordinateEquiv D Sc i (n + 1)).surjective ⟨y, hr⟩
  rw [appendCoordinateEquiv_apply] at hb
  have hy : y = ∑ q ∈ b.support, appendPBWTerm D Sc i q.1 q.2 (b q) := by
    have h := congrArg Subtype.val hb
    rw [Finsupp.sum, Submodule.coe_sum] at h
    exact h.symm
  rw [← hl, hy, Finset.mul_sum]
  exact sum_mem fun q _ => appendOne_mul_appendPBWTerm_mem D Sc i n q.1 q.2 _

/-! ## Directness of the decomposition -/

theorem affineLastCrossing_mul_appendAppendOne (i : I) (n : ℕ) :
    affineLastCrossing D Sc i i n * appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) =
      affineLastCrossing D Sc i i n := by
  rw [affineLastCrossing, Finset.sum_mul]
  exact Finset.sum_congr rfl fun w _ => single_mul_appendAppendOne D Sc i _ w _

theorem homMatrixTwist_appendAlgebra_one (i : I) (n : ℕ) (p : ZMod 2) :
    homMatrixTwist D Sc (n + 1) p (appendAlgebra D Sc i n 1) = appendAlgebra D Sc i n 1 := by
  rw [appendAlgebra_one_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [homMatrixTwist_single, Supercategory.twist_id]

theorem appendAppendOne_mul_lastDot_pow (i : I) (n m : ℕ) :
    appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) * affineLastDot D Sc i (n + 1) ^ m =
      affineLastDot D Sc i (n + 1) ^ m * appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, affineLastDot_twist_comm,
      homMatrixTwist_appendAlgebra_one, ← mul_assoc]

/-- The left-crossing terms only see the coefficient on old words ending in the appended
colour. -/
theorem appendLeftSum_single_appendOne_mul (i : I) (n : ℕ) (j : Fin (n + 1)) (m : ℕ)
    (b : Hn D Sc (n + 1)) :
    appendLeftSum D Sc i n (Finsupp.single (j, m) (appendAlgebra D Sc i n 1 * b)) =
      appendLeftSum D Sc i n (Finsupp.single (j, m) b) := by
  rw [appendLeftSum_single, appendLeftSum_single,
    map_mul (appendAlgebra D Sc i (n + 1)) (appendAlgebra D Sc i n 1) b, ← mul_assoc,
    mul_assoc _ (affineLastCrossing D Sc i i n), affineLastCrossing_mul_appendAppendOne]

theorem appendCoefficients_appendPBWTerm (i : I) (n : ℕ) (u : AppendShuffleAt n) (m : ℕ)
    (b : Hn D Sc n) :
    appendCoefficients D Sc i n (appendPBWTerm D Sc i u m b) = Finsupp.single (u, m) b := by
  have h0 : appendPBWCorner D Sc i u m 0 = 0 :=
    Subtype.ext (by simp [appendPBWCorner, appendPBWTerm])
  have hc : appendCoordinateEquiv D Sc i n (Finsupp.single (u, m) b) =
      appendPBWCorner D Sc i u m b := by
    rw [appendCoordinateEquiv_apply]
    exact Finsupp.sum_single_index h0
  have h := (appendCoordinateEquiv D Sc i n).symm_apply_eq.mpr hc.symm
  rw [appendCoordinateEquiv_symm_apply] at h
  exact h

theorem appendCoefficients_lastDot_pow_mul (i : I) (n k : ℕ) (r : Hn D Sc (n + 1)) :
    appendCoefficients D Sc i (n + 1)
        (affineLastDot D Sc i (n + 1) ^ k * appendAlgebra D Sc i (n + 1) r) =
      Finsupp.single (appendRun (n + 1) (Fin.last (n + 1)), k) r := by
  rw [← appendCoefficients_appendPBWTerm, appendPBWTerm, appendShuffleElement_last]
  congr 1
  cases k with
  | zero =>
    simp only [pow_zero, mul_one, one_mul]
    rw [← map_mul, one_mul]
  | succ k => rw [pow_succ', ← mul_assoc, append_one_mul_affineLastDot]

theorem appendCoefficients_appendPolySum_last (i : I) (n : ℕ) (g : ℕ →₀ Hn D Sc (n + 1))
    (k : ℕ) :
    appendCoefficients D Sc i (n + 1) (appendPolySum D Sc i n g)
        (appendRun (n + 1) (Fin.last (n + 1)), k) = g k := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply]
  | single k' r =>
    rw [appendPolySum_single, appendCoefficients_lastDot_pow_mul]
    simp only [Finsupp.single_apply, Prod.mk.injEq, true_and]

theorem appendCoefficients_appendPolySum_castSucc (i : I) (n : ℕ) (g : ℕ →₀ Hn D Sc (n + 1))
    (j : Fin (n + 1)) (m : ℕ) :
    appendCoefficients D Sc i (n + 1) (appendPolySum D Sc i n g)
        (appendRun (n + 1) j.castSucc, m) = 0 := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, Finsupp.add_apply, hf, hg, add_zero]
  | single k r =>
    have h' : (appendRun (n + 1) (Fin.last (n + 1)), k) ≠ (appendRun (n + 1) j.castSucc, m) :=
      fun h' => Fin.castSucc_ne_last j (appendRun_injective _ (congrArg Prod.fst h')).symm
    rw [appendPolySum_single, appendCoefficients_lastDot_pow_mul]
    simp only [Finsupp.single_apply, h', ↓reduceIte]

/-- A moving-crossing term with coefficient on old words ending in the appended colour is,
up to the sign `s^m`, a left-crossing term plus polynomial terms. -/
theorem appendPBWTerm_castSucc_eq (i : I) (n : ℕ) (j : Fin (n + 1)) (m : ℕ)
    (b : Hn D Sc (n + 1)) :
    ∃ g, appendPBWTerm D Sc i (appendRun (n + 1) j.castSucc) m (appendAlgebra D Sc i n 1 * b) =
      Supercategory.koszulSign (D.parity i) (D.parity i) ^ m •
          appendLeftSum D Sc i n (Finsupp.single (j, m) b) +
        appendPolySum D Sc i n g := by
  obtain ⟨f, hf⟩ := affineLastCrossing_mul_lastDot_pow D Sc i n m
  obtain ⟨g, hg⟩ := appendAlgebra_mul_appendDotSum_mul_mem D Sc i n
    (appendShuffleElement D Sc i (appendRun n j)) b f
  have h1 : appendShuffleElement D Sc i (appendRun (n + 1) j.castSucc) *
      affineLastDot D Sc i (n + 1) ^ m * appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) =
      appendAlgebra D Sc i (n + 1) (appendShuffleElement D Sc i (appendRun n j)) *
        (affineLastCrossing D Sc i i n * affineLastDot D Sc i (n + 1) ^ m) := by
    rw [mul_assoc, ← appendAppendOne_mul_lastDot_pow, ← mul_assoc,
      appendShuffleElement_castSucc_mul_corner, mul_assoc]
  refine ⟨g, ?_⟩
  rw [appendPBWTerm, map_mul, ← mul_assoc, h1, hf, mul_add, add_mul, ← hg, mul_smul_comm,
    smul_mul_assoc, ← mul_assoc, appendAlgebra_mul_pow, appendLeftSum_single]

theorem appendCoefficients_appendLeftSum_castSucc (i : I) (n : ℕ)
    (F : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) (j : Fin (n + 1)) (m : ℕ) :
    Supercategory.koszulSign (D.parity i) (D.parity i) ^ m •
        appendCoefficients D Sc i (n + 1) (appendLeftSum D Sc i n F)
          (appendRun (n + 1) j.castSucc, m) =
      appendAlgebra D Sc i n 1 * F (j, m) := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F G hF hG => rw [map_add, map_add, Finsupp.add_apply, smul_add, hF, hG,
      Finsupp.add_apply, mul_add]
  | single q b =>
    obtain ⟨j', m'⟩ := q
    obtain ⟨g, hg⟩ := appendPBWTerm_castSucc_eq D Sc i n j' m' b
    set s := Supercategory.koszulSign (D.parity i) (D.parity i)
    have hs : ∀ e : ℕ, s ^ e * s ^ e = 1 := fun e => by
      rw [← mul_pow, Supercategory.koszulSign_mul_self, one_pow]
    have hL : appendLeftSum D Sc i n (Finsupp.single (j', m') b) =
        s ^ m' • (appendPBWTerm D Sc i (appendRun (n + 1) j'.castSucc) m'
          (appendAlgebra D Sc i n 1 * b) - appendPolySum D Sc i n g) := by
      rw [hg, add_sub_cancel_right, smul_smul, hs, one_smul]
    rw [hL, map_zsmul, map_sub, appendCoefficients_appendPBWTerm, Finsupp.smul_apply,
      Finsupp.sub_apply, appendCoefficients_appendPolySum_castSucc, sub_zero, smul_smul]
    by_cases h : (j', m') = (j, m)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same, hs, one_smul]
    · have h' : (appendRun (n + 1) j'.castSucc, m') ≠ (appendRun (n + 1) j.castSucc, m) := by
        intro h'
        obtain ⟨h1, h2⟩ := Prod.mk.inj h'
        exact h (Prod.ext (Fin.castSucc_injective _ (appendRun_injective _ h1)) h2)
      simp only [Finsupp.single_apply, h, h', ↓reduceIte, smul_zero, mul_zero]

/-- **Directness of the two-sided corner decomposition**: a vanishing sum of left-crossing
and polynomial terms has zero polynomial part and left-crossing coefficients killed by
the idempotent `ψ'(1)` of old words ending in the appended colour. -/
theorem appendLeftSum_add_appendPolySum_eq_zero (i : I) (n : ℕ)
    (F : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) (G : ℕ →₀ Hn D Sc (n + 1))
    (h : appendLeftSum D Sc i n F + appendPolySum D Sc i n G = 0) :
    (∀ q, appendAlgebra D Sc i n 1 * F q = 0) ∧ G = 0 := by
  have hF : ∀ q, appendAlgebra D Sc i n 1 * F q = 0 := by
    rintro ⟨j, m⟩
    have h' := congrArg (fun y => Supercategory.koszulSign (D.parity i) (D.parity i) ^ m •
      appendCoefficients D Sc i (n + 1) y (appendRun (n + 1) j.castSucc, m)) h
    simp only [map_add, Finsupp.add_apply, appendCoefficients_appendPolySum_castSucc,
      smul_zero, add_zero, map_zero, Finsupp.zero_apply] at h'
    rw [← appendCoefficients_appendLeftSum_castSucc]
    exact h'
  have hL : appendLeftSum D Sc i n F = 0 := by
    rw [← Finsupp.sum_single F, map_finsuppSum]
    refine Finset.sum_eq_zero fun q _ => ?_
    obtain ⟨j, m⟩ := q
    show appendLeftSum D Sc i n (Finsupp.single (j, m) (F (j, m))) = 0
    rw [← appendLeftSum_single_appendOne_mul, hF, Finsupp.single_zero, map_zero]
  refine ⟨hF, ?_⟩
  rw [hL, zero_add] at h
  ext k
  rw [← appendCoefficients_appendPolySum_last D Sc i n G k, h, map_zero, Finsupp.zero_apply,
    Finsupp.zero_apply]

/-! ## Right multiplication by the new dot -/

/-- The parity twist of the appended colour, coefficientwise. -/
abbrev appendTwist (i : I) (n : ℕ) : Hn D Sc (n + 1) →+ Hn D Sc (n + 1) :=
  (homMatrixTwist D Sc (n + 1) (D.parity i)).toAddMonoidHom

/-- Shift of the dot exponent of left-crossing coordinates, with the parity twist. -/
def appendLeftShift (i : I) (n : ℕ) :
    ((Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) →+ ((Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) :=
  (Finsupp.mapDomain.addMonoidHom fun p : Fin (n + 1) × ℕ => (p.1, p.2 + 1)).comp
    (Finsupp.mapRange.addMonoidHom (appendTwist D Sc i n))

/-- The degree-zero correction `Σ c'_j x^m ψ(1) tw(u_(j,m))`. -/
def appendLeftDegree (i : I) (n : ℕ) :
    ((Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) →+ Hn D Sc (n + 1) :=
  Finsupp.liftAddHom fun p =>
    (AddMonoidHom.mulLeft (appendShuffleElement D Sc i (appendRun n p.1) *
      affineLastDot D Sc i n ^ p.2 * appendAlgebra D Sc i n 1)).comp (appendTwist D Sc i n)

/-- Shift of the polynomial coordinates, with the parity twist. -/
def appendPolyShift (i : I) (n : ℕ) : (ℕ →₀ Hn D Sc (n + 1)) →+ (ℕ →₀ Hn D Sc (n + 1)) :=
  (Finsupp.mapDomain.addMonoidHom Nat.succ).comp
    (Finsupp.mapRange.addMonoidHom (appendTwist D Sc i n))

/-- `R_t(j f) = j(t f)`: right multiplication by the new dot on polynomial terms. -/
theorem appendPolySum_mul_lastDot (i : I) (n : ℕ) (g : ℕ →₀ Hn D Sc (n + 1)) :
    appendPolySum D Sc i n g * affineLastDot D Sc i (n + 1) =
      appendPolySum D Sc i n (appendPolyShift D Sc i n g) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, add_mul, hf, hg, map_add, map_add]
  | single m b =>
    simp only [appendPolyShift, AddMonoidHom.comp_apply, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]
    rw [appendPolySum_single, appendPolySum_single, mul_assoc, affineLastDot_twist_comm,
      ← mul_assoc, ← pow_succ]
    rfl

/-- `R_t(F u) = F(X u) + j(E u)`: right multiplication by the new dot on left-crossing terms,
with `X = s · appendLeftShift` and `E = -s · appendLeftDegree`. -/
theorem appendLeftSum_mul_lastDot (i : I) (n : ℕ) (F : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) :
    appendLeftSum D Sc i n F * affineLastDot D Sc i (n + 1) =
      Supercategory.koszulSign (D.parity i) (D.parity i) •
          appendLeftSum D Sc i n (appendLeftShift D Sc i n F) -
        Supercategory.koszulSign (D.parity i) (D.parity i) •
          appendPolySum D Sc i n (Finsupp.single 0 (appendLeftDegree D Sc i n F)) := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, add_mul, hf, hg, map_add, map_add, map_add, Finsupp.single_add, map_add]
    simp only [smul_add]
    abel
  | single q b =>
    obtain ⟨j, m⟩ := q
    simp only [appendLeftShift, AddMonoidHom.comp_apply, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]
    rw [appendLeftSum_single, appendLeftSum_single, appendPolySum_single, pow_zero, one_mul,
      mul_assoc, affineLastDot_twist_comm, ← mul_assoc, mul_assoc _ (affineLastCrossing D Sc i i n),
      affineLastCrossing_mul_lastDot, mul_sub, sub_mul, mul_smul_comm, mul_smul_comm,
      smul_mul_assoc, smul_mul_assoc, ← mul_assoc, ← map_mul, mul_assoc _ (affineLastDot D Sc i n ^ m),
      ← pow_succ, ← map_mul, ← map_mul]
    unfold appendLeftDegree
    simp only [Finsupp.liftAddHom_apply_single, AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft]
    rfl

end OddMath.QuiverHecke
