/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.AppendShuffleRuns
import OddMath.QuiverHecke.CyclotomicAction.AppendCoordinates
import OddMath.QuiverHecke.CyclotomicAction.Square
import OddMath.QuiverHecke.CyclotomicAction.GlobalSlideAlgebra

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

/-- The appended moving crossing on a word whose last old strand has the appended colour,
as a last crossing followed by the moving crossing one level down. -/
theorem appendShuffleHom_castSucc (i : I) {n : ℕ} (j : Fin (n + 1)) (w : Word I n) :
    FiniteHomMatrix.single (appendShuffleTarget i (appendRun (n + 1) j.castSucc) (appendWord i w))
        (appendWord i (appendWord i w))
        (appendShuffleHom D Sc i (appendRun (n + 1) j.castSucc) (appendWord i w)) =
      FiniteHomMatrix.single (appendWord i (appendShuffleTarget i (appendRun n j) w))
        (appendWord i (appendWord i w))
        (inductionLastCrossing D Sc i i w ≫
          appendHom D Sc i _ _ (appendShuffleHom D Sc i (appendRun n j) w)) := by
  have hfits : Fits (appendWord i w).1.length (cw (canWord (n + 1) (appendRun n j).1⁻¹)) := by
    apply fits_cw
    rw [canWord_appendRun]
    intro x hx
    simp only [List.mem_range'_1] at hx
    simp [appendWord]
    omega
  have hR : appendHom D Sc i _ _ (appendShuffleHom D Sc i (appendRun n j) w) =
      cl D Sc ((appendWord i w).1 ++ [i]) ((appendShuffleTarget i (appendRun n j) w).1 ++ [i])
        (cw (canWord (n + 1) (appendRun n j).1⁻¹)) (by
          rw [pl_append_right [i] hfits]
          simpa [appendShuffleTarget, appendWord] using sChain_wh (sChain_pl ((appendWord i w).1)
            (cw (canWord (n + 1) (appendRun n j).1⁻¹))) [] [i]) := by
    change appendShuffleHom D Sc i (appendRun n j) w ▷ (pres D Sc).obj (ob D [i]) = _
    exact cl_whiskerRight D Sc _ _ [i] hfits
  rw [hR, inductionLastCrossing_eq_cl]
  erw [cl_comp]
  unfold appendShuffleHom
  apply single_cl_congr
  rw [canWord_appendRun, canWord_appendRun, Fin.val_castSucc,
    cw_range'_succ (Nat.lt_succ_iff.mp j.2)]
  simp

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

/-- **Dot slide through the last crossing**: `τ x_(n+2)^m = s^m x_(n+1)^m τ + Σ_b ψ(f_b) x_(n+2)^b`
with `s` the Koszul sign of the appended colour (`AppendCoordinates.md` §4, (1)). -/
theorem affineLastCrossing_mul_lastDot_pow (i : I) (n m : ℕ) :
    ∃ f : ℕ →₀ Hn D Sc (n + 1),
      affineLastCrossing D Sc i i n * affineLastDot D Sc i (n + 1) ^ m =
        Supercategory.koszulSign (D.parity i) (D.parity i) ^ m •
            (appendAlgebra D Sc i (n + 1) (affineLastDot D Sc i n) ^ m *
              affineLastCrossing D Sc i i n) +
          appendDotSum D Sc i n f := by
  have hτz : affineLastCrossing D Sc i i n * affineLastDot D Sc i (n + 1) =
      Supercategory.koszulSign (D.parity i) (D.parity i) •
          (appendAlgebra D Sc i (n + 1) (affineLastDot D Sc i n) * affineLastCrossing D Sc i i n) -
        Supercategory.koszulSign (D.parity i) (D.parity i) •
          appendAlgebra D Sc i (n + 1) (appendAlgebra D Sc i n 1) := by
    rw [← affineLastCrossing_slide_right D Sc i n, smul_sub _ _
      (Supercategory.koszulSign (D.parity i) (D.parity i) • _),
      Supercategory.koszulSign_smul_smul]
    abel
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

end OddMath.QuiverHecke
