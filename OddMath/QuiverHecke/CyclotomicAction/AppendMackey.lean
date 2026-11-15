import OddMath.QuiverHecke.AppendShuffleRuns
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunction
import OddMath.QuiverHecke.CyclotomicAction.GlobalInduction
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRight
import OddMath.QuiverHecke.CyclotomicAction.PrependCoordinates
import OddMath.QuiverHecke.CyclotomicAction.MovingShiftRelations
import OddMath.QuiverHecke.CyclotomicAction.BoundaryDivision
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeight
import OddMath.QuiverHecke.CyclotomicAction.AppendBalance

/-!
# Append mackey

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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

/-! ## The two-sided corner as a direct sum -/

/-- Left multiplication by `ψ'(1)` on left-crossing coordinates. -/
def appendLeftProj (i : I) (n : ℕ) :
    ((Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) →+ ((Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) :=
  Finsupp.mapRange.addMonoidHom (AddMonoidHom.mulLeft (appendAlgebra D Sc i n 1))

theorem appendLeftSum_appendLeftProj (i : I) (n : ℕ) (F : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) :
    appendLeftSum D Sc i n (appendLeftProj D Sc i n F) = appendLeftSum D Sc i n F := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | single q b =>
    obtain ⟨j, m⟩ := q
    simp only [appendLeftProj, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
      AddMonoidHom.coe_mulLeft]
    exact appendLeftSum_single_appendOne_mul D Sc i n j m b

/-- Left-crossing coordinates on old words ending in the appended colour. -/
def appendLeftCoordinates (i : I) (n : ℕ) : AddSubgroup ((Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) where
  carrier := {F | ∀ q, appendAlgebra D Sc i n 1 * F q = F q}
  add_mem' {F G} hF hG q := by rw [Finsupp.add_apply, mul_add, hF, hG]
  zero_mem' q := by simp
  neg_mem' {F} hF q := by rw [Finsupp.neg_apply, mul_neg, hF]

/-- The two-sided append corner `ψ(1) Hn (n+2) ψ(1)`. -/
def appendTwoSidedCorner (i : I) (n : ℕ) : AddSubgroup (Hn D Sc (n + 1 + 1)) where
  carrier := {y | appendAlgebra D Sc i (n + 1) 1 * y = y ∧ y * appendAlgebra D Sc i (n + 1) 1 = y}
  add_mem' {x y} hx hy := ⟨by rw [mul_add, hx.1, hy.1], by rw [add_mul, hx.2, hy.2]⟩
  zero_mem' := ⟨by simp, by simp⟩
  neg_mem' {x} hx := ⟨by rw [mul_neg, hx.1], by rw [neg_mul, hx.2]⟩

theorem appendLeftSum_mem_appendTwoSidedCorner (i : I) (n : ℕ)
    (F : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) :
    appendLeftSum D Sc i n F ∈ appendTwoSidedCorner D Sc i n := by
  induction F using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add f g hf hg => rw [map_add]; exact add_mem hf hg
  | single q b =>
    obtain ⟨j, m⟩ := q
    rw [appendLeftSum_single]
    refine ⟨?_, ?_⟩
    · rw [← mul_assoc, ← mul_assoc, ← map_mul, one_mul]
    · rw [mul_assoc, ← map_mul, mul_one]

theorem appendPolySum_mem_appendTwoSidedCorner (i : I) (n : ℕ) (G : ℕ →₀ Hn D Sc (n + 1)) :
    appendPolySum D Sc i n G ∈ appendTwoSidedCorner D Sc i n := by
  induction G using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add f g hf hg => rw [map_add]; exact add_mem hf hg
  | single m b =>
    rw [appendPolySum_single]
    refine ⟨?_, ?_⟩
    · cases m with
      | zero => rw [pow_zero, one_mul, ← map_mul, one_mul]
      | succ m => rw [pow_succ', ← mul_assoc, ← mul_assoc, append_one_mul_affineLastDot]
    · rw [mul_assoc, ← map_mul, mul_one]

/-- The sum map `(F, G) ↦ F(u) + j(G)` into the two-sided corner. -/
def appendCornerSum (i : I) (n : ℕ) :
    appendLeftCoordinates D Sc i n × (ℕ →₀ Hn D Sc (n + 1)) →+ appendTwoSidedCorner D Sc i n :=
  AddMonoidHom.codRestrict
    (((appendLeftSum D Sc i n).comp (appendLeftCoordinates D Sc i n).subtype).coprod
      (appendPolySum D Sc i n))
    (appendTwoSidedCorner D Sc i n) fun _ =>
      add_mem (appendLeftSum_mem_appendTwoSidedCorner D Sc i n _)
        (appendPolySum_mem_appendTwoSidedCorner D Sc i n _)

/-- **Append-side Mackey decomposition of the two-sided corner** (`AppendCoordinates.md` §4):
`ψ(1) Hn (n+2) ψ(1) = ⊕_(j ≤ n, m) ψ(c'_j x^m) τ ψ(ψ'(1) Hn (n+1)) ⊕ ⊕_m z^m ψ(Hn (n+1))`. -/
def appendCornerEquiv (i : I) (n : ℕ) :
    appendLeftCoordinates D Sc i n × (ℕ →₀ Hn D Sc (n + 1)) ≃+ appendTwoSidedCorner D Sc i n :=
  AddEquiv.ofBijective (appendCornerSum D Sc i n) ⟨by
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨F, hF⟩, G⟩ h
    have h' := congrArg Subtype.val h
    obtain ⟨h1, h2⟩ := appendLeftSum_add_appendPolySum_eq_zero D Sc i n F G h'
    refine Prod.ext (Subtype.ext (Finsupp.ext fun q => ?_)) h2
    rw [← hF q, h1 q]
    rfl, by
    rintro ⟨y, hl, hr⟩
    obtain ⟨F, hF, G, hG, hFG⟩ := AddSubgroup.mem_sup.mp
      (mem_appendLeftSum_sup_appendPolySum D Sc i n y hl hr)
    obtain ⟨F', rfl⟩ := hF
    obtain ⟨G', rfl⟩ := hG
    refine ⟨(⟨appendLeftProj D Sc i n F', fun q => ?_⟩, G'), Subtype.ext ?_⟩
    · simp only [appendLeftProj, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply,
        AddMonoidHom.coe_mulLeft, ← mul_assoc, ← map_mul, one_mul]
    · change appendLeftSum D Sc i n (appendLeftProj D Sc i n F') + appendPolySum D Sc i n G' = y
      rw [appendLeftSum_appendLeftProj, hFG]⟩

theorem appendCornerEquiv_apply (i : I) (n : ℕ)
    (p : appendLeftCoordinates D Sc i n × (ℕ →₀ Hn D Sc (n + 1))) :
    (appendCornerEquiv D Sc i n p : Hn D Sc (n + 1 + 1)) =
      appendLeftSum D Sc i n p.1 + appendPolySum D Sc i n p.2 := rfl

/-! ## Right `ψ(Hn (n+1))`-linearity of the summand maps -/

theorem appendLeftSum_mul_appendAlgebra (i : I) (n : ℕ)
    (F : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) (r : Hn D Sc (n + 1)) :
    appendLeftSum D Sc i n (Finsupp.mapRange.addMonoidHom (AddMonoidHom.mulRight r) F) =
      appendLeftSum D Sc i n F * appendAlgebra D Sc i (n + 1) r := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, add_mul]
  | single q b =>
    obtain ⟨j, m⟩ := q
    simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
      AddMonoidHom.coe_mulRight, appendLeftSum_single, map_mul, mul_assoc]

theorem appendPolySum_mul_appendAlgebra (i : I) (n : ℕ) (G : ℕ →₀ Hn D Sc (n + 1))
    (r : Hn D Sc (n + 1)) :
    appendPolySum D Sc i n (Finsupp.mapRange.addMonoidHom (AddMonoidHom.mulRight r) G) =
      appendPolySum D Sc i n G * appendAlgebra D Sc i (n + 1) r := by
  induction G using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, add_mul]
  | single m b =>
    simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
      AddMonoidHom.coe_mulRight, appendPolySum_single, map_mul, mul_assoc]

end OddMath.QuiverHecke
end

end

section

/-!
# The two-sided append corner decomposition on induced modules

For a left `Hn (n+1)`-module `M`, the decomposition `appendCornerEquiv` of the two-sided
append corner `ψ(1) Hn (n+2) ψ(1)` descends along the balanced tensor product
`Ind M = Hn (n+2) ψ(1) ⊗_(Hn (n+1)) M`: the `ψ(1)`-fixed part of `Ind M` is

`⊕_(j ≤ n, m) ψ'(1) M  ⊕  ⊕_m M`,

with `(j, m, y) ↦ ψ(c'_j x^m) τ ⊗ y` and `(m, y) ↦ z^m ⊗ y`. Both round trips use only
`appendCornerEquiv` and the right `ψ(Hn (n+1))`-linearity of its summand maps, not
flatness of `M`. This is the module form of the append-side Mackey decomposition of
`AppendCoordinates.md` §4 (Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Lemma 8.1,
mirror form).
-/

noncomputable section
open Categorification MulOpposite
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (n : ℕ) (M : Type w) [AddCommGroup M] [Module (Hn D Sc (n + 1)) M]
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "C" => InductionAlong.Corner ψ
local notation "T" => InductionAlong.Ind M ψ

/-! ## Finite sums of elementary tensors along an additive family of corner elements -/

section Family
variable {ι : Type*} (Φ : (ι →₀ Hn D Sc (n + 1)) →+ Hn D Sc (n + 1 + 1))
  (hΦ : ∀ x, Φ x * appendAlgebra D Sc i (n + 1) 1 = Φ x)

/-- The family `Φ` with values in the right corner. -/
def appendFamilyCorner : (ι →₀ Hn D Sc (n + 1)) →+ C :=
  AddMonoidHom.codRestrict Φ _ hΦ

/-- `Σ_q Φ(single q 1) ⊗ y_q`. -/
def appendFamilyTensor : (ι →₀ M) →+ T :=
  Finsupp.liftAddHom fun q =>
    { toFun := fun y => InductionAlong.Ind.tmul
        (appendFamilyCorner D Sc i n Φ hΦ (Finsupp.single q 1)) y
      map_zero' := InductionAlong.Ind.tmul_zero _
      map_add' := InductionAlong.Ind.tmul_add _ }

@[simp] theorem appendFamilyTensor_single (q : ι) (y : M) :
    appendFamilyTensor D Sc i n M Φ hΦ (Finsupp.single q y) =
      InductionAlong.Ind.tmul (appendFamilyCorner D Sc i n Φ hΦ (Finsupp.single q 1)) y :=
  Finsupp.liftAddHom_apply_single _ _ _

/-- Old-algebra coefficients move across the tensor sign. -/
theorem appendFamilyTensor_coefficients
    (hr : ∀ q c,
      Φ (Finsupp.single q c) = Φ (Finsupp.single q 1) * appendAlgebra D Sc i (n + 1) c)
    (b : ι →₀ Hn D Sc (n + 1)) (y : M) :
    appendFamilyTensor D Sc i n M Φ hΦ
        (Finsupp.mapRange (fun c : Hn D Sc (n + 1) => c • y) (zero_smul _ y) b) =
      InductionAlong.Ind.tmul (appendFamilyCorner D Sc i n Φ hΦ b) y := by
  induction b using Finsupp.induction with
  | zero => simp [InductionAlong.Ind.zero_tmul]
  | @single_add q c b _ _ hb =>
    rw [Finsupp.mapRange_add (fun a b => add_smul a b y), map_add,
      map_add, InductionAlong.Ind.add_tmul, hb]
    congr 1
    rw [Finsupp.mapRange_single, appendFamilyTensor_single,
      ← InductionAlong.Ind.op_smul_tmul]
    congr 1
    apply Subtype.ext
    change Φ (Finsupp.single q 1) * appendAlgebra D Sc i (n + 1) c = Φ (Finsupp.single q c)
    exact (hr q c).symm

/-- A family fixed by `ψ(1)` on the left gives `ψ(1)`-fixed tensors. -/
theorem appendFamilyTensor_fixed (hl : ∀ x, appendAlgebra D Sc i (n + 1) 1 * Φ x = Φ x)
    (x : ι →₀ M) :
    (appendAlgebra D Sc i (n + 1) 1 : Hn D Sc (n + 1 + 1)) •
        appendFamilyTensor D Sc i n M Φ hΦ x =
      appendFamilyTensor D Sc i n M Φ hΦ x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, smul_add, hf, hg]
  | single q y =>
    rw [appendFamilyTensor_single, InductionAlong.Ind.smul_tmul]
    congr 1
    exact Subtype.ext (hl _)

end Family

/-! ## The two summand families -/

theorem appendLeftSum_mul_appendOne
    (F : (Fin (n + 1) × ℕ) →₀ Hn D Sc (n + 1)) :
    appendLeftSum D Sc i n F * appendAlgebra D Sc i (n + 1) 1 = appendLeftSum D Sc i n F :=
  (appendLeftSum_mem_appendTwoSidedCorner D Sc i n F).2

theorem appendPolySum_mul_appendOne (G : ℕ →₀ Hn D Sc (n + 1)) :
    appendPolySum D Sc i n G * appendAlgebra D Sc i (n + 1) 1 = appendPolySum D Sc i n G :=
  (appendPolySum_mem_appendTwoSidedCorner D Sc i n G).2

theorem appendLeftSum_single_right (q : Fin (n + 1) × ℕ) (c : Hn D Sc (n + 1)) :
    appendLeftSum D Sc i n (Finsupp.single q c) =
      appendLeftSum D Sc i n (Finsupp.single q 1) * appendAlgebra D Sc i (n + 1) c := by
  obtain ⟨j, m⟩ := q
  rw [appendLeftSum_single, appendLeftSum_single,
    mul_assoc (_ * _) (appendAlgebra D Sc i (n + 1) 1),
    ← map_mul, one_mul]

theorem appendPolySum_single_right (m : ℕ) (c : Hn D Sc (n + 1)) :
    appendPolySum D Sc i n (Finsupp.single m c) =
      appendPolySum D Sc i n (Finsupp.single m 1) * appendAlgebra D Sc i (n + 1) c := by
  rw [appendPolySum_single, appendPolySum_single,
    mul_assoc (_ ^ _) (appendAlgebra D Sc i (n + 1) 1),
    ← map_mul, one_mul]

/-- The left-crossing tensors `Σ ψ(c'_j x^m) τ ⊗ y_(j,m)`. -/
abbrev appendLeftTensor : ((Fin (n + 1) × ℕ) →₀ M) →+ T :=
  appendFamilyTensor D Sc i n M (appendLeftSum D Sc i n) (appendLeftSum_mul_appendOne D Sc i n)

/-- The polynomial tensors `Σ z^m ⊗ y_m`. -/
abbrev appendPolyTensor : (ℕ →₀ M) →+ T :=
  appendFamilyTensor D Sc i n M (appendPolySum D Sc i n) (appendPolySum_mul_appendOne D Sc i n)

/-- Left-crossing coefficients in `ψ'(1) M`. -/
def appendTensorLeftCoordinates : AddSubgroup ((Fin (n + 1) × ℕ) →₀ M) where
  carrier := {f | ∀ q, (appendAlgebra D Sc i n 1 : Hn D Sc (n + 1)) • f q = f q}
  add_mem' {f g} hf hg q := by rw [Finsupp.add_apply, smul_add, hf, hg]
  zero_mem' q := by simp
  neg_mem' {f} hf q := by rw [Finsupp.neg_apply, smul_neg, hf]

/-- The `ψ(1)`-fixed part of the induced module. -/
def appendTensorFixed : AddSubgroup T where
  carrier := {t | (appendAlgebra D Sc i (n + 1) 1 : Hn D Sc (n + 1 + 1)) • t = t}
  add_mem' {s t} hs ht := by
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_add, hs, ht]
  zero_mem' := by simp
  neg_mem' {t} ht := by
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_neg, ht]

/-! ## Coordinates of a corner element -/

theorem appendOne_mul_corner_mem (z : C) :
    appendAlgebra D Sc i (n + 1) 1 * z.1 ∈ appendTwoSidedCorner D Sc i n :=
  ⟨by rw [← mul_assoc, ← map_mul, one_mul],
    by rw [mul_assoc]; exact congrArg _ z.2⟩

/-- The coordinates `(F, G)` of `ψ(1) z` in `appendCornerEquiv`. -/
def appendCornerCoords : C →+ appendLeftCoordinates D Sc i n × (ℕ →₀ Hn D Sc (n + 1)) :=
  (appendCornerEquiv D Sc i n).symm.toAddMonoidHom.comp
    { toFun := fun z =>
        ⟨appendAlgebra D Sc i (n + 1) 1 * z.1, appendOne_mul_corner_mem D Sc i n z⟩
      map_zero' := Subtype.ext (mul_zero _)
      map_add' := fun z z' => Subtype.ext (mul_add _ z.1 z'.1) }

theorem appendCornerCoords_spec (z : C) :
    appendLeftSum D Sc i n (appendCornerCoords D Sc i n z).1 +
      appendPolySum D Sc i n (appendCornerCoords D Sc i n z).2 =
        appendAlgebra D Sc i (n + 1) 1 * z.1 := by
  rw [← appendCornerEquiv_apply]
  exact congrArg Subtype.val ((appendCornerEquiv D Sc i n).apply_symm_apply _)

theorem appendCornerCoords_op_smul (z : C) (a : Hn D Sc (n + 1)) :
    appendCornerCoords D Sc i n (op a • z) =
      (⟨Finsupp.mapRange.addMonoidHom (AddMonoidHom.mulRight a)
          (appendCornerCoords D Sc i n z).1.1, fun q => by
          simp only [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply,
            AddMonoidHom.coe_mulRight, ← mul_assoc, (appendCornerCoords D Sc i n z).1.2 q]⟩,
        Finsupp.mapRange.addMonoidHom (AddMonoidHom.mulRight a)
          (appendCornerCoords D Sc i n z).2) := by
  change (appendCornerEquiv D Sc i n).symm _ = _
  rw [AddEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [appendCornerEquiv_apply]
  change appendAlgebra D Sc i (n + 1) 1 * (z.1 * appendAlgebra D Sc i (n + 1) a) = _
  rw [appendLeftSum_mul_appendAlgebra, appendPolySum_mul_appendAlgebra, ← add_mul,
    appendCornerCoords_spec, mul_assoc]

theorem appendCornerCoords_leftSum (q : Fin (n + 1) × ℕ) :
    appendCornerCoords D Sc i n
        (appendFamilyCorner D Sc i n (appendLeftSum D Sc i n)
          (appendLeftSum_mul_appendOne D Sc i n) (Finsupp.single q 1)) =
      (⟨Finsupp.single q (appendAlgebra D Sc i n 1), fun p => by
          by_cases h : q = p
          · subst h; simp [← map_mul]
          · simp [Finsupp.single_eq_of_ne' h]⟩, 0) := by
  change (appendCornerEquiv D Sc i n).symm _ = _
  rw [AddEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [appendCornerEquiv_apply]
  change appendAlgebra D Sc i (n + 1) 1 * appendLeftSum D Sc i n (Finsupp.single q 1) = _
  rw [(appendLeftSum_mem_appendTwoSidedCorner D Sc i n _).1, map_zero, add_zero,
    ← appendLeftSum_appendLeftProj]
  simp only [appendLeftProj, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
    AddMonoidHom.coe_mulLeft, mul_one]

theorem appendCornerCoords_polySum (m : ℕ) :
    appendCornerCoords D Sc i n
        (appendFamilyCorner D Sc i n (appendPolySum D Sc i n)
          (appendPolySum_mul_appendOne D Sc i n) (Finsupp.single m 1)) =
      (0, Finsupp.single m 1) := by
  change (appendCornerEquiv D Sc i n).symm _ = _
  rw [AddEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [appendCornerEquiv_apply]
  change appendAlgebra D Sc i (n + 1) 1 * appendPolySum D Sc i n (Finsupp.single m 1) = _
  rw [(appendPolySum_mem_appendTwoSidedCorner D Sc i n _).1]
  simp

/-! ## The descent -/

/-- Coordinate extraction on the induced module, `z ⊗ y ↦ (F(ψ(1) z) y, G(ψ(1) z) y)`. -/
def appendTensorCornerBackward : T →+ ((Fin (n + 1) × ℕ) →₀ M) × (ℕ →₀ M) :=
  InductionAlong.Ind.liftAdd
    (fun z y =>
      (Finsupp.mapRange (fun b : Hn D Sc (n + 1) => b • y) (zero_smul _ y)
          (appendCornerCoords D Sc i n z).1.1,
        Finsupp.mapRange (fun b : Hn D Sc (n + 1) => b • y) (zero_smul _ y)
          (appendCornerCoords D Sc i n z).2))
    (by intros; ext q <;> simp [add_smul])
    (by intros; ext q <;> simp [smul_add])
    (by
      intro z a y
      rw [appendCornerCoords_op_smul]
      ext q <;> simp [mul_smul])

@[simp] theorem appendTensorCornerBackward_tmul (z : C) (y : M) :
    appendTensorCornerBackward D Sc i n M (InductionAlong.Ind.tmul z y) =
      (Finsupp.mapRange (fun b : Hn D Sc (n + 1) => b • y) (zero_smul _ y)
          (appendCornerCoords D Sc i n z).1.1,
        Finsupp.mapRange (fun b : Hn D Sc (n + 1) => b • y) (zero_smul _ y)
          (appendCornerCoords D Sc i n z).2) := rfl

theorem appendTensorCornerBackward_mem (t : T) :
    (appendTensorCornerBackward D Sc i n M t).1 ∈ appendTensorLeftCoordinates D Sc i n M := by
  induction t using InductionAlong.Ind.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add s t hs ht => rw [map_add]; exact add_mem hs ht
  | tmul z y =>
    intro q
    rw [appendTensorCornerBackward_tmul, Finsupp.mapRange_apply, ← mul_smul,
      (appendCornerCoords D Sc i n z).1.2 q]

/-- The forward sum `(f, g) ↦ Σ ψ(c'_j x^m) τ ⊗ f_(j,m) + Σ z^m ⊗ g_m`. -/
def appendTensorCornerForward : ((Fin (n + 1) × ℕ) →₀ M) × (ℕ →₀ M) →+ T :=
  (appendLeftTensor D Sc i n M).coprod (appendPolyTensor D Sc i n M)

theorem appendTensorCornerForward_backward (t : T) :
    appendTensorCornerForward D Sc i n M (appendTensorCornerBackward D Sc i n M t) =
      (appendAlgebra D Sc i (n + 1) 1 : Hn D Sc (n + 1 + 1)) • t := by
  induction t using InductionAlong.Ind.induction_on with
  | zero => simp
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]
  | tmul z y =>
    rw [appendTensorCornerBackward_tmul, appendTensorCornerForward, AddMonoidHom.coprod_apply,
      appendFamilyTensor_coefficients _ _ _ _ _ _ _ (appendLeftSum_single_right D Sc i n),
      appendFamilyTensor_coefficients _ _ _ _ _ _ _ (appendPolySum_single_right D Sc i n),
      ← InductionAlong.Ind.add_tmul, InductionAlong.Ind.smul_tmul]
    congr 1
    apply Subtype.ext
    exact appendCornerCoords_spec D Sc i n z

theorem appendTensorCornerBackward_leftTensor (f : (Fin (n + 1) × ℕ) →₀ M) :
    appendTensorCornerBackward D Sc i n M (appendLeftTensor D Sc i n M f) =
      (Finsupp.mapRange (fun y : M => (appendAlgebra D Sc i n 1 : Hn D Sc (n + 1)) • y)
        (smul_zero _) f, 0) := by
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, Finsupp.mapRange_zero]; rfl
  | add f g hf hg =>
    rw [map_add, map_add, hf, hg, Finsupp.mapRange_add (fun a b => smul_add _ a b),
      Prod.mk_add_mk, add_zero]
  | single q y =>
    rw [appendFamilyTensor_single, appendTensorCornerBackward_tmul, appendCornerCoords_leftSum]
    simp

theorem appendTensorCornerBackward_polyTensor (g : ℕ →₀ M) :
    appendTensorCornerBackward D Sc i n M (appendPolyTensor D Sc i n M g) = (0, g) := by
  induction g using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]; rfl
  | add f g hf hg => rw [map_add, map_add, hf, hg, Prod.mk_add_mk, add_zero]
  | single m y =>
    rw [appendFamilyTensor_single, appendTensorCornerBackward_tmul, appendCornerCoords_polySum]
    simp

theorem appendTensorCornerForward_mem
    (x : ((Fin (n + 1) × ℕ) →₀ M) × (ℕ →₀ M)) :
    appendTensorCornerForward D Sc i n M x ∈ appendTensorFixed D Sc i n M := by
  change (appendAlgebra D Sc i (n + 1) 1 : Hn D Sc (n + 1 + 1)) •
    (appendLeftTensor D Sc i n M x.1 + appendPolyTensor D Sc i n M x.2) = _
  rw [smul_add,
    appendFamilyTensor_fixed _ _ _ _ _ _ _
      (fun F => (appendLeftSum_mem_appendTwoSidedCorner D Sc i n F).1),
    appendFamilyTensor_fixed _ _ _ _ _ _ _
      (fun G => (appendPolySum_mem_appendTwoSidedCorner D Sc i n G).1)]
  rfl

/-- **Append-side Mackey decomposition of induced modules** (`AppendCoordinates.md` §4):
`ψ(1) (Hn (n+2) ψ(1) ⊗_(Hn (n+1)) M) ≅ ⊕_(j ≤ n, m) ψ'(1) M ⊕ ⊕_m M`, via
`(f, g) ↦ Σ ψ(c'_j x^m) τ ⊗ f_(j,m) + Σ z^m ⊗ g_m`. -/
def appendTensorCornerEquiv :
    appendTensorLeftCoordinates D Sc i n M × (ℕ →₀ M) ≃+ appendTensorFixed D Sc i n M where
  toFun x := ⟨appendTensorCornerForward D Sc i n M (x.1.1, x.2),
    appendTensorCornerForward_mem D Sc i n M _⟩
  invFun t := (⟨(appendTensorCornerBackward D Sc i n M t.1).1,
    appendTensorCornerBackward_mem D Sc i n M t.1⟩, (appendTensorCornerBackward D Sc i n M t.1).2)
  left_inv := by
    rintro ⟨⟨f, hf⟩, g⟩
    have h : appendTensorCornerBackward D Sc i n M
        (appendTensorCornerForward D Sc i n M (f, g)) = (f, g) := by
      rw [appendTensorCornerForward, AddMonoidHom.coprod_apply, map_add,
        appendTensorCornerBackward_leftTensor, appendTensorCornerBackward_polyTensor,
        Prod.mk_add_mk, zero_add, add_zero]
      congr 1
      ext q
      rw [Finsupp.mapRange_apply]
      exact hf q
    simp only [h]
  right_inv := by
    rintro ⟨t, ht⟩
    apply Subtype.ext
    change appendTensorCornerForward D Sc i n M (appendTensorCornerBackward D Sc i n M t) = t
    rw [appendTensorCornerForward_backward]
    exact ht
  map_add' x y := Subtype.ext (map_add (appendTensorCornerForward D Sc i n M) (x.1.1, x.2)
    (y.1.1, y.2))

theorem appendTensorCornerEquiv_apply
    (x : appendTensorLeftCoordinates D Sc i n M × (ℕ →₀ M)) :
    (appendTensorCornerEquiv D Sc i n M x : T) =
      appendLeftTensor D Sc i n M x.1 + appendPolyTensor D Sc i n M x.2 := rfl

end OddMath.QuiverHecke
end

end

section

/-!
# The twisted right dot on append-induced modules

The new dot `x_(n+2)` only supercommutes with the append map: `ψ(r) x = x ψ(tw r)`
(`affineLastDot_twist_comm`). Right multiplication by it therefore descends to the induced
module `Ind M = Hn (n+2) ψ(1) ⊗_(Hn (n+1)) M` only after twisting the coefficients. We encode
the twist by an additive map `θ : M → M` with

`θ (r • y) = tw(r) • θ y`,

where `tw` is the parity twist `homMatrixTwist (n+1) (D.parity i)`. For the regular
supermodule of the cyclotomic quotient this is the parity involution `rightDotCoefficient`
(`rightDotCoefficient_smul`).

Main results: the twisted right dot `appendTensorRightDot θ` (`z ⊗ y ↦ z x ⊗ θ y`), its action
on the two summands of `appendTensorCornerEquiv`,

* `R_t(Σ z^m ⊗ g_m) = Σ z^(m+1) ⊗ θ g_m`,
* `R_t(Σ ψ(c'_j x^m) τ ⊗ f_(j,m)) = s Σ ψ(c'_j x^(m+1)) τ ⊗ θ f_(j,m) - s (1 ⊗ Σ c'_j x^m ψ'(1) θ f_(j,m))`,

with `s = koszulSign (D.parity i) (D.parity i)`, and the stability of the `ψ(1)`-fixed part and
of the left-crossing coordinates. These are the module forms of `appendPolySum_mul_lastDot`
and `appendLeftSum_mul_lastDot` (the identities `R_t j = j t` and `R_t F = F X + j E` of
`DeformedMackeyBoundary.md`, append side; Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of
Lemma 8.1, mirror form).
-/

noncomputable section
open StringDiagrams Categorification MulOpposite
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (n : ℕ) (M : Type w) [AddCommGroup M] [Module (Hn D Sc (n + 1)) M]
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "C" => InductionAlong.Corner ψ
local notation "T" => InductionAlong.Ind M ψ

/-- Elementary tensors as an additive map in the corner variable. -/
def appendTensorCornerHom (y : M) : C →+ T :=
  AddMonoidHom.mk' (fun z => InductionAlong.Ind.tmul z y)
    (fun z z' => InductionAlong.Ind.add_tmul z z' y)

variable (θ : M →+ M)
  (hθ : ∀ (r : Hn D Sc (n + 1)) (y : M),
    θ (r • y) = homMatrixTwist D Sc (n + 1) (D.parity i) r • θ y)

/-- The twisted right dot `z ⊗ y ↦ z x_(n+2) ⊗ θ y` on the induced module. -/
def appendTensorRightDot : Module.End (Hn D Sc (n + 1 + 1)) T :=
  InductionAlong.Ind.lift
    (fun z y => InductionAlong.Ind.tmul (rightDotCorner D Sc i (n + 1) z) (θ y))
    (by intros; rw [map_add, InductionAlong.Ind.add_tmul])
    (by intros; rw [map_add, InductionAlong.Ind.tmul_add])
    (by intros; rw [rightDotCorner_op_smul, InductionAlong.Ind.op_smul_tmul, hθ])
    (by intros; rw [map_smul, InductionAlong.Ind.smul_tmul])

@[simp] theorem appendTensorRightDot_tmul (z : C) (y : M) :
    appendTensorRightDot D Sc i n M θ hθ (InductionAlong.Ind.tmul z y) =
      InductionAlong.Ind.tmul (rightDotCorner D Sc i (n + 1) z) (θ y) := rfl

/-- The twisted right dot preserves the `ψ(1)`-fixed part. -/
theorem appendTensorRightDot_mem_fixed (t : T) (ht : t ∈ appendTensorFixed D Sc i n M) :
    appendTensorRightDot D Sc i n M θ hθ t ∈ appendTensorFixed D Sc i n M := by
  change (appendAlgebra D Sc i (n + 1) 1 : Hn D Sc (n + 1 + 1)) • _ = _
  rw [← LinearMap.map_smul]
  exact congrArg _ ht

/-! ## Coordinate maps -/

/-! ## The slides -/

end OddMath.QuiverHecke
end

end

section

/-!
# The source right dot of the append Mackey boundary

For the append Mackey map `P : z ⊗ m ↦ z W ⊗ m` (`AppendMackeyMap.lean`), the source right dot
is `ρ(z ⊗ m) = z X₁ ⊗ θ m`, where `X₁` is the diagonal first dot of the prepend corner and
`θ` is the parity-twisted right action of the target. This file proves the first obligation of
the source side of `MackeyCosets` (`DeformedMackeyBoundary.md` §1; Kang–Kashiwara–Oh,
arXiv:1206.5933v2, proof of Lemma 8.1, mirror form):

  `P (ρ t) = c • R_t (P t)`,   `c = (-1)^(ε + N p(i))`,

with `R_t = appendTensorRightDot θ` (`z ⊗ y ↦ z x_last ⊗ θ y`).

The local input is the last-dot slide through `W_ν = T_ν ≫ f_i(x₁)`:

  `x_last ≫ W_ν - (-1)^(p(i) p(ν)) W_ν ≫ x₁ ∈ Kill(ν, ν)`,

proved by peeling the last letter of `ν` (`W_(ν++[x]) = σ ≫ (W_ν ▷ x)`). The dot slide (1.8)
through `σ` gives the sign `(-1)^(p(x) p(i))` and, for `x = i`, the term `W_ν ▷ i`, which is in
the killed part. On the words acting nontrivially (`q_t = ε`, i.e. `p(i) p(t) = ε + N p(i)`)
the sign is the constant `c`.

## Main results

* `lastDot_comp_appendW_mem`: the last-dot slide through `W_ν` modulo `Kill`;
* `affineFirstDot_mul_appendMoveMatrix_sub_mem`: `c X₁ W - W X_last` vanishes in `Ind_ψ N`;
* `appendSourceDot`: the source right dot `ρ` on `Ind_(φ_ε) N`;
* `appendMackeyMap_appendSourceDot`: `P ∘ ρ = c • R_t ∘ P`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory Categorification Categorification.InductionAlong
open SKM (zsign)
open scoped Classical
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

set_option quotPrecheck false in
local notation "O[" l "]" => (pres D Sc).obj (ob D l)

section Slide
variable {a : I → _root_.Polynomial k} {i : I}

/-- The dot on the last strand slides down through the last crossing (distinct colours). -/
theorem lastDotE_comp_crossLast_ne (ν : List I) {x : I} (hx : x ≠ i) :
    dotE D Sc (ν ++ [x] ++ [i]) (ν.length + 1) ≫ crossLast D Sc ν x i =
      zsign k (D.parity x * D.parity i) •
        (crossLast D Sc ν x i ≫ dotE D Sc (ν ++ [i] ++ [x]) ν.length) := by
  rw [dotE_eq, dotE_eq, crossLast, cl_comp, cl_comp]
  refine eq_zsign_smul_symm ?_
  exact (IntertwinerMeet.slide_right_ne_gen D Sc ν [] x i hx rfl (by simp) (by simp) _ _)

/-- The dot slide (1.8), right form, for equal colours on any word `l ++ [j, j] ++ r`. -/
theorem slide_right_eq_gen {t : List I} (l r : List I) (j : I) {p : ℕ} (hp : l.length = p)
    (ht : t = l ++ [j, j] ++ r) (h₁ : SChain t (pl t [.cross p, .dot p]) t)
    (h₂ : SChain t (pl t [.dot (p + 1), .cross p]) t) :
    cl D Sc t t [.cross p, .dot p] h₁ =
      zsign k (D.parity j * D.parity j) • cl D Sc t t [.dot (p + 1), .cross p] h₂ +
        cl D Sc t t [] rfl := by
  subst hp ht
  exact slide_right_eq D Sc l r j h₁ h₂

theorem crossLast_comp_dotE_self (ν : List I) :
    crossLast D Sc ν i i ≫ dotE D Sc (ν ++ [i] ++ [i]) ν.length =
      zsign k (D.parity i * D.parity i) •
        (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) ≫ crossLast D Sc ν i i) + 𝟙 _ := by
  rw [dotE_eq, dotE_eq, crossLast, cl_comp, cl_comp, ← cl_nil D Sc (ν ++ [i] ++ [i]) rfl]
  exact slide_right_eq_gen D Sc ν [] i rfl (by simp) _ _

theorem zsign_smul_zsign_smul {M : Type*} [AddCommGroup M] [Module k M] (q : ZMod 2) (m : M) :
    zsign k q • zsign k q • m = m := by
  rw [smul_smul, ← zsign_add_eq, CharTwo.add_self_eq_zero]
  simp [zsign]

/-- The dot on the last strand slides down through the last crossing (equal colours). -/
theorem lastDotE_comp_crossLast_self (ν : List I) :
    dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) ≫ crossLast D Sc ν i i =
      zsign k (D.parity i * D.parity i) •
        (crossLast D Sc ν i i ≫ dotE D Sc (ν ++ [i] ++ [i]) ν.length) -
      zsign k (D.parity i * D.parity i) • 𝟙 _ := by
  rw [crossLast_comp_dotE_self, smul_add, zsign_smul_zsign_smul, add_sub_cancel_right]

end Slide

section LastDot
variable {a : I → _root_.Polynomial k} {i : I}

theorem zsign_lastDot_append (ν : List I) (x : I) :
    zsign k (D.parity i * wordSumParity D (ν ++ [x])) =
      zsign k (D.parity x * D.parity i) * zsign k (D.parity i * wordSumParity D ν) := by
  rw [← zsign_add_eq]
  congr 1
  simp only [wordSumParity, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil]
  ring

end LastDot

/-! ## Matrix form -/

section Matrix
variable [Fintype I] (a : I → _root_.Polynomial k) (i : I) (n : ℕ)

local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

omit [Fintype I] in
theorem homMatrixTwist_comm (p q : ZMod 2) (z : Hn D Sc n) :
    homMatrixTwist D Sc n p (homMatrixTwist D Sc n q z) =
      homMatrixTwist D Sc n q (homMatrixTwist D Sc n p z) := by
  induction z using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [ha, hb]
  | hs s t f => simp [← Supercategory.twist_add, add_comm]

theorem prependTwist_apply (ε : ZMod 2) (r : Hn D Sc (n + 1)) :
    prependTwist D Sc i n ε r = prependAlgebra D Sc i (n + 1) (homMatrixTwist D Sc (n + 1) ε r) :=
  rfl

theorem prependTwist_one (ε : ZMod 2) :
    prependTwist D Sc i n ε 1 = prependAlgebra D Sc i (n + 1) 1 := by
  rw [prependTwist_apply, homMatrixTwist_one]

theorem affineFirstDot_mul_prependTwist_one (ε : ZMod 2) :
    affineFirstDot D Sc i (n + 1) * prependTwist D Sc i n ε 1 = affineFirstDot D Sc i (n + 1) := by
  rw [prependTwist_one, affineFirstDot_mul_prepend_one]

/-- The first dot intertwines `φ_ε` with its parity twist. -/
theorem prependTwist_mul_affineFirstDot (ε : ZMod 2) (r : Hn D Sc (n + 1)) :
    prependTwist D Sc i n ε r * affineFirstDot D Sc i (n + 1) =
      affineFirstDot D Sc i (n + 1) *
        prependTwist D Sc i n ε (homMatrixTwist D Sc (n + 1) (D.parity i) r) := by
  rw [prependTwist_apply, prependTwist_apply, affineFirstDot_twist_comm, homMatrixTwist_comm]

/-- The constant sign `(-1)^(ε + N p(i))` of the last-dot slide on words with `q_t = ε`. -/
def appendSourceSign (ε : ZMod 2) : ZMod 2 := ε - (a i).natDegree • D.parity i

end Matrix

section Vanishing
variable [Fintype I] {a : I → _root_.Polynomial k} {i : I} {n : ℕ} {ε : ZMod 2}
  {N : Type w} [AddCommGroup N] [Module (Hn D Sc (n + 1)) N]

local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

end Vanishing

/-! ## The source right dot on the induced module -/

section Source
variable [Fintype I] (i : I) (n : ℕ) (ε : ZMod 2)

/-- Right multiplication by the first dot on the corner of `φ_ε`. -/
def sourceDotCorner :
    InductionAlong.Corner (prependTwist D Sc i n ε) →ₗ[Hn D Sc (n + 1 + 1)] InductionAlong.Corner (prependTwist D Sc i n ε) where
  toFun z := ⟨z.1 * affineFirstDot D Sc i (n + 1), by
    change (z.1 * affineFirstDot D Sc i (n + 1)) * prependTwist D Sc i n ε 1 = _
    rw [mul_assoc, affineFirstDot_mul_prependTwist_one]⟩
  map_add' z z' := Subtype.ext (add_mul _ _ _)
  map_smul' r z := Subtype.ext (mul_assoc _ _ _)

@[simp] theorem sourceDotCorner_val (z : InductionAlong.Corner (prependTwist D Sc i n ε)) :
    (sourceDotCorner D Sc i n ε z).1 = z.1 * affineFirstDot D Sc i (n + 1) := rfl

theorem sourceDotCorner_op_smul (z : InductionAlong.Corner (prependTwist D Sc i n ε)) (r : Hn D Sc (n + 1)) :
    sourceDotCorner D Sc i n ε (MulOpposite.op r • z) =
      MulOpposite.op (homMatrixTwist D Sc (n + 1) (D.parity i) r) •
        sourceDotCorner D Sc i n ε z := by
  apply Subtype.ext
  change (z.1 * prependTwist D Sc i n ε r) * affineFirstDot D Sc i (n + 1) = _
  rw [mul_assoc, prependTwist_mul_affineFirstDot, ← mul_assoc]
  rfl

variable {N : Type w} [AddCommGroup N] [Module (Hn D Sc (n + 1)) N] (θ : N →+ N)
  (hθ : ∀ (r : Hn D Sc (n + 1)) (y : N),
    θ (r • y) = homMatrixTwist D Sc (n + 1) (D.parity i) r • θ y)

/-- **The source right dot** `ρ : z ⊗ y ↦ z X₁ ⊗ θ y` on `Ind_(φ_ε) N`. -/
def appendSourceDot : Module.End (Hn D Sc (n + 1 + 1)) (Ind N (prependTwist D Sc i n ε)) :=
  Ind.lift (fun z y => Ind.tmul (sourceDotCorner D Sc i n ε z) (θ y))
    (by intros; rw [map_add, Ind.add_tmul])
    (by intros; rw [map_add, Ind.tmul_add])
    (by intros; rw [sourceDotCorner_op_smul, Ind.op_smul_tmul, hθ])
    (by intros; rw [map_smul, Ind.smul_tmul])

@[simp] theorem appendSourceDot_tmul (z : InductionAlong.Corner (prependTwist D Sc i n ε)) (y : N) :
    appendSourceDot D Sc i n ε θ hθ (Ind.tmul z y) =
      Ind.tmul (sourceDotCorner D Sc i n ε z) (θ y) := rfl

end Source

end OddMath.QuiverHecke
end

end

section

/-!
# Decorated moving-dot deletion in the ELV append presentation

The moving-dot step of `DeformedGlobalQP.md` §4, with the dot decoration
placed before the full ELV relation. No commutation of an odd dot with that
relation is used. The same-colour correction is the right extension of a
shorter old ideal element.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

set_option quotPrecheck false in
local notation "O[" l "]" => (pres D Sc).obj (ob D l)

/-- The decoration is between the moving braid and the ELV relation. -/
def appendDecoratedW (i : I) (s : List I) (d : ℕ) :
    hom D Sc cutoff (s ++ [i]) (i :: s) :=
  affineUnit D Sc cutoff _ _ (lastToFirstHom D Sc i s) ≫
    movingPower D Sc cutoff i s d ≫ relation D Sc cutoff i s

/-- Zero decoration recovers the old-generator morphism. -/
@[simp] theorem appendDecoratedW_zero (i : I) (s : List I) :
    appendDecoratedW D Sc cutoff i s 0 = appendW D Sc cutoff i s := by
  have h : movingPower D Sc cutoff i s 0 = 𝟙 (obj D Sc cutoff (i :: s)) := by
    change affineUnit D Sc cutoff _ _ (dotE D Sc (i :: s) 0 ^ 0) = _
    rw [pow_zero, End.one_def, affineUnit_id]
  rw [appendDecoratedW, h, Category.id_comp, appendW]

/-- The shorter decorated morphism remains in the full old ideal. -/
theorem appendDecoratedW_mem_ideal (i : I) (s : List I) (d : ℕ) :
    appendDecoratedW D Sc cutoff i s d ∈ ideal D Sc cutoff (s ++ [i]) (i :: s) :=
  comp_ideal D Sc cutoff _ (comp_ideal D Sc cutoff _ (relation_mem D Sc cutoff i s))

private theorem movingPower_rightContext (i : I) (s : List I) (x : I) (d : ℕ) :
    rightContext D Sc cutoff [x] _ _ (movingPower D Sc cutoff i s d) =
      movingPower D Sc cutoff i (s ++ [x]) d := by
  change affineUnit D Sc cutoff _ _ ((dotE D Sc (i :: s) 0 ^ d) ▷ O[[x]]) = _
  have h : (dotE D Sc (i :: s) 0 ^ d) ▷ O[[x]] =
      dotE D Sc (i :: (s ++ [x])) 0 ^ d := by
    change whiskerWordRingHom D Sc (i :: s) [x] (_ ^ d) = _
    rw [map_pow, whiskerWordRingHom_apply, dotE_whiskerRight D Sc (i :: s) [x] 0 (by simp)]
    rfl
  rw [h]
  rfl

/-- Peeling a final old letter preserves the order of decoration and relation. -/
theorem appendDecoratedW_append (i : I) (s : List I) (x : I) (d : ℕ) :
    appendDecoratedW D Sc cutoff i (s ++ [x]) d =
      affineUnit D Sc cutoff _ _ (crossLast D Sc s x i) ≫
        rightContext D Sc cutoff [x] _ _ (appendDecoratedW D Sc cutoff i s d) := by
  have ht : lastToFirstHom D Sc i (s ++ [x]) =
      crossLast D Sc s x i ≫ affineRightContext D Sc [x] _ _ (lastToFirstHom D Sc i s) :=
    lastToFirstHom_append_singleton D Sc i x s
  unfold appendDecoratedW
  rw [ht, affineUnit_comp D Sc cutoff (v := s ++ [x] ++ [i])
    (w := s ++ [i] ++ [x]) (z := i :: (s ++ [x])),
    rightContext_comp, rightContext_comp, rightContext_relation,
    movingPower_rightContext, rightContext_affineUnit, Category.assoc]
  rfl

/-- Last-dot deletion with arbitrary moving decoration, before commuting the relation. -/
theorem lastDot_comp_appendDecoratedW_mem (i : I) (s : List I) (d : ℕ) :
    affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length) ≫
        appendDecoratedW D Sc cutoff i s d -
      SKM.zsign k (D.parity i * wordSumParity D s) •
        appendDecoratedW D Sc cutoff i s (d + 1) ∈
      appendRelations D Sc cutoff i s (i :: s) := by
  induction s using List.reverseRecOn with
  | nil =>
    have hz : SKM.zsign k (D.parity i * wordSumParity D ([] : List I)) = 1 := by
      simp [wordSumParity, SKM.zsign]
    rw [hz, one_smul]
    have he : affineUnit D Sc cutoff _ _ (dotE D Sc [i] 0) ≫
        appendDecoratedW D Sc cutoff i [] d = appendDecoratedW D Sc cutoff i [] (d + 1) := by
      change affineUnit D Sc cutoff [i] [i] (dotE D Sc [i] 0) ≫
        (𝟙 _ ≫ affineUnit D Sc cutoff [i] [i] (dotE D Sc [i] 0 ^ d) ≫ _) =
        𝟙 _ ≫ affineUnit D Sc cutoff [i] [i] (dotE D Sc [i] 0 ^ (d + 1)) ≫ _
      rw [Category.id_comp, Category.id_comp, ← Category.assoc,
        ← affineUnit_comp, pow_succ, End.mul_def]
    convert Submodule.zero_mem (appendRelations D Sc cutoff i [] [i]) using 1
    exact sub_eq_zero.mpr he
  | append_singleton s x ih =>
    set c := SKM.zsign k (D.parity i * wordSumParity D s) with hc
    set K := affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length) ≫
      appendDecoratedW D Sc cutoff i s d - c • appendDecoratedW D Sc cutoff i s (d + 1) with hK
    have hdK : affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length) ≫
        appendDecoratedW D Sc cutoff i s d =
        K + c • appendDecoratedW D Sc cutoff i s (d + 1) := by
      rw [hK, sub_add_cancel]
    have e1 : affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i] ++ [x]) s.length) =
        rightContext D Sc cutoff [x] _ _
          (affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length)) := by
      rw [rightContext_affineUnit]
      exact congrArg (affineUnit D Sc cutoff _ _)
        (dotE_whiskerRight D Sc (s ++ [i]) [x] s.length (by simp)).symm
    have main : affineUnit D Sc cutoff _ _ (crossLast D Sc s x i) ≫
        (rightContext D Sc cutoff [x] _ _
          (affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length)) ≫
            rightContext D Sc cutoff [x] _ _ (appendDecoratedW D Sc cutoff i s d)) =
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s x i) ≫
          rightContext D Sc cutoff [x] _ _ K :
            hom D Sc cutoff (s ++ [x] ++ [i]) (i :: (s ++ [x]))) +
          c • appendDecoratedW D Sc cutoff i (s ++ [x]) (d + 1) := by
      rw [← rightContext_comp, hdK, map_add, map_smul, Preadditive.comp_add,
        Linear.comp_smul, appendDecoratedW_append]
    rw [zsign_lastDot_append, show (s ++ [x]).length = s.length + 1 by simp,
      appendDecoratedW_append, ← Category.assoc, ← affineUnit_comp]
    rcases eq_or_ne x i with rfl | hx
    · rw [lastDotE_comp_crossLast_self, map_sub, map_smul, map_smul,
        affineUnit_comp, affineUnit_id, Preadditive.sub_comp, Linear.smul_comp,
        Linear.smul_comp, Category.assoc, e1, main, Category.id_comp,
        smul_add, smul_smul]
      have h1 := crossLast_comp_mem_appendRelations D Sc cutoff x x ih
      have h2 := rightContext_mem_appendRelations D Sc cutoff x
        (appendDecoratedW_mem_ideal D Sc cutoff x s d)
      rw [← hc]
      have key : ∀ A B C : hom D Sc cutoff (s ++ [x] ++ [x]) (x :: (s ++ [x])),
          A + B - C - B = A - C := fun _ _ _ => by abel
      rw [key]
      exact sub_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
    · rw [lastDotE_comp_crossLast_ne D Sc s hx, map_smul, affineUnit_comp,
        Linear.smul_comp, Category.assoc, e1, main, smul_add, smul_smul,
        add_sub_cancel_right]
      exact Submodule.smul_mem _ _ (crossLast_comp_mem_appendRelations D Sc cutoff i x ih)

/-- Even an odd trailing dot preserves the append span: it twists the old factor. -/
theorem lastDot_comp_mem_appendRelations (i : I) {s w : List I}
    {h : hom D Sc cutoff (s ++ [i]) w}
    (hh : h ∈ appendRelations D Sc cutoff i s w) :
    affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length) ≫ h ∈
      appendRelations D Sc cutoff i s w := by
  rw [← whiskerLeft_dotE D Sc s i rfl]
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, f, rfl⟩ := hh
    rw [← Category.assoc, trailing_comp_rightContext D Sc cutoff (firstDot_parity D Sc i []),
      Category.assoc]
    exact appendRelations_mem D Sc cutoff i (twist_ideal D Sc cutoff _ hr) _
  | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c ha

/-- Two decorated slides cancel the sign, still without commuting the ELV relation. -/
theorem lastDotSquare_comp_appendDecoratedW_mem (i : I) (s : List I) (d : ℕ) :
    affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length ^ 2) ≫
        appendDecoratedW D Sc cutoff i s d - appendDecoratedW D Sc cutoff i s (d + 2) ∈
      appendRelations D Sc cutoff i s (i :: s) := by
  let L := affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length)
  let c := SKM.zsign k (D.parity i * wordSumParity D s)
  have h₁ := lastDot_comp_mem_appendRelations D Sc cutoff i
    (lastDot_comp_appendDecoratedW_mem D Sc cutoff i s d)
  have h₂ := Submodule.smul_mem (appendRelations D Sc cutoff i s (i :: s)) c
    (lastDot_comp_appendDecoratedW_mem D Sc cutoff i s (d + 1))
  have hc : c * c = 1 := by
    dsimp [c]
    rw [← zsign_add_eq, CharTwo.add_self_eq_zero]
    simp [SKM.zsign]
  have he : affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length ^ 2) = L ≫ L := by
    rw [pow_two, End.mul_def, affineUnit_comp]
  rw [he]
  have h := Submodule.add_mem _ h₁ h₂
  change L ≫ (L ≫ appendDecoratedW D Sc cutoff i s d -
      c • appendDecoratedW D Sc cutoff i s (d + 1)) +
    c • (L ≫ appendDecoratedW D Sc cutoff i s (d + 1) -
      c • appendDecoratedW D Sc cutoff i s (d + 2)) ∈ _ at h
  simpa only [Preadditive.comp_sub, Linear.comp_smul, smul_sub, smul_smul, hc,
    one_smul, sub_add_sub_cancel, Category.assoc] using h

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# The target side of the append-side Mackey boundary

`MackeyCosets` (`BoundaryCosets.lean`) bundles claims about the target `L₀` (its decomposition
`L₀ = F(L₀') ⊕ j(V₀)`, the dot slides and the right `B`-action) with claims about the source
`L₁` and the map `P`. `MackeyTarget` records the target-side fields alone, and
`MackeyCosets.ofTarget` assembles a `MackeyCosets` from them and the source-side data.

For a ring `B` that is a left `Hn (n+1)`-module with `(r • y) b = r • (y b)`, and a ring
endomorphism `σ` of `B` with `σ (r • y) = tw(r) • σ y` (`tw` the parity twist of the appended
colour), `appendMackeyTarget` instantiates every target-side field on

* `L₀ = ψ(1) (Hn (n+2) ψ(1) ⊗_(Hn (n+1)) B)` (`appendTensorFixed`),
* `L₀' = ⊕_(j ≤ n, m) ψ'(1) B` (`appendTensorLeftCoordinates`),

with `F`, `j` the two summands of `appendTensorCornerEquiv` (so `direct` and `span` are that
equivalence), `R_t` the `σ`-twisted right dot `appendTensorRightDot`, and the right `B`-action
`z ⊗ y ↦ z ⊗ y b`. This is the target of `DeformedMackeyBoundary.md` (append side,
`AppendCoordinates.md` §4; Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Lemma 8.1, mirror
form).
-/

noncomputable section
open Finsupp Categorification StringDiagrams

namespace OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

variable {B : Type*} [Ring B] (σ : B →+* B)

/-- The target-side fields of `MackeyCosets`. -/
structure MackeyTarget (L₀ L₀' : Type*) [AddCommGroup L₀] [AddCommGroup L₀'] where
  /-- The target right-dot action `R_t`. -/
  Rt : L₀ →+ L₀
  /-- The crossing summand `F : L₀' → L₀`. -/
  F : L₀' →+ L₀
  /-- The polynomial summand. -/
  j : (ℕ →₀ B) →+ L₀
  /-- The crossing-contraction operator `X` on `L₀'`. -/
  X : L₀' →+ L₀'
  /-- The degree-zero operator `E : L₀' → B`. -/
  E : L₀' →+ B
  /-- The right `B`-action on the target. -/
  r₀ : B → L₀ →+ L₀
  Rt_F : ∀ u, Rt (F u) = F (X u) + j (single 0 (E u))
  Rt_j : ∀ f, Rt (j f) = j (tShift σ f)
  direct : ∀ u f, F u + j f = 0 → u = 0 ∧ f = 0
  span : ∀ y, ∃ u f, y = F u + j f
  F_r : ∀ (b : B) u, ∃ u', r₀ b (F u) = F u'
  j_r : ∀ (b : B) f, r₀ b (j f) = j (rsmul b f)

end OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

namespace OddMath.QuiverHecke
open CyclotomicAction.BoundaryPolynomial
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (n : ℕ) (B : Type w) [Ring B] [Module (Hn D Sc (n + 1)) B]
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "T" => InductionAlong.Ind B ψ

/-! ## The two summands -/

/-- The crossing summand `F u = Σ ψ(c'_j x^m) τ ⊗ u_(j,m)`. -/
def appendTargetF : appendTensorLeftCoordinates D Sc i n B →+ appendTensorFixed D Sc i n B :=
  (appendTensorCornerEquiv D Sc i n B).toAddMonoidHom.comp (AddMonoidHom.inl _ _)

/-- The polynomial summand `j g = Σ z^m ⊗ g_m`. -/
def appendTargetJ : (ℕ →₀ B) →+ appendTensorFixed D Sc i n B :=
  (appendTensorCornerEquiv D Sc i n B).toAddMonoidHom.comp (AddMonoidHom.inr _ _)

@[simp] theorem appendTargetF_coe (u : appendTensorLeftCoordinates D Sc i n B) :
    (appendTargetF D Sc i n B u : T) = appendLeftTensor D Sc i n B u.1 := by
  simp [appendTargetF, appendTensorCornerEquiv_apply]

@[simp] theorem appendTargetJ_coe (f : ℕ →₀ B) :
    (appendTargetJ D Sc i n B f : T) = appendPolyTensor D Sc i n B f := by
  simp [appendTargetJ, appendTensorCornerEquiv_apply]

/-! ## The twisted right dot -/

variable (σ : B →+* B)
  (hσ : ∀ (r : Hn D Sc (n + 1)) (y : B),
    σ (r • y) = homMatrixTwist D Sc (n + 1) (D.parity i) r • σ y)

/-- The `σ`-twisted right dot on the `ψ(1)`-fixed part. -/
def appendTargetRt : appendTensorFixed D Sc i n B →+ appendTensorFixed D Sc i n B :=
  AddMonoidHom.codRestrict
    ((appendTensorRightDot D Sc i n B σ.toAddMonoidHom hσ).toAddMonoidHom.comp
      (appendTensorFixed D Sc i n B).subtype)
    _ fun t => appendTensorRightDot_mem_fixed D Sc i n B _ hσ t.1 t.2

@[simp] theorem appendTargetRt_coe (t : appendTensorFixed D Sc i n B) :
    (appendTargetRt D Sc i n B σ hσ t : T) =
      appendTensorRightDot D Sc i n B σ.toAddMonoidHom hσ t.1 := rfl

/-! ## Right multiplication on the coefficients -/

variable [IsScalarTower (Hn D Sc (n + 1)) B B]

end OddMath.QuiverHecke
end

end

section

/-!
# The append Mackey target on the content corner of the cyclotomic quotient

Let `A = Hn (n+1) / I^Λ` be the cyclotomic quotient (`CyclotomicAlgebra`) and
`e = e(β)` the content idempotent of a multiset `β` (`cyclotomicContentIdempotent`), which is
central and even. The coefficient ring of the append-side Mackey boundary
(`DeformedMackeyBoundary.md`, append side; Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of
Lemma 8.1) is the corner `B_β = e A e` (`CyclotomicContentCorner`), a ring with unit `e`:

* `B_β` is a left `Hn (n+1)`-module through `A`, with `(r • y) b = r • (y b)`;
* the parity involution `φ_i = coefficientParityHom (D.parity i)` fixes `e` and restricts to a
  ring endomorphism `σ_β` of `B_β` (`contentCornerParity`) with
  `σ_β (r • y) = tw(r) • σ_β y` (`contentCornerParity_smul`), where `tw` is the parity twist of
  the appended colour; the identity `φ_i = rightDotCoefficient i`
  (`coefficientParityHom_parity_eq_rightDotCoefficient`) brings in `rightDotCoefficient_smul`.

`appendContentMackeyTarget` is then `appendMackeyTarget` at `B_β`, `σ_β`: the target side of
`MackeyCosets` on `L₀ = ψ(1) (Hn (n+2) ψ(1) ⊗_(Hn (n+1)) B_β)`, with `direct` and `span` the
decomposition `L₀ = F(L₀') ⊕ j(V₀)` of `appendTensorCornerEquiv`.
-/

noncomputable section
open StringDiagrams Categorification Supercategory

namespace OddMath.QuiverHecke

universe u v

variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I)

theorem cyclotomicContentIdempotent_isIdempotentElem :
    IsIdempotentElem (cyclotomicContentIdempotent D Sc a n β) :=
  cyclotomicContentIdempotent_sq D Sc a n β

/-- The content-`β` corner `e(β) A e(β)` of the cyclotomic quotient `A`, a ring with unit
`e(β)`. -/
abbrev CyclotomicContentCorner :=
  (cyclotomicContentIdempotent_isIdempotentElem D Sc a n β).Corner

theorem cyclotomicContentCorner_mem_iff (x : CyclotomicAlgebra D Sc a n) :
    x ∈ Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) ↔
      cyclotomicContentIdempotent D Sc a n β * x = x :=
  (Subsemigroup.mem_corner_iff (cyclotomicContentIdempotent_isIdempotentElem D Sc a n β)).trans
    ⟨fun h => h.1, fun h => ⟨h, by rw [← cyclotomicContentIdempotent_central, h]⟩⟩

/-- The underlying element of the quotient. -/
def contentCornerVal (x : CyclotomicContentCorner D Sc a n β) : CyclotomicAlgebra D Sc a n :=
  (show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from x).1

theorem contentCornerVal_mem (x : CyclotomicContentCorner D Sc a n β) :
    contentCornerVal D Sc a n β x ∈ Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) :=
  (show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from x).2

/-- The corner element of an element of the corner subsemigroup. -/
def contentCornerMk (y : CyclotomicAlgebra D Sc a n)
    (hy : y ∈ Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β)) :
    CyclotomicContentCorner D Sc a n β :=
  show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from ⟨y, hy⟩

@[simp] theorem contentCornerVal_mk (y : CyclotomicAlgebra D Sc a n)
    (hy : y ∈ Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β)) :
    contentCornerVal D Sc a n β (contentCornerMk D Sc a n β y hy) = y := rfl

theorem contentCornerVal_injective : Function.Injective (contentCornerVal D Sc a n β) :=
  fun x y h => (Subtype.ext h :
    (show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from x) =
      show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from y)

theorem contentCornerVal_e_mul (x : CyclotomicContentCorner D Sc a n β) :
    cyclotomicContentIdempotent D Sc a n β * contentCornerVal D Sc a n β x =
      contentCornerVal D Sc a n β x :=
  (cyclotomicContentCorner_mem_iff D Sc a n β _).mp (contentCornerVal_mem D Sc a n β x)

theorem cyclotomicContentCorner_mul_mem (z : CyclotomicAlgebra D Sc a n)
    (x : CyclotomicContentCorner D Sc a n β) :
    z * contentCornerVal D Sc a n β x ∈
      Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) := by
  rw [cyclotomicContentCorner_mem_iff, ← mul_assoc, cyclotomicContentIdempotent_central,
    mul_assoc, contentCornerVal_e_mul]

/-- The inclusion of the corner as an additive map. -/
def contentCornerValHom :
    CyclotomicContentCorner D Sc a n β →+ CyclotomicAlgebra D Sc a n where
  toFun := contentCornerVal D Sc a n β
  map_zero' := rfl
  map_add' _ _ := rfl

instance : SMul (Hn D Sc (n + 1)) (CyclotomicContentCorner D Sc a n β) :=
  ⟨fun r x => contentCornerMk D Sc a n β (r • contentCornerVal D Sc a n β x) (by
    exact cyclotomicContentCorner_mul_mem D Sc a n β (cyclotomicMk D Sc a n r) x)⟩

instance : Module (Hn D Sc (n + 1)) (CyclotomicContentCorner D Sc a n β) :=
  Function.Injective.module _ (contentCornerValHom D Sc a n β)
    (contentCornerVal_injective D Sc a n β) fun _ _ => rfl

instance : IsScalarTower (Hn D Sc (n + 1)) (CyclotomicContentCorner D Sc a n β)
    (CyclotomicContentCorner D Sc a n β) :=
  ⟨fun r x y => contentCornerVal_injective D Sc a n β
    (smul_mul_assoc r (contentCornerVal D Sc a n β x) (contentCornerVal D Sc a n β y))⟩

variable (i : I) (ha : CyclotomicPolynomialParity D a)

/-- The parity involution fixes the (even) content idempotent. -/
theorem coefficientParityHom_contentIdempotent (p : ZMod 2) :
    coefficientParityHom D Sc a ha n p (cyclotomicContentIdempotent D Sc a n β) =
      cyclotomicContentIdempotent D Sc a n β := by
  change (cyclotomicSuperspace D Sc a ha n).sgn p _ = _
  rw [SVec.sgn_apply_of_mem p (cyclotomicContentIdempotent_parity D Sc a ha n β)]
  simp

/-- The parity involution of the appended colour, restricted to the content corner. -/
def contentCornerParity :
    CyclotomicContentCorner D Sc a n β →+* CyclotomicContentCorner D Sc a n β where
  toFun x := contentCornerMk D Sc a n β
    (coefficientParityHom D Sc a ha n (D.parity i) (contentCornerVal D Sc a n β x)) (by
      rw [cyclotomicContentCorner_mem_iff, ← coefficientParityHom_contentIdempotent D Sc a n β ha
          (D.parity i), ← map_mul, contentCornerVal_e_mul])
  map_zero' := contentCornerVal_injective D Sc a n β (map_zero _)
  map_add' x y := contentCornerVal_injective D Sc a n β (map_add _ _ _)
  map_one' := contentCornerVal_injective D Sc a n β
    (coefficientParityHom_contentIdempotent D Sc a n β ha (D.parity i))
  map_mul' x y := contentCornerVal_injective D Sc a n β (map_mul _ _ _)

end OddMath.QuiverHecke
end

end

section

/-!
# Coordinates of the twisted prepend induction

The source module of the append-side Mackey boundary is `Ind_(φ_ε) N` with
`φ_ε = prependAlgebra i (n+1) ∘ tw_ε` (`prependTwist`); the parity shift `Π^ε` of
`docs/Nondegeneracy/DeformedMackeyBoundary.md` §1 is the twist `tw_ε`. Since
`tw_ε` is an involution fixing `1`, inducing along `φ_ε` is the same as inducing
along `prependAlgebra i (n+1)` from the twisted module `N^ε` (`TwistModule`), on
which `r` acts as `tw_ε(r)`.

## Main results

* `TwistModule`: `N` with the action precomposed by the parity twist.
* `prependTwistEquiv`: `Ind_(φ_ε) N ≃+ Ind_(prependAlgebra) N^ε`, `z ⊗ m ↦ z ⊗ m`.
* `prependTwistCoordinates`: the affine prepend PBW coordinates of `Ind_(φ_ε) N`,
  `((PrependShuffle (n+1) × ℕ) →₀ N) ≃+ Ind_(φ_ε) N`, sending `single (u, l) m` to
  `prependPBWCorner u l 1 ⊗ m`.
-/

noncomputable section
open CategoryTheory Categorification Categorification.InductionAlong MulOpposite
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

section Twist
variable (n : ℕ) (p : ZMod 2)

/-- The parity twist as a unital ring endomorphism. -/
def homMatrixTwistRingHom : Hn D Sc n →+* Hn D Sc n :=
  { (homMatrixTwistAlgebra D Sc n p : Hn D Sc n →ₙ+* Hn D Sc n) with
    map_one' := homMatrixTwist_one D Sc n p }

@[simp] theorem homMatrixTwistRingHom_apply (r : Hn D Sc n) :
    homMatrixTwistRingHom D Sc n p r = homMatrixTwist D Sc n p r := rfl

variable (N : Type w) [AddCommGroup N] [Module (Hn D Sc n) N]

/-- `N` with the action precomposed by the parity twist `tw_p`. -/
@[nolint unusedArguments]
def TwistModule (_ : SKM.Scalars D k) (_ : ℕ) (_ : ZMod 2) (N : Type w) : Type w := N

instance : AddCommGroup (TwistModule D Sc n p N) := inferInstanceAs (AddCommGroup N)

instance : Module (Hn D Sc n) (TwistModule D Sc n p N) :=
  Module.compHom N (homMatrixTwistRingHom D Sc n p)

/-- The identity of the underlying group. -/
def toTwistModule : N ≃+ TwistModule D Sc n p N := AddEquiv.refl N

theorem smul_toTwistModule (r : Hn D Sc n) (m : N) :
    r • toTwistModule D Sc n p N m = toTwistModule D Sc n p N (homMatrixTwist D Sc n p r • m) :=
  rfl

theorem toTwistModule_smul (r : Hn D Sc n) (m : N) :
    toTwistModule D Sc n p N (r • m) = homMatrixTwist D Sc n p r • toTwistModule D Sc n p N m := by
  rw [smul_toTwistModule, homMatrixTwist_twice]

end Twist

variable (i : I) (n : ℕ) (ε : ZMod 2) (N : Type w) [AddCommGroup N]
  [Module (Hn D Sc (n + 1)) N]

local notation "φ" => (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

/-- The two corners agree: `φ_ε(1) = φ(1)`. -/
def prependTwistCorner : InductionAlong.Corner (prependTwist D Sc i n ε) ≃+ InductionAlong.Corner φ where
  toFun z := ⟨z.1, by
    change z.1 * prependAlgebra D Sc i (n + 1) 1 = z.1
    have h : z.1 * prependTwist D Sc i n ε 1 = z.1 := z.2
    exact (congrArg (z.1 * ·) (prependTwist_one D Sc i n ε)).symm.trans h⟩
  invFun z := ⟨z.1, by
    change z.1 * prependTwist D Sc i n ε 1 = z.1
    have h : z.1 * prependAlgebra D Sc i (n + 1) 1 = z.1 := z.2
    exact (congrArg (z.1 * ·) (prependTwist_one D Sc i n ε)).trans h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp] theorem prependTwistCorner_val (z : InductionAlong.Corner (prependTwist D Sc i n ε)) :
    (prependTwistCorner D Sc i n ε z).1 = z.1 := rfl

@[simp] theorem prependTwistCorner_symm_val (z : InductionAlong.Corner φ) :
    ((prependTwistCorner D Sc i n ε).symm z).1 = z.1 := rfl

theorem prependTwistCorner_op_smul (a : Hn D Sc (n + 1))
    (z : InductionAlong.Corner (prependTwist D Sc i n ε)) :
    prependTwistCorner D Sc i n ε (op a • z) =
      op (homMatrixTwist D Sc (n + 1) ε a) • prependTwistCorner D Sc i n ε z := rfl

/-- The forward map `z ⊗ m ↦ z ⊗ m` from `Ind_(φ_ε) N` to `Ind_φ N^ε`. -/
def prependTwistForward : Ind N (prependTwist D Sc i n ε) →+ Ind (TwistModule D Sc (n + 1) ε N) φ :=
  Ind.liftAdd
    (fun z m => Ind.tmul (prependTwistCorner D Sc i n ε z) (toTwistModule D Sc (n + 1) ε N m))
    (fun _ _ _ => by rw [map_add, Ind.add_tmul])
    (fun _ _ _ => by rw [map_add, Ind.tmul_add])
    (fun z a m => by
      rw [prependTwistCorner_op_smul, Ind.op_smul_tmul, toTwistModule_smul])

theorem prependTwistForward_tmul (z : InductionAlong.Corner (prependTwist D Sc i n ε)) (m : N) :
    prependTwistForward D Sc i n ε N (Ind.tmul z m) =
      Ind.tmul (prependTwistCorner D Sc i n ε z) (toTwistModule D Sc (n + 1) ε N m) := rfl

/-- The backward map `z ⊗ m ↦ z ⊗ m` from `Ind_φ N^ε` to `Ind_(φ_ε) N`. -/
def prependTwistBackward : Ind (TwistModule D Sc (n + 1) ε N) φ →+ Ind N (prependTwist D Sc i n ε) :=
  Ind.liftAdd
    (fun z m => Ind.tmul ((prependTwistCorner D Sc i n ε).symm z)
      ((toTwistModule D Sc (n + 1) ε N).symm m))
    (fun _ _ _ => by rw [map_add, Ind.add_tmul])
    (fun _ _ _ => by rw [map_add, Ind.tmul_add])
    (fun z a m => by
      have h : (prependTwistCorner D Sc i n ε).symm (op a • z) =
          op (homMatrixTwist D Sc (n + 1) ε a) • (prependTwistCorner D Sc i n ε).symm z :=
        Subtype.ext (by
          change z.1 * prependAlgebra D Sc i (n + 1) a =
            z.1 * prependAlgebra D Sc i (n + 1)
              (homMatrixTwist D Sc (n + 1) ε (homMatrixTwist D Sc (n + 1) ε a))
          rw [homMatrixTwist_twice])
      rw [h, Ind.op_smul_tmul]
      rfl)

theorem prependTwistBackward_tmul (z : InductionAlong.Corner φ)
    (m : TwistModule D Sc (n + 1) ε N) :
    prependTwistBackward D Sc i n ε N (Ind.tmul z m) =
      Ind.tmul ((prependTwistCorner D Sc i n ε).symm z) ((toTwistModule D Sc (n + 1) ε N).symm m) :=
  rfl

/-- `Ind_(φ_ε) N ≃+ Ind_φ N^ε`, `z ⊗ m ↦ z ⊗ m`. -/
def prependTwistEquiv :
    Ind N (prependTwist D Sc i n ε) ≃+ Ind (TwistModule D Sc (n + 1) ε N) φ where
  toFun := prependTwistForward D Sc i n ε N
  invFun := prependTwistBackward D Sc i n ε N
  left_inv t := by
    induction t using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z m =>
      rw [prependTwistForward_tmul, prependTwistBackward_tmul, AddEquiv.symm_apply_apply,
        AddEquiv.symm_apply_apply]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  right_inv t := by
    induction t using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z m =>
      rw [prependTwistBackward_tmul, prependTwistForward_tmul, AddEquiv.apply_symm_apply,
        AddEquiv.apply_symm_apply]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  map_add' := map_add _

@[simp] theorem prependTwistEquiv_tmul (z : InductionAlong.Corner (prependTwist D Sc i n ε))
    (m : N) :
    prependTwistEquiv D Sc i n ε N (Ind.tmul z m) =
      Ind.tmul (prependTwistCorner D Sc i n ε z) (toTwistModule D Sc (n + 1) ε N m) := rfl

@[simp] theorem prependTwistEquiv_symm_tmul (z : InductionAlong.Corner φ)
    (m : TwistModule D Sc (n + 1) ε N) :
    (prependTwistEquiv D Sc i n ε N).symm (Ind.tmul z m) =
      Ind.tmul ((prependTwistCorner D Sc i n ε).symm z) ((toTwistModule D Sc (n + 1) ε N).symm m) :=
  rfl

/-- The affine prepend PBW coordinates of the twisted induction. -/
def prependTwistCoordinates :
    ((PrependShuffle (n + 1) × ℕ) →₀ N) ≃+ Ind N (prependTwist D Sc i n ε) :=
  ((Finsupp.mapRange.addEquiv (toTwistModule D Sc (n + 1) ε N)).trans
    (prependTensorEquiv D Sc i (n + 1) (TwistModule D Sc (n + 1) ε N))).trans
    (prependTwistEquiv D Sc i n ε N).symm

@[simp] theorem prependTwistCoordinates_single (q : PrependShuffle (n + 1) × ℕ) (m : N) :
    prependTwistCoordinates D Sc i n ε N (Finsupp.single q m) =
      Ind.tmul ((prependTwistCorner D Sc i n ε).symm (prependPBWCorner D Sc i q.1 q.2 1)) m := by
  simp [prependTwistCoordinates, prependTensorEquiv]

end OddMath.QuiverHecke
end

end
