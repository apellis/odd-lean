/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendCoordinates

/-!
# Whole affine append-corner coordinates

Mirror of `PrependEquivalence.lean` (KKO I, arXiv:1206.5933v2, Lemma 8.1, for
the append induction): `appendCoordinateEquiv` identifies finite old-algebra
coefficient families with the append corner.
`appendCoefficients_expansion` proves uniqueness using the scalar append
basis and the old normal-form basis. `appendExpansion_projection` proves
existence by finite matrix entries. The forward map is the literal sum of
`appendPBWCorner`; both directions respect the existing right old-algebra
action. Balanced tensor descent and cancellation remain separate steps.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA MonoidalCategory
open scoped Classical
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Literal finite old-algebra coefficient expansion in the ambient algebra. -/
def appendExpansion (i : I) (n : ℕ) :
    ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) →ₗ[k] Hn D Sc (n + 1) :=
  Finsupp.lsum k fun q =>
    { toFun := appendPBWTerm D Sc i q.1 q.2
      map_add' := by intros; simp [appendPBWTerm, map_add, mul_add]
      map_smul' := by intros; simp [appendPBWTerm, map_smul] }

@[simp] theorem appendExpansion_single (i : I) (n : ℕ)
    (q : AppendShuffleAt n × ℕ) (b : Hn D Sc n) :
    appendExpansion D Sc i n (Finsupp.single q b) = appendPBWTerm D Sc i q.1 q.2 b :=
  Finsupp.lsum_single _ _ _ _

/-- Regroup one scalar Hom expansion into finite old-algebra coefficients. -/
def appendEntryCoefficients (i : I) (s : List I) (t : Word I (s.length + 1)) :
    (wordObj D Sc (appendWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) →ₗ[k]
      ((AppendShuffleAt s.length × ℕ) →₀ Hn D Sc s.length) :=
  (Finsupp.linearCombination k (fun x : AppendIdx i s t.1 =>
    Finsupp.single (x.shuffle, x.1.1)
      (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old)))).comp
    (appendBasis D Sc (i := i) (s := s) (t := t.1)).repr.toLinearMap

/-- Regrouping retains the single-entry matrix, not merely its span. -/
theorem appendExpansion_entry (i : I) (s : List I) (t : Word I (s.length + 1))
    (f : wordObj D Sc (appendWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) :
    appendExpansion D Sc i s.length (appendEntryCoefficients D Sc i s t f) =
      FiniteHomMatrix.single t (appendWord i ⟨s, rfl⟩) f := by
  rw [append_single_expansion D Sc i s t f]
  simp [appendEntryCoefficients, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    appendPBWTerm]
  rfl

/-- The same entry regrouping at a fixed height. -/
def appendWordCoefficients (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1)) :
    (wordObj D Sc (appendWord i s) ⟶ wordObj D Sc t) →ₗ[k]
      ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) := by
  rcases s with ⟨s, hs⟩
  subst n
  exact appendEntryCoefficients D Sc i s t

theorem appendExpansion_word (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1))
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc t) :
    appendExpansion D Sc i n (appendWordCoefficients D Sc i s t f) =
      FiniteHomMatrix.single t (appendWord i s) f := by
  rcases s with ⟨s, hs⟩
  subst n
  exact appendExpansion_entry D Sc i s t f

/-- Finite matrix-entry assembly of the old-algebra coefficients. -/
def appendCoefficients (i : I) (n : ℕ) : Hn D Sc (n + 1) →ₗ[k]
    ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) :=
  ∑ s : Word I n, ∑ t : Word I (n + 1),
    (appendWordCoefficients D Sc i s t).comp
      (DFinsupp.lapply (t, appendWord i s))

/-- Reassembly is the projection onto the allowed columns. -/
theorem appendExpansion_coefficients (i : I) (n : ℕ) (a : Hn D Sc (n + 1)) :
    appendExpansion D Sc i n (appendCoefficients D Sc i n a) =
      ∑ s : Word I n, ∑ t : Word I (n + 1),
        FiniteHomMatrix.single t (appendWord i s) (a (t, appendWord i s)) := by
  simp [appendCoefficients, map_sum, appendExpansion_word]

/-- The old normal form and a chosen shuffle specify one append index. -/
def appendIndex (i : I) {s t : List I} (y : NFIdx s t)
    (q : AppendShuffleAt s.length × ℕ) :
    AppendIdx i s (appendShuffleTarget i q.1 ⟨t, by
      rw [← y.tgt_cw]; simp⟩).1 :=
  ⟨(q.2, y.1.1, y.1.2, AppendShuffle.cast _ (appendLen s i) q.1), y.2.1, y.2.2.1, by
    have he := tgt_append_right [i] (t := s) (fits_cw (validWord_canWord s.length y.1.2))
    simp only [appendCrossingWord, cw_append, tgt_append, he, y.tgt_cw, appendShuffleTarget,
      AppendShuffle.canWord_cast]⟩

theorem appendCoefficients_single (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1))
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc t) :
    appendCoefficients D Sc i n (FiniteHomMatrix.single t (appendWord i s) f) =
      appendWordCoefficients D Sc i s t f := by
  classical
  simp only [appendCoefficients, LinearMap.sum_apply, LinearMap.comp_apply,
    DFinsupp.lapply_apply]
  rw [Finset.sum_eq_single s]
  · rw [Finset.sum_eq_single t]
    · simp [FiniteHomMatrix.single]
    · intro b _ hb
      simp [FiniteHomMatrix.single, Ne.symm hb]
    · simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    have h : appendWord i s ≠ appendWord i b := fun h => hb ((appendWord_injective i n h).symm)
    simp [FiniteHomMatrix.single, h]
  · simp

theorem appendCoefficients_old_nf {i : I} {s t : List I} (x : AppendIdx i s t) :
    appendCoefficients D Sc i s.length
      (appendPBWTerm D Sc i x.shuffle x.1.1
        (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old))) =
    Finsupp.single (x.shuffle, x.1.1)
      (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old)) := by
  rw [appendPBWTerm_old_nf, appendCoefficients_single]
  change appendEntryCoefficients D Sc i s x.targetWord (appendElt D Sc x) = _
  rw [← appendBasis_apply D Sc x]
  simp only [appendEntryCoefficients, LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [Module.Basis.repr_self]
  simp only [Finsupp.linearCombination_single, one_smul]

theorem appendCoefficients_nf (i : I) (s : List I) (t : Word I s.length)
    (y : NFIdx s t.1) (q : AppendShuffleAt s.length × ℕ) :
    appendCoefficients D Sc i s.length
      (appendPBWTerm D Sc i q.1 q.2
        (FiniteHomMatrix.single t ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) y))) =
      Finsupp.single q (FiniteHomMatrix.single t ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) y)) := by
  rcases t with ⟨t, ht⟩
  have he := y.tgt_cw
  rcases y with ⟨⟨L, v⟩, hy⟩
  change tgt s (cw (canWord s.length v)) = t at he
  subst t
  simpa [appendIndex, AppendIdx.oldWord, AppendIdx.old, AppendIdx.oldTarget,
    AppendIdx.shuffle] using
    appendCoefficients_old_nf D Sc (appendIndex i ⟨(L, v), hy⟩ q)

theorem appendCoefficients_term (i : I) {n : ℕ} (q : AppendShuffleAt n × ℕ)
    (b : Hn D Sc n) :
    appendCoefficients D Sc i n (appendPBWTerm D Sc i q.1 q.2 b) = Finsupp.single q b := by
  let P : Hn D Sc n →ₗ[k] Hn D Sc (n + 1) :=
    (appendExpansion D Sc i n).comp (Finsupp.lsingle q)
  rw [← appendExpansion_single D Sc i n q b]
  change appendCoefficients D Sc i n (P b) = Finsupp.single q b
  induction b using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [ha, hb]
  | hs t s f =>
    let E : (wordObj D Sc s ⟶ wordObj D Sc t) →ₗ[k] Hn D Sc n :=
      { toFun := FiniteHomMatrix.single t s
        map_add' := FiniteHomMatrix.single_add _ _
        map_smul' := fun c g => FiniteHomMatrix.single_smul _ _ c g }
    have h : ((appendCoefficients D Sc i n).comp P).comp E =
        (Finsupp.lsingle q).comp E := by
      apply (basisNF D Sc s.1 t.1).ext
      intro y
      simp only [LinearMap.comp_apply, P, Finsupp.lsingle_apply, appendExpansion_single,
        basisNF_apply, E, LinearMap.coe_mk, AddHom.coe_mk]
      rcases s with ⟨s, hs⟩
      subst n
      exact appendCoefficients_nf D Sc i s t y q
    exact LinearMap.congr_fun h f

/-- Scalar append independence recovers every old-algebra coefficient. -/
theorem appendCoefficients_expansion (i : I) (n : ℕ)
    (b : (AppendShuffleAt n × ℕ) →₀ Hn D Sc n) :
    appendCoefficients D Sc i n (appendExpansion D Sc i n b) = b := by
  have h : (appendCoefficients D Sc i n).comp (appendExpansion D Sc i n) =
      LinearMap.id := by
    apply Finsupp.lhom_ext
    intro q b
    simpa only [LinearMap.comp_apply, appendExpansion_single, LinearMap.id_apply] using
      appendCoefficients_term D Sc i q b
  exact LinearMap.congr_fun h b

/-- Uniqueness holds for coefficients in the whole old algebra. -/
theorem appendExpansion_injective (i : I) (n : ℕ) :
    Function.Injective (appendExpansion D Sc i n) :=
  Function.LeftInverse.injective (appendCoefficients_expansion D Sc i n)

private theorem matrix_mul_idem_sum {n : ℕ} (a : Hn D Sc n) (s : Word I n) :
    a * FiniteHomMatrix.idem s =
      ∑ t : Word I n, FiniteHomMatrix.single t s (a (t, s)) := by
  classical
  induction a using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [add_mul, ha, hb, DFinsupp.add_apply,
      Finset.sum_add_distrib]
  | hs t r f =>
    by_cases h : r = s
    · subst r
      rw [FiniteHomMatrix.single_mul_idem]
      symm
      rw [Finset.sum_eq_single t]
      · simp [FiniteHomMatrix.single]
      · intro b _ hb
        simp [FiniteHomMatrix.single, Ne.symm hb]
      · simp
    · rw [FiniteHomMatrix.idem, FiniteHomMatrix.single_mul_single_of_ne _ _ _ _ h]
      symm
      apply Finset.sum_eq_zero
      intro b _
      simp [FiniteHomMatrix.single, h]

/-- The matrix reassembly is multiplication by the append idempotent. -/
theorem appendExpansion_projection (i : I) (n : ℕ) (a : Hn D Sc (n + 1)) :
    appendExpansion D Sc i n (appendCoefficients D Sc i n a) =
      a * appendAlgebra D Sc i n 1 := by
  rw [appendExpansion_coefficients]
  change _ = a * appendLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ)
  simp only [FiniteHomMatrix.localUnit, map_sum, FiniteHomMatrix.idem, appendLinear_single,
    appendHom, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  erw [MonoidalSupercategory.id_whiskerRight (R := k)]
  exact (matrix_mul_idem_sum D Sc a (appendWord i s)).symm

/-- Every element of the whole corner has finite old-algebra coefficients. -/
theorem appendExpansion_exists (i : I) (n : ℕ)
    (z : InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))) :
    ∃ b : (AppendShuffleAt n × ℕ) →₀ Hn D Sc n, appendExpansion D Sc i n b = z.1 :=
  ⟨appendCoefficients D Sc i n z.1, (appendExpansion_projection D Sc i n z.1).trans z.2⟩

/-- The finite expansion lands in the corner. -/
def appendCornerExpansion (i : I) (n : ℕ) :
    ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) →ₗ[k]
      InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) where
  toFun b := ⟨appendExpansion D Sc i n b, by
    have h := appendExpansion_projection D Sc i n (appendExpansion D Sc i n b)
    rw [appendCoefficients_expansion] at h
    exact h.symm⟩
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' c b := Subtype.ext (map_smul _ c b)

/-- Whole affine append-corner coordinates (mirror of KKO I, Lemma 8.1). -/
def appendCoordinateEquiv (i : I) (n : ℕ) :
    ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) ≃ₗ[k]
      InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) :=
  LinearEquiv.ofBijective (appendCornerExpansion D Sc i n) ⟨
    fun a b h => appendExpansion_injective D Sc i n (congrArg Subtype.val h), by
      intro z
      obtain ⟨b, hb⟩ := appendExpansion_exists D Sc i n z
      exact ⟨b, Subtype.ext hb⟩⟩

/-- Forward coordinates are the literal finite sum of append corner terms. -/
theorem appendCoordinateEquiv_apply (i : I) (n : ℕ)
    (b : (AppendShuffleAt n × ℕ) →₀ Hn D Sc n) :
    appendCoordinateEquiv D Sc i n b =
      b.sum (fun q c => appendPBWCorner D Sc i q.1 q.2 c) := by
  apply Subtype.ext
  change appendExpansion D Sc i n b = _
  simp [appendExpansion, Finsupp.lsum_apply, Finsupp.sum, appendPBWCorner]

/-- The inverse is the finite entrywise coefficient assembly. -/
theorem appendCoordinateEquiv_symm_apply (i : I) (n : ℕ)
    (z : InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))) :
    (appendCoordinateEquiv D Sc i n).symm z = appendCoefficients D Sc i n z.1 := by
  apply (appendCoordinateEquiv D Sc i n).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact ((appendExpansion_projection D Sc i n z.1).trans z.2).symm

/-- Coefficientwise right multiplication by an old-algebra element. -/
def appendRightCoefficients {n : ℕ} (r : Hn D Sc n) :
    ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) →ₗ[k]
      ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) :=
  Finsupp.mapRange.linearMap
    { toFun := fun b => b * r
      map_add' := fun a b => add_mul a b r
      map_smul' := fun c b => smul_mul_assoc c b r }

@[simp] theorem appendRightCoefficients_apply {n : ℕ} (r : Hn D Sc n)
    (b : (AppendShuffleAt n × ℕ) →₀ Hn D Sc n) (q : AppendShuffleAt n × ℕ) :
    appendRightCoefficients D Sc r b q = b q * r := rfl

/-- Right action is inherited from the affine multiplication. -/
theorem appendExpansion_right (i : I) (n : ℕ)
    (b : (AppendShuffleAt n × ℕ) →₀ Hn D Sc n) (r : Hn D Sc n) :
    appendExpansion D Sc i n (appendRightCoefficients D Sc r b) =
      appendExpansion D Sc i n b * appendAlgebra D Sc i n r := by
  let R : Hn D Sc (n + 1) →ₗ[k] Hn D Sc (n + 1) :=
    { toFun := fun a => a * appendAlgebra D Sc i n r
      map_add' := fun a b => add_mul a b _
      map_smul' := fun c b => smul_mul_assoc c b _ }
  have h : (appendExpansion D Sc i n).comp (appendRightCoefficients D Sc r) =
      R.comp (appendExpansion D Sc i n) := by
    apply Finsupp.lhom_ext
    intro q a
    simp only [LinearMap.comp_apply, appendRightCoefficients, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, LinearMap.coe_mk, AddHom.coe_mk, appendExpansion_single, R]
    exact appendPBWTerm_right D Sc i q.1 q.2 a r
  exact LinearMap.congr_fun h b

theorem appendCoordinateEquiv_right (i : I) (n : ℕ)
    (b : (AppendShuffleAt n × ℕ) →₀ Hn D Sc n) (r : Hn D Sc n) :
    appendCoordinateEquiv D Sc i n (appendRightCoefficients D Sc r b) =
      MulOpposite.op r • appendCoordinateEquiv D Sc i n b := by
  apply Subtype.ext
  exact appendExpansion_right D Sc i n b r

/-- The coordinate inverse respects the same right-old-algebra action. -/
theorem appendCoordinateEquiv_symm_right (i : I) (n : ℕ)
    (z : InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)))
    (r : Hn D Sc n) :
    (appendCoordinateEquiv D Sc i n).symm (MulOpposite.op r • z) =
      appendRightCoefficients D Sc r ((appendCoordinateEquiv D Sc i n).symm z) := by
  apply (appendCoordinateEquiv D Sc i n).injective
  rw [LinearEquiv.apply_symm_apply, appendCoordinateEquiv_right, LinearEquiv.apply_symm_apply]

/-- Reconstructing the extracted coefficients gives the corner element. -/
theorem appendCoordinateEquiv_roundtrip (i : I) (n : ℕ)
    (z : InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))) :
    appendCoordinateEquiv D Sc i n ((appendCoordinateEquiv D Sc i n).symm z) = z :=
  (appendCoordinateEquiv D Sc i n).apply_symm_apply z

/-- Extracting the coefficients of the literal expansion gives the family. -/
theorem appendCoordinateEquiv_symm_roundtrip (i : I) (n : ℕ)
    (b : (AppendShuffleAt n × ℕ) →₀ Hn D Sc n) :
    (appendCoordinateEquiv D Sc i n).symm (appendCoordinateEquiv D Sc i n b) = b :=
  (appendCoordinateEquiv D Sc i n).symm_apply_apply b

end OddMath.QuiverHecke
