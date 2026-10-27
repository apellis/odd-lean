/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.PrependMatrix

/-!
# Whole affine prepend-corner coordinates

For KKO I, arXiv:1206.5933v2, Lemma 8.1, `prependCoordinateEquiv` identifies
finite old-algebra coefficient families with the original prepend corner.
`prependCoefficients_expansion` proves uniqueness using the scalar prepend
basis and the old normal-form basis. `prependExpansion_projection` proves
existence by finite matrix entries. The forward map is the literal sum of
`prependPBWCorner`; both directions respect the existing right old-algebra
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
def prependExpansion (i : I) (n : ℕ) :
    ((PrependShuffle n × ℕ) →₀ Hn D Sc n) →ₗ[k] Hn D Sc (n + 1) :=
  Finsupp.lsum k fun q =>
    { toFun := prependPBWTerm D Sc i q.1 q.2
      map_add' := by intros; simp [prependPBWTerm, map_add, mul_add]
      map_smul' := by intros; simp [prependPBWTerm, map_smul] }

@[simp] theorem prependExpansion_single (i : I) (n : ℕ)
    (q : PrependShuffle n × ℕ) (b : Hn D Sc n) :
    prependExpansion D Sc i n (Finsupp.single q b) = prependPBWTerm D Sc i q.1 q.2 b :=
  Finsupp.lsum_single _ _ _ _

/-- Regroup one scalar Hom expansion into finite old-algebra coefficients. -/
def prependEntryCoefficients (i : I) (s : List I) (t : Word I (s.length + 1)) :
    (wordObj D Sc (prependWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) →ₗ[k]
      ((PrependShuffle s.length × ℕ) →₀ Hn D Sc s.length) :=
  (Finsupp.linearCombination k (fun x : PrependIdx i s t.1 =>
    Finsupp.single (x.1.2.2.2, x.1.1)
      (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old)))).comp
    (prependBasis D Sc (i := i) (s := s) (t := t.1)).repr.toLinearMap

/-- Regrouping retains the actual single-entry matrix, not merely its span. -/
theorem prependExpansion_entry (i : I) (s : List I) (t : Word I (s.length + 1))
    (f : wordObj D Sc (prependWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) :
    prependExpansion D Sc i s.length (prependEntryCoefficients D Sc i s t f) =
      FiniteHomMatrix.single t (prependWord i ⟨s, rfl⟩) f := by
  rw [prepend_single_expansion D Sc i s t f]
  simp [prependEntryCoefficients, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    prependPBWTerm]
  rfl

/-- The same entry regrouping at a fixed height. -/
def prependWordCoefficients (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1)) :
    (wordObj D Sc (prependWord i s) ⟶ wordObj D Sc t) →ₗ[k]
      ((PrependShuffle n × ℕ) →₀ Hn D Sc n) := by
  rcases s with ⟨s, hs⟩
  subst n
  exact prependEntryCoefficients D Sc i s t

theorem prependExpansion_word (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1))
    (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc t) :
    prependExpansion D Sc i n (prependWordCoefficients D Sc i s t f) =
      FiniteHomMatrix.single t (prependWord i s) f := by
  rcases s with ⟨s, hs⟩
  subst n
  exact prependExpansion_entry D Sc i s t f

/-- Finite matrix-entry assembly of the old-algebra coefficients. -/
def prependCoefficients (i : I) (n : ℕ) : Hn D Sc (n + 1) →ₗ[k]
    ((PrependShuffle n × ℕ) →₀ Hn D Sc n) :=
  ∑ s : Word I n, ∑ t : Word I (n + 1),
    (prependWordCoefficients D Sc i s t).comp
      (DFinsupp.lapply (t, prependWord i s))

/-- Reassembly is the projection onto the allowed columns. -/
theorem prependExpansion_coefficients (i : I) (n : ℕ) (a : Hn D Sc (n + 1)) :
    prependExpansion D Sc i n (prependCoefficients D Sc i n a) =
      ∑ s : Word I n, ∑ t : Word I (n + 1),
        FiniteHomMatrix.single t (prependWord i s) (a (t, prependWord i s)) := by
  simp [prependCoefficients, map_sum, prependExpansion_word]

/-- The old normal form and a chosen shuffle specify one prepend index. -/
def prependIndex (i : I) {s t : List I} (y : NFIdx s t)
    (q : PrependShuffle s.length × ℕ) :
    PrependIdx i s (prependShuffleTarget i q.1 ⟨t, by
      rw [← y.tgt_cw]; simp⟩).1 :=
  ⟨(q.2, y.1.1, y.1.2, q.1), y.2.1, y.2.2.1, by
    have he := tgt_shift [i] s (cw (canWord s.length y.1.2))
    simp only [List.length_singleton, cw_map_shift, List.singleton_append] at he
    simp only [prependCrossingWord, cw_append, tgt_append, he, y.tgt_cw]
    rfl⟩

theorem prependCoefficients_single (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1))
    (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc t) :
    prependCoefficients D Sc i n (FiniteHomMatrix.single t (prependWord i s) f) =
      prependWordCoefficients D Sc i s t f := by
  classical
  simp only [prependCoefficients, LinearMap.sum_apply, LinearMap.comp_apply,
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
    have h : prependWord i s ≠ prependWord i b := fun h => hb ((prependWord_injective i n h).symm)
    simp [FiniteHomMatrix.single, h]
  · simp

theorem prependCoefficients_old_nf {i : I} {s t : List I} (x : PrependIdx i s t) :
    prependCoefficients D Sc i s.length
      (prependPBWTerm D Sc i x.1.2.2.2 x.1.1
        (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old))) =
    Finsupp.single (x.1.2.2.2, x.1.1)
      (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old)) := by
  rw [prependPBWTerm_old_nf, prependCoefficients_single]
  change prependEntryCoefficients D Sc i s x.targetWord (prependElt D Sc x) = _
  rw [← prependBasis_apply D Sc x]
  simp only [prependEntryCoefficients, LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [Module.Basis.repr_self]
  simp only [Finsupp.linearCombination_single, one_smul]

theorem prependCoefficients_nf (i : I) (s : List I) (t : Word I s.length)
    (y : NFIdx s t.1) (q : PrependShuffle s.length × ℕ) :
    prependCoefficients D Sc i s.length
      (prependPBWTerm D Sc i q.1 q.2
        (FiniteHomMatrix.single t ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) y))) =
      Finsupp.single q (FiniteHomMatrix.single t ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) y)) := by
  rcases t with ⟨t, ht⟩
  have he := y.tgt_cw
  rcases y with ⟨⟨L, v⟩, hy⟩
  change tgt s (cw (canWord s.length v)) = t at he
  subst t
  simpa [prependIndex, PrependIdx.oldWord, PrependIdx.old, PrependIdx.oldTarget] using
    prependCoefficients_old_nf D Sc (prependIndex i ⟨(L, v), hy⟩ q)

theorem prependCoefficients_term (i : I) {n : ℕ} (q : PrependShuffle n × ℕ)
    (b : Hn D Sc n) :
    prependCoefficients D Sc i n (prependPBWTerm D Sc i q.1 q.2 b) = Finsupp.single q b := by
  let P : Hn D Sc n →ₗ[k] Hn D Sc (n + 1) :=
    (prependExpansion D Sc i n).comp (Finsupp.lsingle q)
  rw [← prependExpansion_single D Sc i n q b]
  change prependCoefficients D Sc i n (P b) = Finsupp.single q b
  induction b using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [ha, hb]
  | hs t s f =>
    let E : (wordObj D Sc s ⟶ wordObj D Sc t) →ₗ[k] Hn D Sc n :=
      { toFun := FiniteHomMatrix.single t s
        map_add' := FiniteHomMatrix.single_add _ _
        map_smul' := fun c g => FiniteHomMatrix.single_smul _ _ c g }
    have h : ((prependCoefficients D Sc i n).comp P).comp E =
        (Finsupp.lsingle q).comp E := by
      apply (basisNF D Sc s.1 t.1).ext
      intro y
      simp only [LinearMap.comp_apply, P, Finsupp.lsingle_apply, prependExpansion_single,
        basisNF_apply, E, LinearMap.coe_mk, AddHom.coe_mk]
      rcases s with ⟨s, hs⟩
      subst n
      exact prependCoefficients_nf D Sc i s t y q
    exact LinearMap.congr_fun h f

/-- Scalar prepend independence recovers every old-algebra coefficient. -/
theorem prependCoefficients_expansion (i : I) (n : ℕ)
    (b : (PrependShuffle n × ℕ) →₀ Hn D Sc n) :
    prependCoefficients D Sc i n (prependExpansion D Sc i n b) = b := by
  have h : (prependCoefficients D Sc i n).comp (prependExpansion D Sc i n) =
      LinearMap.id := by
    apply Finsupp.lhom_ext
    intro q b
    simpa only [LinearMap.comp_apply, prependExpansion_single, LinearMap.id_apply] using
      prependCoefficients_term D Sc i q b
  exact LinearMap.congr_fun h b

/-- Uniqueness holds for coefficients in the whole old algebra. -/
theorem prependExpansion_injective (i : I) (n : ℕ) :
    Function.Injective (prependExpansion D Sc i n) :=
  Function.LeftInverse.injective (prependCoefficients_expansion D Sc i n)

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

/-- The matrix reassembly is multiplication by the actual prepend idempotent. -/
theorem prependExpansion_projection (i : I) (n : ℕ) (a : Hn D Sc (n + 1)) :
    prependExpansion D Sc i n (prependCoefficients D Sc i n a) =
      a * prependAlgebra D Sc i n 1 := by
  rw [prependExpansion_coefficients]
  change _ = a * prependLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ)
  simp only [FiniteHomMatrix.localUnit, map_sum, FiniteHomMatrix.idem, prependLinear_single,
    prependHom, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  erw [MonoidalSupercategory.whiskerLeft_id (R := k)]
  exact (matrix_mul_idem_sum D Sc a (prependWord i s)).symm

/-- Every element of the original whole corner has finite old-algebra coefficients. -/
theorem prependExpansion_exists (i : I) (n : ℕ)
    (z : InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))) :
    ∃ b : (PrependShuffle n × ℕ) →₀ Hn D Sc n, prependExpansion D Sc i n b = z.1 :=
  ⟨prependCoefficients D Sc i n z.1, (prependExpansion_projection D Sc i n z.1).trans z.2⟩

/-- The finite expansion lands in the original corner. -/
def prependCornerExpansion (i : I) (n : ℕ) :
    ((PrependShuffle n × ℕ) →₀ Hn D Sc n) →ₗ[k]
      InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) where
  toFun b := ⟨prependExpansion D Sc i n b, by
    have h := prependExpansion_projection D Sc i n (prependExpansion D Sc i n b)
    rw [prependCoefficients_expansion] at h
    exact h.symm⟩
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' c b := Subtype.ext (map_smul _ c b)

/-- Whole affine prepend-corner coordinates (KKO I, Lemma 8.1). -/
def prependCoordinateEquiv (i : I) (n : ℕ) :
    ((PrependShuffle n × ℕ) →₀ Hn D Sc n) ≃ₗ[k]
      InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) :=
  LinearEquiv.ofBijective (prependCornerExpansion D Sc i n) ⟨
    fun a b h => prependExpansion_injective D Sc i n (congrArg Subtype.val h), by
      intro z
      obtain ⟨b, hb⟩ := prependExpansion_exists D Sc i n z
      exact ⟨b, Subtype.ext hb⟩⟩

/-- Forward coordinates are the literal finite sum of prepend corner terms. -/
theorem prependCoordinateEquiv_apply (i : I) (n : ℕ)
    (b : (PrependShuffle n × ℕ) →₀ Hn D Sc n) :
    prependCoordinateEquiv D Sc i n b =
      b.sum (fun q c => prependPBWCorner D Sc i q.1 q.2 c) := by
  apply Subtype.ext
  change prependExpansion D Sc i n b = _
  simp [prependExpansion, Finsupp.lsum_apply, Finsupp.sum, prependPBWCorner]

/-- The inverse is the finite entrywise coefficient assembly. -/
theorem prependCoordinateEquiv_symm_apply (i : I) (n : ℕ)
    (z : InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))) :
    (prependCoordinateEquiv D Sc i n).symm z = prependCoefficients D Sc i n z.1 := by
  apply (prependCoordinateEquiv D Sc i n).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact ((prependExpansion_projection D Sc i n z.1).trans z.2).symm

/-- Coefficientwise right multiplication by an old-algebra element. -/
def prependRightCoefficients {n : ℕ} (r : Hn D Sc n) :
    ((PrependShuffle n × ℕ) →₀ Hn D Sc n) →ₗ[k]
      ((PrependShuffle n × ℕ) →₀ Hn D Sc n) :=
  Finsupp.mapRange.linearMap
    { toFun := fun b => b * r
      map_add' := fun a b => add_mul a b r
      map_smul' := fun c b => smul_mul_assoc c b r }

@[simp] theorem prependRightCoefficients_apply {n : ℕ} (r : Hn D Sc n)
    (b : (PrependShuffle n × ℕ) →₀ Hn D Sc n) (q : PrependShuffle n × ℕ) :
    prependRightCoefficients D Sc r b q = b q * r := rfl

/-- Right action is inherited from the actual affine multiplication. -/
theorem prependExpansion_right (i : I) (n : ℕ)
    (b : (PrependShuffle n × ℕ) →₀ Hn D Sc n) (r : Hn D Sc n) :
    prependExpansion D Sc i n (prependRightCoefficients D Sc r b) =
      prependExpansion D Sc i n b * prependAlgebra D Sc i n r := by
  let R : Hn D Sc (n + 1) →ₗ[k] Hn D Sc (n + 1) :=
    { toFun := fun a => a * prependAlgebra D Sc i n r
      map_add' := fun a b => add_mul a b _
      map_smul' := fun c b => smul_mul_assoc c b _ }
  have h : (prependExpansion D Sc i n).comp (prependRightCoefficients D Sc r) =
      R.comp (prependExpansion D Sc i n) := by
    apply Finsupp.lhom_ext
    intro q a
    simp only [LinearMap.comp_apply, prependRightCoefficients, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, LinearMap.coe_mk, AddHom.coe_mk, prependExpansion_single, R]
    exact prependPBWTerm_right D Sc i q.1 q.2 a r
  exact LinearMap.congr_fun h b

theorem prependCoordinateEquiv_right (i : I) (n : ℕ)
    (b : (PrependShuffle n × ℕ) →₀ Hn D Sc n) (r : Hn D Sc n) :
    prependCoordinateEquiv D Sc i n (prependRightCoefficients D Sc r b) =
      MulOpposite.op r • prependCoordinateEquiv D Sc i n b := by
  apply Subtype.ext
  exact prependExpansion_right D Sc i n b r

/-- The coordinate inverse respects the same right-old-algebra action. -/
theorem prependCoordinateEquiv_symm_right (i : I) (n : ℕ)
    (z : InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)))
    (r : Hn D Sc n) :
    (prependCoordinateEquiv D Sc i n).symm (MulOpposite.op r • z) =
      prependRightCoefficients D Sc r ((prependCoordinateEquiv D Sc i n).symm z) := by
  apply (prependCoordinateEquiv D Sc i n).injective
  rw [LinearEquiv.apply_symm_apply, prependCoordinateEquiv_right, LinearEquiv.apply_symm_apply]

/-- Reconstructing the extracted coefficients gives the original corner element. -/
theorem prependCoordinateEquiv_roundtrip (i : I) (n : ℕ)
    (z : InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))) :
    prependCoordinateEquiv D Sc i n ((prependCoordinateEquiv D Sc i n).symm z) = z :=
  (prependCoordinateEquiv D Sc i n).apply_symm_apply z

/-- Extracting the coefficients of the literal expansion gives the original family. -/
theorem prependCoordinateEquiv_symm_roundtrip (i : I) (n : ℕ)
    (b : (PrependShuffle n × ℕ) →₀ Hn D Sc n) :
    (prependCoordinateEquiv D Sc i n).symm (prependCoordinateEquiv D Sc i n b) = b :=
  (prependCoordinateEquiv D Sc i n).symm_apply_apply b

end OddMath.QuiverHecke
