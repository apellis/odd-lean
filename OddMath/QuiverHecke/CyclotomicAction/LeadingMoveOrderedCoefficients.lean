/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveProduct
import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveCoefficients
import OddMath.QuiverHecke.HnBasis

/-!
# Concrete ordered coefficients of the moving product

`prependWordCoefficients_moveHom_ordered` computes the longest-shuffle
coefficient of the prescribed moving homomorphism by a finite sum over local
choices. `leadingMoveOrderedCoefficients_explicit` separates the moving degree
from the old diagonal dot monomial. All distant separation signs cancel for
these square factors, in both parities. The old monomials are already sorted,
and `leadingMoveOrderedCoefficients_nonidentity` excludes every nonidentity
old permutation.

The degree-normalizing sign is trivial on this producer. Invariance under the
separate old matrix twist is not asserted here.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA MonoidalCategory
open scoped Classical
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The moving degree counts only dots at the new source position zero. -/
def sourceMovingDegree : List ℕ → ℕ
  | [] => 0
  | 0 :: ps => sourceMovingDegree ps + 1
  | (_ + 1) :: ps => sourceMovingDegree ps

/-- Dot monomials with the object family fixed to the matrix object family. -/
def wordEndpointDots {n : ℕ} (w : Word I n) (ps : List ℕ) : End (wordObj D Sc w) :=
  endpointDotMonomial D Sc w.1 ps

/-- A positioned dot with the object family fixed. -/
def wordPositionDot {n : ℕ} (w : Word I n) (p : ℕ) : End (wordObj D Sc w) :=
  dotE D Sc w.1 p

/-- Explicit old coefficient, with every superinterchange sign retained by the
parity automorphism. The list is chronological, hence multiplication reverses it. -/
def sourceOldCoefficient (i : I) (ν : List I) : List ℕ → Hn D Sc ν.length
  | [] => FiniteHomMatrix.single ⟨ν, rfl⟩ ⟨ν, rfl⟩ (𝟙 _)
  | 0 :: ps => homMatrixTwist D Sc ν.length (D.parity i) (sourceOldCoefficient i ν ps)
  | (p + 1) :: ps => sourceOldCoefficient i ν ps *
      FiniteHomMatrix.single ⟨ν, rfl⟩ ⟨ν, rfl⟩ (wordPositionDot D Sc ⟨ν, rfl⟩ p)

omit [Fintype I] in
private theorem wordEndpointDots_cons {n : ℕ} (w : Word I n) (p : ℕ) (ps : List ℕ) :
    wordEndpointDots D Sc w (p :: ps) =
      wordPositionDot D Sc w p ≫ wordEndpointDots D Sc w ps := by
  change endpointDotMonomial D Sc w.1 (p :: ps) =
    dotE D Sc w.1 p ≫ endpointDotMonomial D Sc w.1 ps
  rw [dotE_eq_cl D Sc (sChain_dotAny w.1 p)]
  unfold endpointDotMonomial
  rw [cl_comp]
  rfl

omit [Fintype I] in
private theorem prependAlgebra_single' (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    prependAlgebra D Sc i n (FiniteHomMatrix.single t s f) =
      FiniteHomMatrix.single (prependWord i t) (prependWord i s) (prependHom D Sc i s t f) :=
  prependLinear_single D Sc i s t f

private theorem single_mul_firstDot' (i : I) {n : ℕ} (s : Word I n)
    (f : End (wordObj D Sc (prependWord i s))) :
    FiniteHomMatrix.single (prependWord i s) (prependWord i s) f *
      affineFirstDot D Sc i n =
    FiniteHomMatrix.single (prependWord i s) (prependWord i s)
      (inductionFirstDot D Sc i s ≫ f) := by
  rw [affineFirstDot, Finset.mul_sum, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (prependWord_injective i n h.symm)) _ _
  · simp

omit [Fintype I] in
private theorem wordPositionDot_zero (i : I) {n : ℕ} (s : Word I n) :
    wordPositionDot D Sc (prependWord i s) 0 = inductionFirstDot D Sc i s :=
  (inductionFirstDot_eq_dotE D Sc i s).symm

omit [Fintype I] in
private theorem wordPositionDot_succ (i : I) {n : ℕ} (s : Word I n) (p : ℕ) :
    wordPositionDot D Sc (prependWord i s) (p + 1) =
      prependHom D Sc i s s (wordPositionDot D Sc s p) :=
  (whiskerLeft_letter_dotE D Sc i s.1 p).symm

/-- Exact separation of arbitrary source dot words into moving powers and old
matrix coefficients. This recurrence includes odd distant interchange signs. -/
theorem endpointDotMonomial_separate (i : I) (ν : List I) (ps : List ℕ) :
    FiniteHomMatrix.single (prependWord i ⟨ν, rfl⟩) (prependWord i ⟨ν, rfl⟩)
      (wordEndpointDots D Sc (prependWord i ⟨ν, rfl⟩) ps) =
    affineFirstDot D Sc i ν.length ^ sourceMovingDegree ps *
      prependAlgebra D Sc i ν.length (sourceOldCoefficient D Sc i ν ps) := by
  induction ps with
  | nil =>
    simp only [sourceMovingDegree, pow_zero, one_mul, sourceOldCoefficient,
      prependAlgebra_single']
    congr 1
    trans 𝟙 _
    · exact cl_nil D Sc (i :: ν) rfl
    · exact (MonoidalSupercategory.whiskerLeft_id (R := k)
        ((pres D Sc).obj (ob D [i])) (wordObj D Sc ⟨ν, rfl⟩)).symm
  | cons p ps ih =>
    rw [wordEndpointDots_cons]
    cases p with
    | zero =>
      rw [wordPositionDot_zero, ← single_mul_firstDot', ih, mul_assoc,
        affineFirstDot_twist_comm]
      simp only [sourceMovingDegree, sourceOldCoefficient, pow_succ, mul_assoc]
    | succ p =>
      rw [wordPositionDot_succ, ← FiniteHomMatrix.single_mul_single,
        ← prependAlgebra_single', ih]
      simp only [sourceMovingDegree, sourceOldCoefficient, map_mul, mul_assoc]

/-- The scalar-free old entry underlying the coefficient recurrence. -/
def sourceOldHom (i : I) (ν : List I) : List ℕ → End (wordObj D Sc ⟨ν, rfl⟩)
  | [] => 𝟙 _
  | 0 :: ps => Supercategory.twist k (D.parity i) (sourceOldHom i ν ps)
  | (p + 1) :: ps => wordPositionDot D Sc ⟨ν, rfl⟩ p ≫ sourceOldHom i ν ps

omit [Fintype I] in
/-- All old coefficients are on the original word's diagonal. -/
theorem sourceOldCoefficient_single (i : I) (ν : List I) (ps : List ℕ) :
    sourceOldCoefficient D Sc i ν ps =
      FiniteHomMatrix.single ⟨ν, rfl⟩ ⟨ν, rfl⟩ (sourceOldHom D Sc i ν ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases p with
    | zero => simp only [sourceOldCoefficient, sourceOldHom, ih, homMatrixTwist_single]
    | succ p => simp only [sourceOldCoefficient, sourceOldHom, ih,
        FiniteHomMatrix.single_mul_single]

/-- Concrete coordinates of any source dot monomial followed by a prescribed
shuffle: one moving degree, and the explicitly computed old diagonal entry. -/
theorem prependWordCoefficients_endpointDots (i : I) (ν : List I)
    (u : PrependShuffle ν.length) (ps : List ℕ) :
    prependWordCoefficients D Sc i ⟨ν, rfl⟩ (prependShuffleTarget i u ⟨ν, rfl⟩)
      (wordEndpointDots D Sc (prependWord i ⟨ν, rfl⟩) ps ≫
        prependShuffleHom D Sc i u ⟨ν, rfl⟩) =
      Finsupp.single (u, sourceMovingDegree ps) (sourceOldCoefficient D Sc i ν ps) := by
  apply prependExpansion_injective D Sc i ν.length
  rw [prependExpansion_word, prependExpansion_single]
  have h := prependShuffleElement_mul_single D Sc i u ⟨ν, rfl⟩ ⟨ν, rfl⟩
    (wordEndpointDots D Sc (prependWord i ⟨ν, rfl⟩) ps)
  rw [endpointDotMonomial_separate] at h
  exact h.symm.trans (mul_assoc _ _ _).symm

/-- Explicit finite producer for an ordered moving product. No basis inverse is
used in this definition: each choice gives its moving degree and old dot entry. -/
def leadingMoveOrderedCoefficients (i : I) (ν : List I) :
    (PrependShuffle ν.length × ℕ) →₀ Hn D Sc ν.length :=
  ∑ c : MoveChoices ν, leadingMoveCoeff D (k := k) i ν c •
    Finsupp.single (longPrependShuffle ν.length,
      sourceMovingDegree (leadingSourceDots D i 0 0 ν c))
      (sourceOldCoefficient D Sc i ν (leadingSourceDots D i 0 0 ν c))

/-- The actual ordered moving product, typed in the matrix object family. -/
def wordLeadingMoveProduct (i : I) (ν : List I) :
    End (wordObj D Sc (prependWord i ⟨ν, rfl⟩)) := leadingMoveProduct D Sc i [] ν

omit [Fintype I] in
private theorem wordLeadingMoveProduct_expansion (i : I) (ν : List I) :
    wordLeadingMoveProduct D Sc i ν =
      ∑ c : MoveChoices ν, leadingMoveCoeff D (k := k) i ν c •
        wordEndpointDots D Sc (prependWord i ⟨ν, rfl⟩)
          (leadingSourceDots D i 0 0 ν c) :=
  leadingSourceProduct_expansion D Sc (i :: ν) i 0 0 ν

/-- Concrete evaluation of the square-difference product in the existing
prepend coordinates. This is a finite coefficient formula, not a comparison
with another coordinate extraction. It holds for arbitrary words and parity. -/
theorem prependWordCoefficients_leadingMoveProduct (i : I) (ν : List I) :
    prependWordCoefficients D Sc i ⟨ν, rfl⟩
      (prependShuffleTarget i (longPrependShuffle ν.length) ⟨ν, rfl⟩)
      (wordLeadingMoveProduct D Sc i ν ≫
        prependShuffleHom D Sc i (longPrependShuffle ν.length) ⟨ν, rfl⟩) =
      leadingMoveOrderedCoefficients D Sc i ν := by
  rw [wordLeadingMoveProduct_expansion]
  erw [Preadditive.sum_comp]
  simp only [map_sum, leadingMoveOrderedCoefficients]
  apply Finset.sum_congr rfl
  intro c _
  erw [Linear.smul_comp]
  rw [map_smul, prependWordCoefficients_endpointDots]

/-- Delete moving dots and renumber every old source position. -/
def sourceOldDots : List ℕ → List ℕ
  | [] => []
  | 0 :: ps => sourceOldDots ps
  | (p + 1) :: ps => p :: sourceOldDots ps

/-- The unsigned old dot monomial, with no coordinate extraction. -/
def sourceUnsignedCoefficient (ν : List I) : List ℕ → Hn D Sc ν.length
  | [] => FiniteHomMatrix.single ⟨ν, rfl⟩ ⟨ν, rfl⟩ (𝟙 _)
  | 0 :: ps => sourceUnsignedCoefficient ν ps
  | (p + 1) :: ps => sourceUnsignedCoefficient ν ps *
      FiniteHomMatrix.single ⟨ν, rfl⟩ ⟨ν, rfl⟩ (wordPositionDot D Sc ⟨ν, rfl⟩ p)

omit [Fintype I] in
private theorem matrixTwist_zero (m : ℕ) (z : Hn D Sc m) :
    homMatrixTwist D Sc m 0 z = z := by
  induction z using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [ha, hb]
  | hs s t f => simp

omit [Fintype I] in
/-- For the moving square product all separation signs cancel: even moving
colours twist trivially; odd blocks contain moving dots in adjacent pairs. -/
theorem sourceOldCoefficient_leadingSourceDots (i : I) (ν μ : List I)
    (a : ℕ) (c : MoveChoices μ) :
    sourceOldCoefficient D Sc i ν (leadingSourceDots D i 0 a μ c) =
      sourceUnsignedCoefficient D Sc ν (leadingSourceDots D i 0 a μ c) := by
  induction μ generalizing a with
  | nil => rfl
  | cons j μ ih =>
    rcases c with ⟨b, c⟩
    by_cases hij : i = j
    · subst j
      rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
      all_goals
        fin_cases b <;>
          simp [leadingSourceDots, leadingSourceBlockDots, hi,
            sourceOldCoefficient, sourceUnsignedCoefficient,
            matrixTwist_zero, homMatrixTwist_twice, ih]
    · simp [leadingSourceDots, leadingSourceBlockDots, hij, ih]

omit [Fintype I] in
/-- The unsigned coefficient is literally one old diagonal dot monomial. -/
theorem sourceUnsignedCoefficient_single (ν : List I) (ps : List ℕ) :
    sourceUnsignedCoefficient D Sc ν ps =
      FiniteHomMatrix.single ⟨ν, rfl⟩ ⟨ν, rfl⟩
        (wordEndpointDots D Sc ⟨ν, rfl⟩ (sourceOldDots ps)) := by
  induction ps with
  | nil =>
    simp only [sourceUnsignedCoefficient, sourceOldDots]
    congr 1
  | cons p ps ih =>
    cases p with
    | zero => exact ih
    | succ p => simp only [sourceUnsignedCoefficient, sourceOldDots, ih,
        wordEndpointDots_cons, FiniteHomMatrix.single_mul_single]

omit [Fintype I] in
/-- Closed finite-sum evaluation: moving degrees are zero-position counts and
old coefficients are unsigned diagonal monomials with the moving dots deleted. -/
theorem leadingMoveOrderedCoefficients_explicit (i : I) (ν : List I) :
    leadingMoveOrderedCoefficients D Sc i ν =
      ∑ c : MoveChoices ν, leadingMoveCoeff D (k := k) i ν c •
        Finsupp.single (longPrependShuffle ν.length,
          sourceMovingDegree (leadingSourceDots D i 0 0 ν c))
          (FiniteHomMatrix.single ⟨ν, rfl⟩ ⟨ν, rfl⟩
            (wordEndpointDots D Sc ⟨ν, rfl⟩
              (sourceOldDots (leadingSourceDots D i 0 0 ν c)))) := by
  simp only [leadingMoveOrderedCoefficients, sourceOldCoefficient_leadingSourceDots,
    sourceUnsignedCoefficient_single]

theorem sourceMovingDegree_append (ps qs : List ℕ) :
    sourceMovingDegree (ps ++ qs) = sourceMovingDegree ps + sourceMovingDegree qs := by
  induction ps with
  | nil => simp [sourceMovingDegree]
  | cons p ps ih =>
    cases p <;> simp [sourceMovingDegree, ih, Nat.add_right_comm]

omit [Fintype I] in
/-- Odd moving colours have only even moving degrees, including zero. -/
theorem sourceMovingDegree_leadingSourceDots_even (i : I) (hi : D.parity i = 1)
    (a : ℕ) (ν : List I) (c : MoveChoices ν) :
    sourceMovingDegree (leadingSourceDots D i 0 a ν c) % 2 = 0 := by
  induction ν generalizing a with
  | nil => rfl
  | cons j ν ih =>
    rcases c with ⟨b, c⟩
    by_cases hij : i = j
    · subst j
      fin_cases b <;>
        simp [leadingSourceDots, leadingSourceBlockDots, hi,
          sourceMovingDegree, Nat.add_mod, ih]
    · simp [leadingSourceDots, leadingSourceBlockDots, hij, ih]

omit [Fintype I] in
/-- The degree-normalizing sign is one on each actual moving-product term. -/
theorem leadingSourceDots_degreeSign (i : I) (q : ZMod 2)
    (a : ℕ) (ν : List I) (c : MoveChoices ν) :
    (SKM.zsign ℤ (D.parity i * q)) ^
      sourceMovingDegree (leadingSourceDots D i 0 a ν c) = 1 := by
  rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · simp [hi, SKM.zsign]
  · have he := sourceMovingDegree_leadingSourceDots_even D i hi a ν c
    have hd : Even (sourceMovingDegree (leadingSourceDots D i 0 a ν c)) :=
      Nat.even_iff.mpr he
    unfold SKM.zsign
    split_ifs
    · exact hd.neg_one_pow
    · simp

omit [Fintype I] in
/-- At every extracted degree the degree-normalizing sign acts trivially.
This does not assert invariance under the separate old matrix twist. -/
theorem leadingMoveOrderedCoefficients_degreeSign (i : I) (q : ZMod 2)
    (ν : List I) (u : PrependShuffle ν.length) (m : ℕ) :
    (SKM.zsign ℤ (D.parity i * q)) ^ m •
      leadingMoveOrderedCoefficients D Sc i ν (u, m) =
      leadingMoveOrderedCoefficients D Sc i ν (u, m) := by
  simp only [leadingMoveOrderedCoefficients, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : (longPrependShuffle ν.length,
      sourceMovingDegree (leadingSourceDots D i 0 0 ν c)) = (u, m)
  · have hm := congrArg Prod.snd h
    dsimp only at hm
    rw [← hm, leadingSourceDots_degreeSign, one_smul]
  · simp [h]

omit [Fintype I] in
/-- The prescribed leading crossing word is already the canonical descending run. -/
theorem leadingMoveWord_eq_descRun (l ν : List I) :
    leadingMoveWord l ν = descRun l.length ν.length := by
  induction ν generalizing l with
  | nil => rfl
  | cons j ν ih => simp [leadingMoveWord, ih, descRun_succ]

/-- The concrete finite producer also evaluates the original endpoint-polynomial
expression, with exactly the source and target words used by moving coefficients. -/
theorem prependEntryCoefficients_leadingEndpoint (i : I) (ν : List I) :
    prependEntryCoefficients D Sc i ν ⟨ν ++ [i], by simp⟩
      (leadingMoveEndpointPolynomial D Sc i [] ν ≫
        cl D Sc _ _ (cw (leadingMoveWord [] ν)) (leadingMoveWord_sChain i [] ν)) =
      leadingMoveOrderedCoefficients D Sc i ν := by
  have h := prependWordCoefficients_leadingMoveProduct D Sc i ν
  change prependEntryCoefficients D Sc i ν
    ⟨tgt (i :: ν) (cw (canWord (ν.length + 1) (longPrependShuffle ν.length).1⁻¹)),
      by simp⟩
    (leadingMoveProduct D Sc i [] ν ≫
      cl D Sc _ _ (cw (canWord (ν.length + 1) (longPrependShuffle ν.length).1⁻¹))
        (sChain_pl _ _)) = _ at h
  have hw : descRun 0 ν.length = leadingMoveWord ([] : List I) ν :=
    (leadingMoveWord_eq_descRun [] ν).symm
  erw [canWord_longPrependShuffle, hw] at h
  have ht : tgt (i :: ν) (cw (leadingMoveWord [] ν)) = ν ++ [i] :=
    tgt_eq (leadingMoveWord_sChain i [] ν)
  have hc (t t' : Word I (ν.length + 1)) (he : t = t')
      (h₁ : SChain (i :: ν) (pl (i :: ν) (cw (leadingMoveWord [] ν))) t.1)
      (h₂ : SChain (i :: ν) (pl (i :: ν) (cw (leadingMoveWord [] ν))) t'.1) :
      prependEntryCoefficients D Sc i ν t
          (leadingMoveProduct D Sc i [] ν ≫ cl D Sc _ _ _ h₁) =
        prependEntryCoefficients D Sc i ν t'
          (leadingMoveProduct D Sc i [] ν ≫ cl D Sc _ _ _ h₂) := by
    subst t'
    rfl
  rw [leadingMoveEndpointPolynomial_eq_product]
  exact (hc _ _ (Subtype.ext ht) _ _).symm.trans h

theorem sourceOldDots_append (ps qs : List ℕ) :
    sourceOldDots (ps ++ qs) = sourceOldDots ps ++ sourceOldDots qs := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p <;> simp [sourceOldDots, ih]

omit [Fintype I] in
/-- Old positions in the finite producer are already in PBW order and bounded. -/
theorem sourceOldDots_leadingSourceDots_ordered (i : I) (a : ℕ)
    (ν : List I) (c : MoveChoices ν) :
    (sourceOldDots (leadingSourceDots D i 0 a ν c)).Pairwise (· ≤ ·) ∧
      ∀ p ∈ sourceOldDots (leadingSourceDots D i 0 a ν c), a ≤ p ∧ p < a + ν.length := by
  induction ν generalizing a with
  | nil => simp [leadingSourceDots, sourceOldDots]
  | cons j ν ih =>
    rcases c with ⟨b, c⟩
    obtain ⟨hs, hb⟩ := ih (a + 1) c
    have hlo : ∀ p ∈ sourceOldDots (leadingSourceDots D i 0 (a + 1) ν c), a ≤ p := by
      intro p hp
      exact Nat.le_trans (Nat.le_succ a) (hb p hp).1
    have hrange : ∀ p ∈ sourceOldDots (leadingSourceDots D i 0 (a + 1) ν c),
        a ≤ p ∧ p < a + (j :: ν).length := by
      intro p hp
      have := hb p hp
      simp only [List.length_cons]
      omega
    by_cases hij : i = j
    · subst j
      rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
      all_goals
        fin_cases b <;>
          simp [leadingSourceDots, leadingSourceBlockDots, hi,
            sourceOldDots, List.pairwise_cons, hs] <;>
          first | exact hrange | exact ⟨hlo, hrange⟩
    · simp only [leadingSourceDots, leadingSourceBlockDots, hij, ↓reduceIte,
        List.nil_append]
      exact ⟨hs, hrange⟩

private theorem canonicalWord_one (n : ℕ) : canWord n 1 = [] :=
  List.length_eq_zero_iff.mp (by simp [length_canWord])

/-- The old PBW index of an expansion choice has identity permutation. -/
def leadingMoveOldNFIdx (i : I) (ν : List I) (c : MoveChoices ν) : NFIdx ν ν :=
  ⟨(sourceOldDots (leadingSourceDots D i 0 0 ν c), 1),
    (sourceOldDots_leadingSourceDots_ordered D i 0 ν c).1,
    fun p hp => by
      simpa using (sourceOldDots_leadingSourceDots_ordered D i 0 ν c).2 p hp |>.2,
    by simpa [canonicalWord_one, cw, tgt_map_dot] using
      sChain_pl ν ((sourceOldDots (leadingSourceDots D i 0 0 ν c)).map PG.dot)⟩

omit [Fintype I] in
/-- Every old coefficient is exactly one identity-permutation PBW basis vector. -/
theorem sourceOldCoefficient_leadingSourceDots_basis (i : I) (ν : List I)
    (c : MoveChoices ν) :
    sourceOldCoefficient D Sc i ν (leadingSourceDots D i 0 0 ν c) =
      Hn.basis D Sc ν.length ⟨(⟨ν, rfl⟩, ⟨ν, rfl⟩), leadingMoveOldNFIdx D i ν c⟩ := by
  rw [sourceOldCoefficient_leadingSourceDots, sourceUnsignedCoefficient_single,
    Hn.basis_apply]
  congr 1
  exact cl_congr_gs D Sc (by simp [leadingMoveOldNFIdx, canonicalWord_one, cw]) _ _

omit [Fintype I] in
/-- Nonidentity old permutations have zero coefficient in the evaluated product. -/
theorem leadingMoveOrderedCoefficients_nonidentity (i : I) (ν : List I)
    (u : PrependShuffle ν.length) (m : ℕ) (x : HnIdx I ν.length)
    (hx : x.2.1.2 ≠ 1) :
    (Hn.basis D Sc ν.length).repr (leadingMoveOrderedCoefficients D Sc i ν (u, m)) x = 0 := by
  simp only [leadingMoveOrderedCoefficients, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro c _
  by_cases he : (longPrependShuffle ν.length,
      sourceMovingDegree (leadingSourceDots D i 0 0 ν c)) = (u, m)
  · simp only [Finsupp.single_apply, he, ↓reduceIte,
      sourceOldCoefficient_leadingSourceDots_basis, Module.Basis.repr_self]
    have hn : (⟨(⟨ν, rfl⟩, ⟨ν, rfl⟩), leadingMoveOldNFIdx D i ν c⟩ :
        HnIdx I ν.length) ≠ x := by
      intro h
      subst x
      exact hx rfl
    simp [hn]
  · simp [he]

/-- The requested concrete longest-shuffle evaluation of the prescribed moving
homomorphism itself, not just its collected endpoint polynomial. -/
theorem prependWordCoefficients_moveHom_ordered (i : I) (ν : List I) (m : ℕ) :
    prependWordCoefficients D Sc i ⟨ν, rfl⟩ (appendWord i ⟨ν, rfl⟩)
      (moveHom D Sc i [] ν) (longPrependShuffle ν.length, m) =
      leadingMoveOrderedCoefficients D Sc i ν (longPrependShuffle ν.length, m) := by
  rw [prependWordCoefficients_moveHom_long]
  exact congrArg (fun f => f (longPrependShuffle ν.length, m))
    (prependEntryCoefficients_leadingEndpoint D Sc i ν)

end OddMath.QuiverHecke
