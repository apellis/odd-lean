/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveOrderedCoefficients

/-!
# Explicit normalized moving-source extraction

The old diagonal dot monomials have even parity, so every old matrix twist
acts trivially. Together with the checked moving-degree sign cancellation,
this evaluates the actual content moving source by a finite word/choice sum.
The affine result holds at all old heights; the append tensor result retains
the existing old-height `n+1` scope and the unchanged right coefficient.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA
open scoped Classical
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

omit [Fintype I] in
private theorem oldDots_parity (i : I) (w l μ : List I) (h : w = l ++ μ)
    (c : MoveChoices μ) :
    chainParity D w ((sourceOldDots (leadingSourceDots D i 0 l.length μ c)).map PG.dot) = 0 := by
  induction μ generalizing l with
  | nil => simp [leadingSourceDots, sourceOldDots]
  | cons j μ ih =>
    rcases c with ⟨b, c⟩
    have ht := ih (l ++ [j]) (by simpa [List.append_assoc] using h) c
    simp only [List.length_append, List.length_singleton] at ht
    have hj : w[l.length]? = some j := by simp [h]
    by_cases hij : i = j
    · subst j
      rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
      all_goals
        fin_cases b <;>
          simp [leadingSourceDots, leadingSourceBlockDots, hi, sourceOldDots,
            chainParity, PG.act, PG.par, hj, ht]
    · simpa [leadingSourceDots, leadingSourceBlockDots, hij, sourceOldDots] using ht

omit [Fintype I] in
/-- The old diagonal monomials in the moving product have even total parity. -/
theorem leadingMoveOldDots_twist (i : I) (ν : List I) (c : MoveChoices ν) (q : ZMod 2) :
    Supercategory.twist k q
      (wordEndpointDots D Sc ⟨ν, rfl⟩ (sourceOldDots (leadingSourceDots D i 0 0 ν c))) =
      wordEndpointDots D Sc ⟨ν, rfl⟩ (sourceOldDots (leadingSourceDots D i 0 0 ν c)) := by
  have hp := oldDots_parity D i ν [] ν rfl c
  have hf : Fits ν.length ((sourceOldDots (leadingSourceDots D i 0 0 ν c)).map PG.dot) := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    have hb := (sourceOldDots_leadingSourceDots_ordered D i 0 ν c).2 p hp |>.2
    change p + 1 ≤ ν.length
    omega
  have hm := cl_mem_chainParity D Sc _
    (show SChain ν (pl ν ((sourceOldDots (leadingSourceDots D i 0 0 ν c)).map PG.dot)) ν from
      by simpa only [tgt_map_dot] using
        sChain_pl ν ((sourceOldDots (leadingSourceDots D i 0 0 ν c)).map PG.dot)) hf
  simp only [List.length_nil] at hp
  rw [hp] at hm
  exact (Supercategory.twist_of_mem q hm).trans (by
    simp [wordEndpointDots, endpointDotMonomial])

omit [Fintype I] in
/-- Every evaluated coefficient is fixed by every old matrix parity twist. -/
theorem leadingMoveOrderedCoefficients_twist (i : I) (ν : List I)
    (q : ZMod 2) (u : PrependShuffle ν.length) (m : ℕ) :
    homMatrixTwist D Sc ν.length q (leadingMoveOrderedCoefficients D Sc i ν (u, m)) =
      leadingMoveOrderedCoefficients D Sc i ν (u, m) := by
  simp only [leadingMoveOrderedCoefficients_explicit, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : (longPrependShuffle ν.length,
      sourceMovingDegree (leadingSourceDots D i 0 0 ν c)) = (u, m)
  · simp only [Finsupp.single_apply, h, ↓reduceIte, homMatrixTwist_single,
      leadingMoveOldDots_twist]
  · simp [h]

/-- Explicit old diagonal coefficient at an arbitrary old height. -/
def leadingMoveWordCoefficient (i : I) {n : ℕ} (s : Word I n) (m : ℕ) : Hn D Sc n :=
  ∑ c : MoveChoices s.1,
    if sourceMovingDegree (leadingSourceDots D i 0 0 s.1 c) = m then
      leadingMoveCoeff D (k := k) i s.1 c •
        FiniteHomMatrix.single s s (wordEndpointDots D Sc s
          (sourceOldDots (leadingSourceDots D i 0 0 s.1 c)))
    else 0

private theorem leadingMoveWordCoefficient_eq (i : I) (ν : List I) (m : ℕ) :
    leadingMoveWordCoefficient D Sc i ⟨ν, rfl⟩ m =
      leadingMoveOrderedCoefficients D Sc i ν (longPrependShuffle ν.length, m) := by
  simp only [leadingMoveWordCoefficient, leadingMoveOrderedCoefficients_explicit,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    Prod.mk.injEq, true_and]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

/-- A finite sum over content words and local square choices; no inverse coordinates. -/
def leadingMoveContentCoefficient (i : I) (n : ℕ) (β : Multiset I) (m : ℕ) : Hn D Sc n :=
  ∑ s ∈ Finset.univ.filter (fun s : Word I n => wordContent s = β),
    leadingMoveWordCoefficient D Sc i s m

/-- Evaluation of the actual moving source, for every old height. -/
theorem contentMove_long_prependCoefficients_explicit (i : I) (n : ℕ)
    (β : Multiset I) (m : ℕ) :
    prependCoefficients D Sc i n (contentMove D Sc i n β) (longPrependShuffle n, m) =
      leadingMoveContentCoefficient D Sc i n β m := by
  simp only [contentMove, leadingMoveContentCoefficient, map_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  rcases s with ⟨ν, hν⟩
  subst n
  rw [leadingMoveWordCoefficient_eq]
  erw [prependCoefficients_single]
  exact prependWordCoefficients_moveHom_ordered D Sc i ν m

/-- The explicit finite content sum is invariant under the old matrix twist. -/
theorem leadingMoveContentCoefficient_twist (i : I) (n : ℕ) (β : Multiset I)
    (m : ℕ) (q : ZMod 2) :
    homMatrixTwist D Sc n q (leadingMoveContentCoefficient D Sc i n β m) =
      leadingMoveContentCoefficient D Sc i n β m := by
  simp only [leadingMoveContentCoefficient, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rcases s with ⟨ν, hν⟩
  subst n
  rw [leadingMoveWordCoefficient_eq, leadingMoveOrderedCoefficients_twist]

/-- The degree normalization is also trivial on the explicit content sum. -/
theorem leadingMoveContentCoefficient_degreeSign (i : I) (n : ℕ) (β : Multiset I)
    (m : ℕ) (q : ZMod 2) :
    (SKM.zsign ℤ (D.parity i * q)) ^ m • leadingMoveContentCoefficient D Sc i n β m =
      leadingMoveContentCoefficient D Sc i n β m := by
  simp only [leadingMoveContentCoefficient, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rcases s with ⟨ν, hν⟩
  subst n
  rw [leadingMoveWordCoefficient_eq, leadingMoveOrderedCoefficients_degreeSign]

/-- Normalized longest extraction of the actual content moving tensor.
The right coefficient is unchanged; this uses the existing append source at old height `n+1`.
No full ELV boundary or corrected `w_k` identification is asserted. -/
theorem appendContentMoveLift_extract_explicit (a : I → _root_.Polynomial k)
    (n : ℕ) (β : Multiset I) (i : I)
    (b : CyclotomicContentCorner D Sc a n β) (m : ℕ) :
    appendContentRhoExtract D Sc a n β i (appendContentMoveLift D Sc a n β i b) m =
      leadingMoveContentCoefficient D Sc i (n + 1) β m • b := by
  rw [appendContentMoveLift_extract, contentMove_long_prependCoefficients_explicit,
    leadingMoveContentCoefficient_twist]
  let f : Hn D Sc (n + 1) →+ CyclotomicContentCorner D Sc a n β :=
    { toFun := fun z => z • b
      map_zero' := by
        change (0 : Hn D Sc (n + 1)) • b = 0
        exact zero_smul (Hn D Sc (n + 1)) b
      map_add' := fun x y => add_smul x y b }
  exact (f.map_zsmul _ _).symm.trans
    (congrArg f (leadingMoveContentCoefficient_degreeSign D Sc i (n + 1) β m _))

/-- Fully expanded finite normalized extraction, with no coordinate maps on the right. -/
theorem appendContentMoveLift_extract_sum (a : I → _root_.Polynomial k)
    (n : ℕ) (β : Multiset I) (i : I)
    (b : CyclotomicContentCorner D Sc a n β) (m : ℕ) :
    appendContentRhoExtract D Sc a n β i (appendContentMoveLift D Sc a n β i b) m =
      (∑ s ∈ Finset.univ.filter (fun s : Word I (n + 1) => wordContent s = β),
        ∑ c : MoveChoices s.1,
          if sourceMovingDegree (leadingSourceDots D i 0 0 s.1 c) = m then
            leadingMoveCoeff D (k := k) i s.1 c •
              FiniteHomMatrix.single s s (wordEndpointDots D Sc s
                (sourceOldDots (leadingSourceDots D i 0 0 s.1 c)))
          else 0) • b :=
  appendContentMoveLift_extract_explicit D Sc a n β i b m

end OddMath.QuiverHecke
