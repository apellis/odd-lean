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

/-- Explicit old diagonal coefficient at an arbitrary old height. -/
def leadingMoveWordCoefficient (i : I) {n : ℕ} (s : Word I n) (m : ℕ) : Hn D Sc n :=
  ∑ c : MoveChoices s.1,
    if sourceMovingDegree (leadingSourceDots D i 0 0 s.1 c) = m then
      leadingMoveCoeff D (k := k) i s.1 c •
        FiniteHomMatrix.single s s (wordEndpointDots D Sc s
          (sourceOldDots (leadingSourceDots D i 0 0 s.1 c)))
    else 0

/-- A finite sum over content words and local square choices; no inverse coordinates. -/
def leadingMoveContentCoefficient (i : I) (n : ℕ) (β : Multiset I) (m : ℕ) : Hn D Sc n :=
  ∑ s ∈ Finset.univ.filter (fun s : Word I n => wordContent s = β),
    leadingMoveWordCoefficient D Sc i s m

end OddMath.QuiverHecke
