/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PositiveDecoratedCoefficients

/-!
# Coefficient fixtures for positive decorated matchings

Concrete odd rank-one applications of `positive_decorated_coeff`: negative crossing
shift, a vanishing fiber below it, repeated-colour dot allocations, and the empty
word over a ring with zero divisors. All matching and root-datum hypotheses are proved.
-/

noncomputable section
namespace OddMath.SKM.PositiveDecoratedCoefficientsExamples
open CoveringQuantum StringDiagrams StringDiagrams.Chord
open scoped BigOperators

/-- One odd simple root, with Cartan entry two and symmetrizer one. -/
private def oddDatum : RootDatum Unit ℤ where
  a := Matrix.of fun _ _ => 2
  isGCM :=
    { diag := fun _ => rfl
      offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
      zero_comm := fun _ _ => Iff.rfl }
  d := fun _ => 1
  d_pos := fun _ => one_pos
  d_mul_symm := fun _ _ => rfl
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two
  cd :=
    { root := fun _ => 2
      coroot := fun _ => LinearMap.id
      coroot_root_self := fun _ => rfl }
  coroot_root _ _ := rfl

private abbrev word : Fin 2 → Unit := fun _ => ()
private abbrev crossing : List (TMove (Letter Unit)) := [.mv (.cross 0)]

private theorem crossing_matching :
    IsMatching₂ (List.ofFn fun r => (true, word r))
      (List.ofFn fun r => (true, word r)) crossing := by
  constructor
  · change 3 < 4 ∧ True
    decide
  · rfl

private theorem crossing_reduced :
    StrictReduced₂ (List.ofFn fun r => (true, word r)) crossing := by
  refine ⟨⟨List.nodup_singleton _, ?_⟩, List.nodup_nil⟩
  intro z hz
  change z ∈ [_] at hz
  obtain rfl := List.mem_singleton.mp hz
  change ¬ (s(2, 0) : Sym2 ℕ).IsDiag
  decide

private theorem crossing_endpoints : ∀ r : Fin 2,
    Same (pairing₂ (List.ofFn fun r => (true, word r)) crossing)
      (2 - 1 - r.val) (2 + ((Equiv.swap 0 1) r).val) := by
  intro r
  fin_cases r
  · change 1 ≠ 3 ∧ (some 2 : Option ℕ) ≠ none ∧ (some 2 : Option ℕ) = some 2
    decide
  · change 0 ≠ 2 ∧ (some 0 : Option ℕ) ≠ none ∧ (some 0 : Option ℕ) = some 0
    decide

-- The crossing shift is -2, not a natural degree. Every hypothesis is proved.
private theorem crossing_coeff :
    ∃ p : MatchingStrand [(true, ()), (true, ())] crossing ≃ Fin 2,
      (∀ j, OnStrand₂ [(true, ()), (true, ())] crossing j.val (1, (p j).val)) ∧
      ∃ (L : (Fin 2 → ℕ) → List (LayerData Unit))
        (hL : ∀ c, SChain [(true, ()), (true, ())] (L c) [(true, ()), (true, ())]),
        (∀ c, (L c).map ofL = dLay [(true, ()), (true, ())]
          (topDotMoves [(true, ()), (true, ())] crossing
            (fun j => (p j).val) (fun j => c (p j)))) ∧
        ∀ z : ℤ,
          ∃ hf : Set.Finite {c : Fin 2 → ℕ |
            Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
              (mkD oddDatum.toSKM 0 (L c) (hL c)) = z},
            (∑ c ∈ hf.toFinset, (-1 : ℤ) ^ (xpar oddDatum.toSKM 0 ((L c).map ofL)).val) =
              if -2 ≤ z then -PowerSeries.coeff (z + 2).toNat
                (oddDatum.toSuperCartanDatum.dotSeries (-1 : ℤ) word) else 0 := by
  obtain ⟨p, hp, L, hL, hm, h⟩ := positive_decorated_coeff oddDatum 0 (-1 : ℤ)
    (by norm_num) word word crossing_matching crossing_reduced (Equiv.swap 0 1) crossing_endpoints
  refine ⟨p, hp, L, hL, hm, ?_⟩
  intro z
  obtain ⟨hf, hc⟩ := h z
  refine ⟨hf, ?_⟩
  simp only [Finset.sum_filter, Fin.sum_univ_two] at hc
  norm_num [word, oddDatum, SuperCartanDatum.dot] at hc ⊢
  have hv : (1 : ZMod 2).val = 1 := rfl
  simpa only [hv, pow_one, neg_one_mul] using hc

-- The degree -3 fiber vanishes; degree -2 has the odd crossing contribution.
-- At degree 4 all four allocations, including ![1, 2] and ![2, 1], contribute.
example : ∃ (L : (Fin 2 → ℕ) → List (LayerData Unit))
    (hL : ∀ c, SChain [(true, ()), (true, ())] (L c) [(true, ()), (true, ())]),
    ∀ t : Fin 4, ∃ hf : Set.Finite {c : Fin 2 → ℕ |
      Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
        (mkD oddDatum.toSKM 0 (L c) (hL c)) = (![-3, -2, 0, 4] : Fin 4 → ℤ) t},
      (∑ c ∈ hf.toFinset, (-1 : ℤ) ^ (xpar oddDatum.toSKM 0 ((L c).map ofL)).val) =
        (![0, -1, 2, 4] : Fin 4 → ℤ) t := by
  obtain ⟨_, _, L, hL, _, h⟩ := crossing_coeff
  refine ⟨L, hL, ?_⟩
  have hcoeff (m : ℕ) : PowerSeries.coeff m
      (oddDatum.toSuperCartanDatum.dotSeries (-1 : ℤ) word) =
      PowerSeries.coeff m
        (PreF.DotSeries.factor (-1 : ℤ) 2 (by decide) *
          PreF.DotSeries.factor (-1 : ℤ) 2 (by decide)) := by
    congr 1
    simp only [SuperCartanDatum.dotSeries, PreF.DotSeries.strands, Fin.prod_univ_two]
    rfl
  intro t
  obtain ⟨hf, hc⟩ := h ((![-3, -2, 0, 4] : Fin 4 → ℤ) t)
  refine ⟨hf, ?_⟩
  fin_cases t <;>
    norm_num [hcoeff, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
      PreF.DotSeries.coeff_factor] at hc ⊢ <;> exact hc

-- Nonuniform counts on repeated odd colours: one crossing and three dots.
example :
    ∃ p : MatchingStrand [(true, ()), (true, ())] crossing ≃ Fin 2,
      (∀ j, OnStrand₂ [(true, ()), (true, ())] crossing j.val (1, (p j).val)) ∧
      ∃ (L : List (LayerData Unit))
        (hL : SChain [(true, ()), (true, ())] L [(true, ()), (true, ())]),
        L.map ofL = dLay [(true, ()), (true, ())]
          (topDotMoves [(true, ()), (true, ())] crossing
            (fun j => (p j).val) (fun j => ![1, 2] (p j))) ∧
        Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
          (mkD oddDatum.toSKM 0 L hL) = 4 ∧ xpar oddDatum.toSKM 0 (L.map ofL) = 0 := by
  obtain ⟨p, hp, hg⟩ := positive_decorated_degree_parity oddDatum.toSKM
    oddDatum.skmSymmetrizer 0 word word crossing_matching crossing_reduced
    (Equiv.swap 0 1) crossing_endpoints
  obtain ⟨L, hL, hm, hd, hpar⟩ := hg ![1, 2]
  refine ⟨p, hp, L, hL, hm, ?_, ?_⟩
  · simp only [Finset.sum_filter, Fin.sum_univ_two] at hd
    simpa [word, oddDatum, CoveringQuantum.RootDatum.toSKM_d] using hd
  · rw [hm]
    simp only [Finset.sum_filter, Fin.sum_univ_two] at hpar
    have hz : (1 + (1 + 2) : ZMod 2) = 0 := by decide
    simpa [word, oddDatum, hz] using hpar

-- Empty words and a coefficient ring with zero divisors.
example :
    ∃ p : MatchingStrand ([] : List (Letter Unit)) [] ≃ Fin 0,
      (∀ j, OnStrand₂ ([] : List (Letter Unit)) [] j.val (0, (p j).val)) ∧
      ∃ (L : (Fin 0 → ℕ) → List (LayerData Unit)) (hL : ∀ c, SChain [] (L c) []),
        (∀ c, (L c).map ofL = dLay []
          (topDotMoves [] [] (fun j => (p j).val) (fun j => c (p j)))) ∧
        ∀ z : ℤ, ∃ hf : Set.Finite {c : Fin 0 → ℕ |
          Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
            (mkD oddDatum.toSKM 0 (L c) (hL c)) = z},
          (∑ c ∈ hf.toFinset, (-1 : ZMod 4) ^ (xpar oddDatum.toSKM 0 ((L c).map ofL)).val) =
            if z = 0 then 1 else 0 := by
  let a : Fin 0 → Unit := Fin.elim0
  have hm : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, a r)) [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ (List.ofFn fun r => (true, a r)) [] :=
    ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  obtain ⟨p, hp, L, hL, hmap, h⟩ := positive_decorated_coeff oddDatum 0 (-1 : ZMod 4)
    (by decide) a a hm hr (Equiv.refl _) (fun r => Fin.elim0 r)
  refine ⟨p, hp, L, hL, hmap, ?_⟩
  intro z
  obtain ⟨hf, hc⟩ := h z
  refine ⟨hf, ?_⟩
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero,
    SuperCartanDatum.dotSeries_empty, PowerSeries.coeff_one] at hc
  by_cases hz : z = 0
  · subst z
    simpa using hc
  · by_cases hn : 0 ≤ z
    · have hp : ¬z ≤ 0 := by omega
      simpa [hz, hn, hp] using hc
    · simpa [hz, hn] using hc

end OddMath.SKM.PositiveDecoratedCoefficientsExamples
