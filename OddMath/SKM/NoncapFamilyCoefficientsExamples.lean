/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.NoncapFamilyCoefficients
import OddMath.SKM.BoundaryExchangeExamples

/-! Populated equal odd-colour non-cap coefficient fibers for both
intersection classes in BE2 v2 Theorem 10.3 Claim 5. -/
noncomputable section
namespace OddMath.SKM.NoncapFamilyCoefficientsExamples
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators
open MixedCrossingLocalExamples (oddDatum oddSymmetrizer)

private def tail (k : Bool) : List (Letter Bool) :=
  if k then [(false, false), (true, false)] else [(true, false), (false, false)]
private def A (k : Bool) : List (Letter Bool) := (true, false) :: (false, false) :: tail k
private def B (k : Bool) : List (Letter Bool) := (false, false) :: (true, false) :: tail k
private def R (k : Bool) : List (TMove (Letter Bool)) :=
  if k then [.mv (.cross 0), .cap 1, .cap 0] else [.cap 1, .cap 0]
private def S (k : Bool) : List (TMove (Letter Bool)) :=
  if k then [.cap 1, .cap 0] else [.mv (.cross 0), .cap 1, .cap 0]
private def C : List (TMove (Letter Bool)) := [.cap 0, .cap 0]
private def M (k : Bool) : Set (List (TMove (Letter Bool))) := {R k, C}
private def N (k : Bool) : Set (List (TMove (Letter Bool))) := {S k, C}
private def M₀ (k : Bool) := noncapFamily (A k) 2 (M k)
private def N₀ (k : Bool) := noncapFamily (B k) 2 (N k)
abbrev T (k : Bool) := Σ V : {V // V ∈ M₀ k}, MatchingStrand (A k) V.val → ℕ
abbrev U (k : Bool) := Σ V : {V // V ∈ N₀ k}, MatchingStrand (B k) V.val → ℕ

private theorem hm (k : Bool) : IsMatching₂ (A k) [] (R k) := by
  cases k
  · exact BoundaryExchangeExamples.matching₀
  · exact BoundaryExchangeExamples.source_matching
private theorem hn (k : Bool) : IsMatching₂ (B k) [] (S k) := by
  cases k
  · exact BoundaryExchangeExamples.matching₁
  · exact BoundaryExchangeExamples.target_matching
private theorem rm (k : Bool) : StrictReduced₂ (A k) (R k) := by
  cases k
  · exact BoundaryExchangeExamples.reduced₀
  · exact BoundaryExchangeExamples.source_reduced
private theorem rn (k : Bool) : StrictReduced₂ (B k) (S k) := by
  cases k
  · exact BoundaryExchangeExamples.reduced₁
  · exact BoundaryExchangeExamples.target_reduced

private theorem cm (k : Bool) : IsMatching₂ (A k) [] C := by
  cases k <;> refine ⟨?_, rfl⟩
  · exact ⟨⟨(6, (true, false)), (4, (false, false)), rfl, rfl, rfl, by decide⟩,
      ⟨(2, (true, false)), (0, (false, false)), rfl, rfl, rfl, by decide⟩, trivial⟩
  · exact ⟨⟨(6, (true, false)), (4, (false, false)), rfl, rfl, rfl, by decide⟩,
      ⟨(2, (false, false)), (0, (true, false)), rfl, rfl, rfl, by decide⟩, trivial⟩
private theorem cn (k : Bool) : IsMatching₂ (B k) [] C := by
  cases k <;> refine ⟨?_, rfl⟩
  · exact ⟨⟨(6, (false, false)), (4, (true, false)), rfl, rfl, rfl, by decide⟩,
      ⟨(2, (true, false)), (0, (false, false)), rfl, rfl, rfl, by decide⟩, trivial⟩
  · exact ⟨⟨(6, (false, false)), (4, (true, false)), rfl, rfl, rfl, by decide⟩,
      ⟨(2, (false, false)), (0, (true, false)), rfl, rfl, rfl, by decide⟩, trivial⟩
private theorem cr (k : Bool) : StrictReduced₂ (A k) C ∧ StrictReduced₂ (B k) C := by
  cases k <;> constructor <;>
    change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([6, 2] : List ℕ).Nodup
  all_goals simp

private theorem hM (k : Bool) : ∀ V ∈ M k, IsMatching₂ (A k) [] V ∧ StrictReduced₂ (A k) V := by
  intro V hv
  rcases hv with rfl | rfl
  · exact ⟨hm k, rm k⟩
  · exact ⟨cm k, (cr k).1⟩
private theorem hN (k : Bool) : ∀ V ∈ N k, IsMatching₂ (B k) [] V ∧ StrictReduced₂ (B k) V := by
  intro V hv
  rcases hv with rfl | rfl
  · exact ⟨hn k, rn k⟩
  · exact ⟨cn k, (cr k).2⟩

private theorem four_matchings (f : Fin 4 → Fin 4)
    (hi : ∀ i, f (f i) = i) (hn : ∀ i, f i ≠ i) :
    f = ![1, 0, 3, 2] ∨ f = ![2, 3, 0, 1] ∨ f = ![3, 2, 1, 0] := by
  have h0 := hi 0
  have h1 := hi 1
  have h2 := hi 2
  have h3 := hi 3
  have n0 := hn 0
  have n1 := hn 1
  have n2 := hn 2
  have n3 := hn 3
  generalize e0 : f 0 = v0 at *
  all_goals fin_cases v0 <;> simp_all only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  all_goals generalize e1 : f 1 = v1 at *
  all_goals fin_cases v1 <;> simp_all only [Fin.isValue]
  all_goals generalize e2 : f 2 = v2 at *
  all_goals fin_cases v2 <;> simp_all only [Fin.isValue]
  all_goals generalize e3 : f 3 = v3 at *
  all_goals fin_cases v3 <;> simp_all only [Fin.isValue]
  all_goals simp_all [funext_iff, Fin.forall_fin_succ]

private theorem iso_of_four_function {s t : List (ℕ × Letter Bool)}
    (hv : Valid s) (hs : s.length = 4) (ht : t.length = 4)
    (he : s.map Prod.snd = t.map Prod.snd) (f : Fin 4 → Fin 4)
    (hf : ∀ j, matchingOf hv hs j = f j)
    (htf : ∀ i j : Fin 4, Same t i j ↔ f i = j) : Iso s t := by
  refine ⟨he, fun i j => ?_⟩
  by_cases hi : i < 4
  · by_cases hj : j < 4
    · exact (same_iff_matchingOf hv hs ⟨i, hi⟩ ⟨j, hj⟩).trans
        ((congrArg (fun z => z = (⟨j, hj⟩ : Fin 4)) (hf ⟨i, hi⟩)).to_iff.trans
          (htf ⟨i, hi⟩ ⟨j, hj⟩).symm)
    · exact iff_of_false (fun h => hj (hs ▸ h.lt_right)) (fun h => hj (ht ▸ h.lt_right))
  · exact iff_of_false (fun h => hi (hs ▸ h.lt_left)) (fun h => hi (ht ▸ h.lt_left))

private theorem matching_length {A : List (Letter Bool)} {V : List (TMove (Letter Bool))}
    (hV : IsMatching₂ A [] V) (ha : A.length = 4) : (pairing₂ A V).length = 4 := by
  have h := congrArg List.length hV.pairing_properties.2.2
  simpa only [List.length_map, List.length_append, List.length_nil, add_zero,
    length_dualW, ha] using h

private theorem same_letter {s : List (ℕ × Letter Bool)}
    (hl : Lettered flipL s) {i j : ℕ} (h : Same s i j) :
    (s[j]?).map Prod.snd = ((s[i]?).map Prod.snd).map flipL := by
  rcases lt_or_gt_of_ne h.ne with hij | hji
  · simpa only [Option.map_map] using hl i j h hij
  · have hh := congrArg (Option.map flipL) (hl j i h.symm hji)
    simpa only [Option.map_map, Function.comp_def, flipL_flipL] using hh.symm

private theorem classifyM (k : Bool) (V : List (TMove (Letter Bool)))
    (hV : IsMatching₂ (A k) [] V) :
    Iso (pairing₂ (A k) V) (pairing₂ (A k) (R k)) ∨
      Iso (pairing₂ (A k) V) (pairing₂ (A k) C) := by
  have hv := hV.pairing_properties.1
  have hl := matching_length hV (by cases k <;> rfl)
  let f := matchingOf hv hl
  have hcases := four_matchings f (isMatching_matchingOf hv hl).1 (isMatching_matchingOf hv hl).2
  have letters (W) (hW : IsMatching₂ (A k) [] W) :
      (pairing₂ (A k) V).map Prod.snd = (pairing₂ (A k) W).map Prod.snd :=
    hV.pairing_properties.2.2.trans hW.pairing_properties.2.2.symm
  rcases hcases with hf | hf | hf
  · right
    apply iso_of_four_function hv hl (matching_length (cm k) (by cases k <;> rfl))
      (letters C (cm k)) ![1, 0, 3, 2] (fun j => congrFun hf j)
    cases k <;> unfold Same idAt <;> decide
  · cases k
    · exfalso
      have hh := same_letter hV.pairing_properties.2.1
        ((same_iff_matchingOf hv hl 0 2).mpr (congrFun hf 0))
      simp only [← List.getElem?_map, hV.pairing_properties.2.2] at hh
      contradiction
    · left
      apply iso_of_four_function hv hl (matching_length (hm true) rfl)
        (letters (R true) (hm true)) ![2, 3, 0, 1] (fun j => congrFun hf j)
      unfold Same idAt
      decide
  · cases k
    · left
      apply iso_of_four_function hv hl (matching_length (hm false) rfl)
        (letters (R false) (hm false)) ![3, 2, 1, 0] (fun j => congrFun hf j)
      unfold Same idAt
      decide
    · exfalso
      have hh := same_letter hV.pairing_properties.2.1
        ((same_iff_matchingOf hv hl 0 3).mpr (congrFun hf 0))
      simp only [← List.getElem?_map, hV.pairing_properties.2.2] at hh
      contradiction

private theorem classifyN (k : Bool) (V : List (TMove (Letter Bool)))
    (hV : IsMatching₂ (B k) [] V) :
    Iso (pairing₂ (B k) V) (pairing₂ (B k) (S k)) ∨
      Iso (pairing₂ (B k) V) (pairing₂ (B k) C) := by
  have hv := hV.pairing_properties.1
  have hl := matching_length hV (by cases k <;> rfl)
  let f := matchingOf hv hl
  have hcases := four_matchings f (isMatching_matchingOf hv hl).1 (isMatching_matchingOf hv hl).2
  have letters (W) (hW : IsMatching₂ (B k) [] W) :
      (pairing₂ (B k) V).map Prod.snd = (pairing₂ (B k) W).map Prod.snd :=
    hV.pairing_properties.2.2.trans hW.pairing_properties.2.2.symm
  rcases hcases with hf | hf | hf
  · right
    apply iso_of_four_function hv hl (matching_length (cn k) (by cases k <;> rfl))
      (letters C (cn k)) ![1, 0, 3, 2] (fun j => congrFun hf j)
    cases k <;> unfold Same idAt <;> decide
  · cases k
    · left
      apply iso_of_four_function hv hl (matching_length (hn false) rfl)
        (letters (S false) (hn false)) ![2, 3, 0, 1] (fun j => congrFun hf j)
      unfold Same idAt
      decide
    · exfalso
      have hh := same_letter hV.pairing_properties.2.1
        ((same_iff_matchingOf hv hl 0 2).mpr (congrFun hf 0))
      simp only [← List.getElem?_map, hV.pairing_properties.2.2] at hh
      contradiction
  · cases k
    · exfalso
      have hh := same_letter hV.pairing_properties.2.1
        ((same_iff_matchingOf hv hl 0 3).mpr (congrFun hf 0))
      simp only [← List.getElem?_map, hV.pairing_properties.2.2] at hh
      contradiction
    · left
      apply iso_of_four_function hv hl (matching_length (hn true) rfl)
        (letters (S true) (hn true)) ![3, 2, 1, 0] (fun j => congrFun hf j)
      unfold Same idAt
      decide

private theorem notsameR (k : Bool) : ¬ Same (pairing₂ (A k) (R k)) 2 3 := by
  cases k <;> unfold Same idAt <;> decide
private theorem notsameS (k : Bool) : ¬ Same (pairing₂ (B k) (S k)) 2 3 := by
  cases k <;> unfold Same idAt <;> decide
private theorem sameCM (k : Bool) : Same (pairing₂ (A k) C) 2 3 := by
  cases k <;> unfold Same idAt <;> decide
private theorem sameCN (k : Bool) : Same (pairing₂ (B k) C) 2 3 := by
  cases k <;> unfold Same idAt <;> decide

private theorem hMrep (k : Bool) : ∀ V, IsMatching₂ (A k) [] V → StrictReduced₂ (A k) V →
    ∃ W ∈ M k, Iso (pairing₂ (A k) W) (pairing₂ (A k) V) := by
  intro V h _
  rcases classifyM k V h with h | h
  · exact ⟨R k, Or.inl rfl, h.symm⟩
  · exact ⟨C, Or.inr rfl, h.symm⟩
private theorem hNrep (k : Bool) : ∀ V, IsMatching₂ (B k) [] V → StrictReduced₂ (B k) V →
    ∃ W ∈ N k, Iso (pairing₂ (B k) W) (pairing₂ (B k) V) := by
  intro V h _
  rcases classifyN k V h with h | h
  · exact ⟨S k, Or.inl rfl, h.symm⟩
  · exact ⟨C, Or.inr rfl, h.symm⟩
private theorem hMuniq (k : Bool) : ∀ V ∈ M k, ∀ W ∈ M k,
    Iso (pairing₂ (A k) V) (pairing₂ (A k) W) → V = W := by
  intro V hv W hw h
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
  · rfl
  · exact False.elim (notsameR k ((h.2 2 3).mpr (sameCM k)))
  · exact False.elim (notsameR k ((h.2 2 3).mp (sameCM k)))
  · rfl
private theorem hNuniq (k : Bool) : ∀ V ∈ N k, ∀ W ∈ N k,
    Iso (pairing₂ (B k) V) (pairing₂ (B k) W) → V = W := by
  intro V hv W hw h
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
  · rfl
  · exact False.elim (notsameS k ((h.2 2 3).mpr (sameCN k)))
  · exact False.elim (notsameS k ((h.2 2 3).mp (sameCN k)))
  · rfl

private theorem filteredM (k : Bool) : M₀ k = {R k} := by
  ext V
  constructor
  · rintro ⟨h | h, hn⟩
    · exact h
    · subst V; exact False.elim (hn (sameCM k))
  · rintro rfl
    exact ⟨Or.inl rfl, notsameR k⟩
private theorem filteredN (k : Bool) : N₀ k = {S k} := by
  ext V
  constructor
  · rintro ⟨h | h, hn⟩
    · exact h
    · subst V; exact False.elim (hn (sameCN k))
  · rintro rfl
    exact ⟨Or.inl rfl, notsameS k⟩

private theorem endsR (k : Bool) : leftEnds₂ (A k) (R k) = [0, 1] := by
  classical
  cases k
  · change (List.range 4).filter (fun j => decide (IsLeftEnd
      [(6, (true, false)), (4, (false, false)), (4, (true, false)), (6, (false, false))] j)) =
        [0, 1]
    norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
    exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  · change (List.range 4).filter (fun j => decide (IsLeftEnd
      [(4, (false, false)), (6, (true, false)), (4, (true, false)), (6, (false, false))] j)) =
        [0, 1]
    norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
    exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

private theorem endsS (k : Bool) : leftEnds₂ (B k) (S k) = [0, 1] := by
  classical
  cases k
  · change (List.range 4).filter (fun j => decide (IsLeftEnd
      [(4, (true, false)), (6, (false, false)), (4, (false, false)), (6, (true, false))] j)) =
        [0, 1]
    norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
    exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
  · change (List.range 4).filter (fun j => decide (IsLeftEnd
      [(6, (false, false)), (4, (true, false)), (4, (false, false)), (6, (true, false))] j)) =
        [0, 1]
    norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
    exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩

private def q (k : Bool) (_ : {V // V ∈ M₀ k}) (j : ℕ) : ℕ × ℕ := (0, 3 - j)
private def r (k : Bool) (_ : {V // V ∈ N₀ k}) (j : ℕ) : ℕ × ℕ :=
  (if k then 0 else 1, if j = 1 then 1 else 0)
private theorem hq (k : Bool) : ∀ V j, j ∈ leftEnds₂ (A k) V.val →
    (q k V j).1 ≤ V.val.length ∧ OnStrand₂ (A k) V.val j (q k V j) := by
  rintro ⟨V, hv⟩ j hj
  obtain rfl := Set.mem_singleton_iff.mp ((filteredM k) ▸ hv)
  simp only [endsR, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> cases k <;> dsimp only [q, r] <;> unfold OnStrand₂ <;> decide
private theorem hr (k : Bool) : ∀ V j, j ∈ leftEnds₂ (B k) V.val →
    (r k V j).1 ≤ V.val.length ∧ OnStrand₂ (B k) V.val j (r k V j) := by
  rintro ⟨V, hv⟩ j hj
  obtain rfl := Set.mem_singleton_iff.mp ((filteredN k) ▸ hv)
  simp only [endsS, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> cases k <;> dsimp only [q, r] <;> unfold OnStrand₂ <;> decide

private def τ (k : Bool) (V : {V // V ∈ M₀ k}) (c : MatchingStrand (A k) V.val → ℕ) :
    List (DTMove Bool) :=
  (exists_decorates₂_of_bounded_points (A k) V.val (q k V)
    (fun j hj => (hq k V j hj).2) (fun j hj => (hq k V j hj).1) c).choose
private theorem hτ (k : Bool) (V : {V // V ∈ M₀ k}) (c : MatchingStrand (A k) V.val → ℕ) :
    Decorates₂ (A k) V.val (q k V) (strandCounts c) (τ k V c) :=
  (exists_decorates₂_of_bounded_points (A k) V.val (q k V)
    (fun j hj => (hq k V j hj).2) (fun j hj => (hq k V j hj).1) c).choose_spec.1
private def υ (k : Bool) (V : {V // V ∈ N₀ k}) (c : MatchingStrand (B k) V.val → ℕ) :
    List (DTMove Bool) :=
  (exists_decorates₂_of_bounded_points (B k) V.val (r k V)
    (fun j hj => (hr k V j hj).2) (fun j hj => (hr k V j hj).1) c).choose
private theorem hυ (k : Bool) (V : {V // V ∈ N₀ k}) (c : MatchingStrand (B k) V.val → ℕ) :
    Decorates₂ (B k) V.val (r k V) (strandCounts c) (υ k V c) :=
  (exists_decorates₂_of_bounded_points (B k) V.val (r k V)
    (fun j hj => (hr k V j hj).2) (fun j hj => (hr k V j hj).1) c).choose_spec.1

/-- An actual application to both complete families, with independently fixed
valid serializers for all natural counts; the equivalence precedes all gradings. -/
theorem equal_odd_families (k : Bool) : ∃ F : T k ≃ U k,
    ∀ (D : Datum Bool (Bool → ℤ)) (sy : Symmetrizer D) (μ : Bool → ℤ),
    let d := fun t : T k => tableDegree D sy μ (dLay (A k) (τ k t.1 t.2))
    let e := fun u : U k => tableDegree D sy μ (dLay (B k) (υ k u.1 u.2))
    let p := fun t : T k => xpar D μ (dLay (A k) (τ k t.1 t.2))
    let p' := fun u : U k => xpar D μ (dLay (B k) (υ k u.1 u.2))
    ∃ (hf : ∀ z : ℤ, Set.Finite {t | d t = z}) (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
      (∀ t, e (F t) = d t ∧ p' (F t) = p t + D.parity false) ∧
      (∀ z, Nonempty ({t // d t = z} ≃ {u // e u = z})) ∧
      ∀ σ : ℚ, σ ^ 2 = 1 → ∀ z : ℤ,
        (∑ u ∈ (hg z).toFinset, σ ^ (p' u).val) =
          σ ^ (D.parity false).val * ∑ t ∈ (hf z).toFinset, σ ^ (p t).val ∧
        (∑ t ∈ (hf z).toFinset, σ ^ (p t).val) =
          σ ^ (D.parity false).val * ∑ u ∈ (hg z).toFinset, σ ^ (p' u).val := by
  cases k
  · exact noncap_labelled_family_coefficients (a := []) (b := tail false)
      (hM false) (hN false) (q false) (r false)
      (fun V j hj => (hq false V j hj).2) (fun V j hj => (hr false V j hj).2)
      (τ false) (υ false) (hτ false) (hυ false) (hMrep false) (hNrep false)
      (hMuniq false) (hNuniq false)
  · exact noncap_labelled_family_coefficients (a := []) (b := tail true)
      (hM true) (hN true) (q true) (r true)
      (fun V j hj => (hq true V j hj).2) (fun V j hj => (hr true V j hj).2)
      (τ true) (υ true) (hτ true) (hυ true) (hMrep true) (hNrep true) (hMuniq true) (hNuniq true)

private abbrev D := oddDatum
private abbrev sy := oddSymmetrizer
def d (k : Bool) (t : T k) : ℤ := tableDegree D sy 0 (dLay (A k) (τ k t.1 t.2))
def e (k : Bool) (u : U k) : ℤ := tableDegree D sy 0 (dLay (B k) (υ k u.1 u.2))
def p (k : Bool) (t : T k) : ZMod 2 := xpar D 0 (dLay (A k) (τ k t.1 t.2))
def p' (k : Bool) (u : U k) : ZMod 2 := xpar D 0 (dLay (B k) (υ k u.1 u.2))
private def jf (k : Bool) : MatchingStrand (A k) (R k) :=
  ⟨if k then 1 else 0, by rw [endsR]; cases k <;> simp⟩
private def jt (k : Bool) : MatchingStrand (A k) (R k) :=
  ⟨if k then 0 else 1, by rw [endsR]; cases k <;> simp⟩
private def oneDot (k : Bool) : T k :=
  ⟨⟨R k, ⟨Or.inl rfl, notsameR k⟩⟩, fun j => if j.val = (jf k).val then 1 else 0⟩

private theorem base_values (k : Bool) :
    tableDegree D sy 0 (tLay (A k) (R k)) = 0 ∧
    xpar D 0 (tLay (A k) (R k)) = if k then 0 else 1 := by
  cases k <;>
    norm_num [A, R, tail, tLay, tmLay, tLet, moveLay, chStep, lstep, swapAt, xCrL, xCapL,
      sigmaL, up, dn,
      tableDegree, xpar, xlpar, ofL, gdeg, Shape.parity, xwhL, wt, sh, ipar,
      D, sy, oddDatum, oddSymmetrizer, Datum.h, Datum.α, Datum.d,
      PositivePointGradingExamples.twoColourDatum]
  all_goals rfl

private theorem count_grading (k : Bool) (c : MatchingStrand (A k) (R k) → ℕ) :
    d k ⟨⟨R k, ⟨Or.inl rfl, notsameR k⟩⟩, c⟩ = 0 + 2 * (c (jf k) : ℤ) + 2 * (c (jt k) : ℤ) ∧
    p k ⟨⟨R k, ⟨Or.inl rfl, notsameR k⟩⟩, c⟩ = (if k then 0 else 1) +
      (c (jf k) : ZMod 2) + (c (jt k) : ZMod 2) := by
  classical
  have hu : (Finset.univ : Finset (MatchingStrand (A k) (R k))) = {jf k, jt k} := by
    ext j
    have hj := j.property
    simp only [endsR, List.mem_cons, List.not_mem_nil, or_false] at hj
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    cases k <;> rcases hj with hj | hj
    · exact Or.inl (Subtype.ext hj)
    · exact Or.inr (Subtype.ext hj)
    · exact Or.inr (Subtype.ext hj)
    · exact Or.inl (Subtype.ext hj)
  have hne : jf k ≠ jt k := by
    intro h
    have hh := congrArg Subtype.val h
    cases k <;> cases hh
  have cf : matchingStrandColour (A k) (R k) (jf k) = false := by cases k <;> rfl
  have ct : matchingStrandColour (A k) (R k) (jt k) = false := by cases k <;> rfl
  have h := mixed_decorated_degree_parity D sy 0 (hm k)
    (q k ⟨R k, ⟨Or.inl rfl, notsameR k⟩⟩) (fun j hj => (hq k _ j hj).2) c _
    (hτ k ⟨R k, ⟨Or.inl rfl, notsameR k⟩⟩ c)
  simp only [hu, Finset.sum_insert (show jf k ∉ ({jt k} : Finset _) by simpa using hne),
    Finset.sum_singleton,
    cf, ct, (base_values k).1, (base_values k).2] at h
  constructor
  · have hd := h.1
    change d k ⟨⟨R k, ⟨Or.inl rfl, notsameR k⟩⟩, c⟩ =
      0 + ((c (jf k) : ℤ) * 2 + (c (jt k) : ℤ) * 2) at hd
    linarith
  · simpa only [p, D, oddDatum, mul_one, add_assoc] using h.2

private def otherDot (k : Bool) : T k :=
  ⟨⟨R k, ⟨Or.inl rfl, notsameR k⟩⟩, fun j => if j.val = (jt k).val then 1 else 0⟩

private theorem oneDot_values (k : Bool) : d k (oneDot k) = 2 ∧
    p k (oneDot k) = if k then 1 else 0 := by
  have h := count_grading k (oneDot k).2
  cases k <;> norm_num [oneDot, jf, jt] at h ⊢ <;> exact h
private theorem otherDot_values (k : Bool) : d k (otherDot k) = 2 ∧
    p k (otherDot k) = if k then 1 else 0 := by
  have h := count_grading k (otherDot k).2
  cases k <;> norm_num [otherDot, jf, jt] at h ⊢ <;> exact h

private theorem fiber_two (k : Bool) : {t : T k | d k t = 2} = {oneDot k, otherDot k} := by
  ext t
  constructor
  · rcases t with ⟨⟨V, hV⟩, c⟩
    obtain rfl := Set.mem_singleton_iff.mp ((filteredM k) ▸ hV)
    intro hd
    have h := (count_grading k c).1
    change d k ⟨⟨R k, hV⟩, c⟩ = 2 at hd
    have hh : (c (jf k) = 1 ∧ c (jt k) = 0) ∨ (c (jf k) = 0 ∧ c (jt k) = 1) := by omega
    rcases hh with ⟨hf, ht⟩ | ⟨hf, ht⟩
    · have hc : c = (oneDot k).2 := by
        funext j
        have hj := j.property
        simp only [endsR, List.mem_cons, List.not_mem_nil, or_false] at hj
        cases k <;> rcases hj with hj | hj
        · have he : j = jf false := Subtype.ext hj
          rw [he, hf]; rfl
        · have he : j = jt false := Subtype.ext hj
          rw [he, ht]; rfl
        · have he : j = jt true := Subtype.ext hj
          rw [he, ht]; rfl
        · have he : j = jf true := Subtype.ext hj
          rw [he, hf]; rfl
      subst c
      exact Or.inl rfl
    · have hc : c = (otherDot k).2 := by
        funext j
        have hj := j.property
        simp only [endsR, List.mem_cons, List.not_mem_nil, or_false] at hj
        cases k <;> rcases hj with hj | hj
        · have he : j = jf false := Subtype.ext hj
          rw [he, hf]; rfl
        · have he : j = jt false := Subtype.ext hj
          rw [he, ht]; rfl
        · have he : j = jt true := Subtype.ext hj
          rw [he, ht]; rfl
        · have he : j = jf true := Subtype.ext hj
          rw [he, hf]; rfl
      subst c
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact (oneDot_values k).1
    · exact (otherDot_values k).1

private theorem dots_ne (k : Bool) : oneDot k ≠ otherDot k := by
  intro h
  have hc : (oneDot k).2 = (otherDot k).2 := by
    exact (Sigma.mk.inj h).2.eq
  have hj := congrFun hc (jf k)
  change (if (jf k).val = (jf k).val then 1 else 0) =
    (if (jf k).val = (jt k).val then 1 else 0) at hj
  cases k <;> norm_num [jf, jt] at hj

/-- Both intersection classes occur among the equal-colour representatives. -/
theorem intersection_cases : Ilv (pairing₂ (A true) (R true)) 2 ∧
    ¬ Ilv (pairing₂ (A false) (R false)) 2 :=
  ⟨BoundaryExchangeExamples.existing_intersection,
    BoundaryExchangeExamples.no_existing_intersection⟩

/-- Each degree-two source fiber consists of precisely the two one-dot labels.
The target coefficient is computed using the constructed exchange, not a form. -/
theorem populated_coefficient (k : Bool) (σ : ℚ) (hσ : σ ^ 2 = 1) :
    ∃ (hf : Set.Finite {t : T k | d k t = 2}) (hg : Set.Finite {u : U k | e k u = 2}),
      (∃ t, d k t = 2 ∧ ∃ j, t.2 j ≠ 0) ∧ (∃ u, e k u = 2) ∧
      (∑ t ∈ hf.toFinset, σ ^ (p k t).val) = 2 * σ ^ (if k then 1 else 0) ∧
      (∑ u ∈ hg.toFinset, σ ^ (p' k u).val) = σ * (2 * σ ^ (if k then 1 else 0)) := by
  classical
  obtain ⟨F, hF⟩ := equal_odd_families k
  obtain ⟨hf, hg, h⟩ := hF D sy 0
  change (∀ t, e k (F t) = d k t ∧ p' k (F t) = p k t + 1) ∧
    (∀ z, Nonempty ({t // d k t = z} ≃ {u // e k u = z})) ∧
    (∀ σ : ℚ, σ ^ 2 = 1 → ∀ z : ℤ,
      (∑ u ∈ (hg z).toFinset, σ ^ (p' k u).val) = σ ^ (1 : ZMod 2).val *
        ∑ t ∈ (hf z).toFinset, σ ^ (p k t).val ∧
      (∑ t ∈ (hf z).toFinset, σ ^ (p k t).val) = σ ^ (1 : ZMod 2).val *
        ∑ u ∈ (hg z).toFinset, σ ^ (p' k u).val) at h
  have hc : (∑ t ∈ (hf 2).toFinset, σ ^ (p k t).val) = 2 * σ ^ (if k then 1 else 0) := by
    have he : (hf 2).toFinset = {oneDot k, otherDot k} := by
      ext t
      rw [Set.Finite.mem_toFinset]
      change t ∈ {t : T k | d k t = 2} ↔ t ∈ ({oneDot k, otherDot k} : Finset (T k))
      rw [fiber_two]
      simp
    rw [he, Finset.sum_pair (dots_ne k), (oneDot_values k).2, (otherDot_values k).2]
    cases k <;> norm_num [show (1 : ZMod 2).val = 1 from rfl, two_mul]
  refine ⟨hf 2, hg 2, ⟨oneDot k, (oneDot_values k).1, jf k, ?_⟩,
    ⟨F (oneDot k), (h.1 _).1.trans (oneDot_values k).1⟩, hc, ?_⟩
  · simp [oneDot]
  · have ht := (h.2.2 σ hσ 2).1
    simpa only [show (1 : ZMod 2).val = 1 from rfl, pow_one, hc] using ht

/-- The two rational parity specializations distinguish the odd crossing sign
on nonempty degree fibers, in both intersection branches. -/
theorem both_signs (k : Bool) :
    (∃ (hf : Set.Finite {t : T k | d k t = 2}) (hg : Set.Finite {u : U k | e k u = 2}),
      (∑ t ∈ hf.toFinset, (1 : ℚ) ^ (p k t).val) = 2 ∧
      (∑ u ∈ hg.toFinset, (1 : ℚ) ^ (p' k u).val) = 2) ∧
    (∃ (hf : Set.Finite {t : T k | d k t = 2}) (hg : Set.Finite {u : U k | e k u = 2}),
      (∑ t ∈ hf.toFinset, (-1 : ℚ) ^ (p k t).val) = (if k then -2 else 2) ∧
      (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' k u).val) = (if k then 2 else -2)) := by
  obtain ⟨hf, hg, _, _, h1, h2⟩ := populated_coefficient k 1 (by norm_num)
  obtain ⟨hf', hg', _, _, h1', h2'⟩ := populated_coefficient k (-1) (by norm_num)
  constructor
  · exact ⟨hf, hg, by simpa using h1, by simpa using h2⟩
  · refine ⟨hf', hg', ?_, ?_⟩
    · cases k <;> simpa using h1'
    · cases k <;> simpa using h2'

end OddMath.SKM.NoncapFamilyCoefficientsExamples
