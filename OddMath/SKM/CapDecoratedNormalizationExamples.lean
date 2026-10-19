/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.CapDecoratedNormalization
import OddMath.SKM.MixedCrossingLocalExamples

/-! Nonzero cap and surviving dots, independent bounded points, and both
orientations of the cap-class normalization in BE2 Theorem 10.3 Claim 5. -/
noncomputable section
namespace OddMath.SKM.CapDecoratedNormalizationExamples
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators
open MixedCrossingLocalExamples (oddDatum oddSymmetrizer)

private def a (k j : Bool) : List (Letter Bool) := if k then [(true, j)] else []
private def b (k j : Bool) : List (Letter Bool) := if k then [(false, j)] else []
private def A (ε k j : Bool) := a k j ++ (ε, false) :: (!ε, false) :: b k j
private def R (k : Bool) : List (TMove (Letter Bool)) :=
  if k then [.cap 1, .cap 0] else [.cap 0]
private def S (k : Bool) : List (TMove (Letter Bool)) := if k then [.cap 0] else []

private theorem matching (ε k j : Bool) : IsMatching₂ (A ε k j) [] (R k) := by
  cases ε <;> cases k
  · exact ⟨⟨⟨(2, (false, false)), (0, (true, false)),
      rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩
  · refine ⟨⟨?_, ?_⟩, rfl⟩
    · exact ⟨(4, (false, false)), (2, (true, false)), rfl, rfl, rfl, by decide⟩
    · exact ⟨⟨(6, (true, j)), (0, (false, j)), rfl, rfl, rfl,
        by change (6 : ℕ) ≠ 0; decide⟩, trivial⟩
  · exact ⟨⟨⟨(2, (true, false)), (0, (false, false)),
      rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩
  · refine ⟨⟨?_, ?_⟩, rfl⟩
    · exact ⟨(4, (true, false)), (2, (false, false)), rfl, rfl, rfl, by decide⟩
    · exact ⟨⟨(6, (true, j)), (0, (false, j)), rfl, rfl, rfl,
        by change (6 : ℕ) ≠ 0; decide⟩, trivial⟩

private theorem shorter_matching (k j : Bool) : IsMatching₂ (a k j ++ b k j) [] (S k) := by
  cases k
  · exact ⟨trivial, rfl⟩
  · exact ⟨⟨⟨(2, (true, j)), (0, (false, j)), rfl, rfl, rfl,
      by change (2 : ℕ) ≠ 0; decide⟩, trivial⟩, rfl⟩

private theorem reduced (ε k j : Bool) : Reduced₂ (A ε k j) (R k) := by
  cases k <;>
    change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag <;> simp

private theorem shorter_reduced (k j : Bool) : Reduced₂ (a k j ++ b k j) (S k) := by
  cases k <;>
    change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag <;> simp

private theorem cap (ε k j : Bool) :
    Same (pairing₂ (A ε k j) (R k)) (b k j).length ((b k j).length + 1) := by
  cases ε <;> cases k <;> cases j <;> unfold Same idAt <;> decide

private theorem deleted (ε k j : Bool) : Iso (pairing₂ (a k j ++ b k j) (S k))
    (rmAt (pairing₂ (A ε k j) (R k)) (b k j).length) := by
  have pair (u v : ℕ) (x y : Letter Bool) : Iso [(u, x), (u, y)] [(v, x), (v, y)] := by
    refine ⟨rfl, ?_⟩
    intro i j
    obtain _ | _ | i := i <;> obtain _ | _ | j := j <;> simp [Same, idAt]
  cases ε <;> cases k
  · exact Iso.refl _
  · exact pair _ _ _ _
  · exact Iso.refl _
  · exact pair _ _ _ _


private def q (k : Bool) (t : ℕ) : ℕ × ℕ :=
  if k then if t = 0 then (1, 0) else (0, 1) else (0, 0)
private def r (_ : ℕ) : ℕ × ℕ := (0, 1)

private theorem points (ε k j : Bool) (t : ℕ) (ht : t ∈ leftEnds₂ (A ε k j) (R k)) :
    (q k t).1 ≤ (R k).length ∧ OnStrand₂ (A ε k j) (R k) t (q k t) := by
  have h := mem_leftEnds₂.mp ht
  have hb := h.1
  cases k
  · change t < 2 at hb
    interval_cases t
    · cases ε <;> cases j <;> constructor
      all_goals first | decide | unfold OnStrand₂; decide
    · exact (h.2 ⟨0, by decide, (cap ε false j).symm⟩).elim
  · change t < 4 at hb
    interval_cases t
    · cases ε <;> cases j <;> constructor
      all_goals first | decide | unfold OnStrand₂; decide
    · cases ε <;> cases j <;> constructor
      all_goals first | decide | unfold OnStrand₂; decide
    · exact (h.2 ⟨1, by decide, (cap ε true j).symm⟩).elim
    · apply False.elim
      apply h.2
      refine ⟨0, by decide, ?_⟩
      cases ε <;> cases j <;> unfold Same idAt <;> decide

private theorem shorter_points (k j : Bool) (t : ℕ)
    (ht : t ∈ leftEnds₂ (a k j ++ b k j) (S k)) :
    (r t).1 ≤ (S k).length ∧ OnStrand₂ (a k j ++ b k j) (S k) t (r t) := by
  have h := mem_leftEnds₂.mp ht
  have hb := h.1
  cases k
  · change t < 0 at hb
    omega
  · change t < 2 at hb
    interval_cases t
    · cases j <;> constructor
      all_goals first | decide | unfold OnStrand₂; decide
    · apply False.elim
      apply h.2
      refine ⟨0, by decide, ?_⟩
      cases j <;> unfold Same idAt <;> decide

private def τ (ε k j : Bool) (c : MatchingStrand (A ε k j) (R k) → ℕ) :
    List (DTMove Bool) :=
  (exists_decorates₂_of_bounded_points (A ε k j) (R k) (q k)
    (fun t ht => (points ε k j t ht).2) (fun t ht => (points ε k j t ht).1) c).choose

private theorem τ_valid (ε k j : Bool) (c : MatchingStrand (A ε k j) (R k) → ℕ) :
    Decorates₂ (A ε k j) (R k) (q k) (strandCounts c) (τ ε k j c) :=
  (exists_decorates₂_of_bounded_points (A ε k j) (R k) (q k)
    (fun t ht => (points ε k j t ht).2) (fun t ht => (points ε k j t ht).1) c).choose_spec.1

private def υ (k j : Bool) (c : MatchingStrand (a k j ++ b k j) (S k) → ℕ) :
    List (DTMove Bool) :=
  (exists_decorates₂_of_bounded_points (a k j ++ b k j) (S k) r
    (fun t ht => (shorter_points k j t ht).2)
    (fun t ht => (shorter_points k j t ht).1) c).choose

private theorem υ_valid (k j : Bool) (c : MatchingStrand (a k j ++ b k j) (S k) → ℕ) :
    Decorates₂ (a k j ++ b k j) (S k) r (strandCounts c) (υ k j c) :=
  (exists_decorates₂_of_bounded_points (a k j ++ b k j) (S k) r
    (fun t ht => (shorter_points k j t ht).2)
    (fun t ht => (shorter_points k j t ht).1) c).choose_spec.1

private def L (ε k j : Bool) := capLabelEquiv
  (matching ε k j).pairing_properties.1 (cap ε k j) (deleted ε k j)
private def labels (ε k j : Bool) (n m : ℕ) : MatchingStrand (A ε k j) (R k) → ℕ :=
  (L ε k j).symm (n, fun _ => m)

/-- The cap and remaining labels are arbitrary independent naturals. The two
serializers were constructed separately from bounded geometric points. -/
theorem decorated_cap (ε k j : Bool) (n m : ℕ) :
    tableDegree oddDatum oddSymmetrizer 0 (dLay (A ε k j) (τ ε k j (labels ε k j n m))) =
      tableDegree oddDatum oddSymmetrizer 0 (dLay (a k j ++ b k j) (υ k j (fun _ => m))) +
        (1 + if !ε then oddDatum.h false (wt oddDatum 0 (b k j))
          else -oddDatum.h false (wt oddDatum 0 (b k j))) + 2 * n ∧
    xpar oddDatum 0 (dLay (A ε k j) (τ ε k j (labels ε k j n m))) =
      xpar oddDatum 0 (dLay (a k j ++ b k j) (υ k j (fun _ => m))) +
        cupPar oddDatum (wt oddDatum 0 (b k j)) (!ε, false) + n := by
  have he := (L ε k j).apply_symm_apply (n, fun _ => m)
  have hd := cap_normalized_decorated_degree_parity oddDatum oddSymmetrizer 0
    (a k j) (b k j) ε false (matching ε k j) (reduced ε k j)
    (shorter_matching k j) (shorter_reduced k j) (cap ε k j) (deleted ε k j)
    (q k) r (fun t ht => (points ε k j t ht).2)
    (fun t ht => (shorter_points k j t ht).2) (labels ε k j n m)
    (τ ε k j (labels ε k j n m)) (υ k j (fun _ => m)) (τ_valid _ _ _ _) (by
      change Decorates₂ _ _ _ (strandCounts (L ε k j ((L ε k j).symm (n, fun _ => m))).2) _
      rw [he]
      exact υ_valid k j _)
  change _ = _ + _ + _ * ((L ε k j ((L ε k j).symm (n, fun _ => m))).1 : ℤ) ∧
    _ = _ + _ + ((L ε k j ((L ε k j).symm (n, fun _ => m))).1 : ZMod 2) * _ at hd
  rw [he] at hd
  simpa only [A, oddSymmetrizer, Bool.false_eq_true, ↓reduceIte, one_mul,
    show oddDatum.parity false = 1 from rfl, mul_one] using hd

/-- The nonempty suffix changes the physical coroot coordinate, so it cannot
be replaced by the exterior weight in the cap factor. -/
theorem suffix_weight_shift : oddDatum.h false (0 : Bool → ℤ) = 0 ∧
    oddDatum.h false (wt oddDatum 0 (b true false)) = -2 := by
  norm_num [b, wt, sh, oddDatum, Datum.h, Datum.α,
    PositivePointGradingExamples.twoColourDatum]

private def shortStrand (j : Bool) : MatchingStrand (a true j ++ b true j) (S true) :=
  ⟨0, mem_leftEnds₂.mpr ⟨by change 0 < 2; decide, by simp⟩⟩

private theorem shortStrand_unique (j : Bool)
    (s : MatchingStrand (a true j ++ b true j) (S true)) : s = shortStrand j := by
  apply Subtype.ext
  have h := mem_leftEnds₂.mp s.property
  have hb := h.1
  change s.val < 2 at hb
  have hs : s.val ≠ 1 := by
    intro he
    apply h.2
    refine ⟨0, by omega, ?_⟩
    rw [he]
    cases j <;> unfold Same idAt <;> decide
  change s.val = 0
  omega

/-- Nonzero independent labels on the actual cap and remaining strand. -/
theorem nonzero_label_values (ε : Bool) :
    labels ε true false 2 3
      (capStrand (matching ε true false).pairing_properties.1 (cap ε true false)) = 2 ∧
    labels ε true false 2 3
      (capRemainingStrand (matching ε true false).pairing_properties.1
        (cap ε true false) (deleted ε true false) (shortStrand false)) = 3 ∧
    q true 0 ≠ r 0 := by
  refine ⟨capLabelEquiv_symm_cap _ _ _ _ _, capLabelEquiv_symm_remaining _ _ _ _ _ _, ?_⟩
  decide

private theorem shorter_values (m : ℕ) :
    tableDegree oddDatum oddSymmetrizer 0
      (dLay (a true false ++ b true false) (υ true false (fun _ => m))) = 1 + 2 * m ∧
    xpar oddDatum 0
      (dLay (a true false ++ b true false) (υ true false (fun _ => m))) = m := by
  classical
  have hs {V : Type} [AddCommMonoid V]
      (f : MatchingStrand (a true false ++ b true false) (S true) → V) :
      ∑ j, f j = f (shortStrand false) := by
    apply Finset.sum_eq_single (shortStrand false)
    · intro j _ hj
      exact (hj (shortStrand_unique false j)).elim
    · simp
  obtain ⟨hd, hp⟩ := mixed_decorated_degree_parity oddDatum oddSymmetrizer 0
    (shorter_matching true false) r (fun t ht => (shorter_points true false t ht).2)
    (fun _ => m) _ (υ_valid true false (fun _ => m))
  rw [hs] at hd hp
  change _ = (1 : ℤ) + m * (2 * 1) at hd
  change _ = (0 : ZMod 2) + m * 1 at hp
  exact ⟨by simpa only [mul_one, one_mul, mul_comm] using hd,
    by simpa only [zero_add, mul_one] using hp⟩

private theorem shorter_empty (m : ℕ) :
    tableDegree oddDatum oddSymmetrizer 0
      (dLay (a false false ++ b false false) (υ false false (fun _ => m))) = 0 ∧
    xpar oddDatum 0
      (dLay (a false false ++ b false false) (υ false false (fun _ => m))) = 0 := by
  let : IsEmpty (MatchingStrand (a false false ++ b false false) (S false)) := ⟨fun j => by
    have h := (mem_leftEnds₂.mp j.property).1
    change j.val < 0 at h
    omega⟩
  have h := mixed_decorated_degree_parity oddDatum oddSymmetrizer 0
    (shorter_matching false false) r (fun t ht => (shorter_points false false t ht).2)
    (fun _ => m) _ (υ_valid false false (fun _ => m))
  simpa only [Fintype.sum_empty, add_zero, a, b, S, Bool.false_eq_true, ↓reduceIte,
    List.nil_append, tLay, tableDegree, xpar, List.map_nil, List.sum_nil] using h

/-- Two cap dots and three surviving odd dots, at a shifted suffix weight.
EF and FE differ in both the cap degree and the cap parity. -/
theorem nonempty_values :
    tableDegree oddDatum oddSymmetrizer 0
      (dLay (A true true false) (τ true true false (labels true true false 2 3))) = 14 ∧
    xpar oddDatum 0
      (dLay (A true true false) (τ true true false (labels true true false 2 3))) = 1 ∧
    tableDegree oddDatum oddSymmetrizer 0
      (dLay (A false true false) (τ false true false (labels false true false 2 3))) = 10 ∧
    xpar oddDatum 0
      (dLay (A false true false) (τ false true false (labels false true false 2 3))) = 0 := by
  have h₁ := decorated_cap true true false 2 3
  have h₂ := decorated_cap false true false 2 3
  rw [(shorter_values 3).1, (shorter_values 3).2] at h₁ h₂
  norm_num [suffix_weight_shift.2, cupPar, ipar,
    show oddDatum.parity false = 1 from rfl] at h₁ h₂
  exact ⟨h₁.1, h₁.2, h₂.1, h₂.2⟩

/-- Empty contexts still have two cap dots, and no surviving strand. -/
theorem empty_values :
    tableDegree oddDatum oddSymmetrizer 0
      (dLay (A true false false) (τ true false false (labels true false false 2 0))) = 5 ∧
    xpar oddDatum 0
      (dLay (A true false false) (τ true false false (labels true false false 2 0))) = 0 ∧
    tableDegree oddDatum oddSymmetrizer 0
      (dLay (A false false false) (τ false false false (labels false false false 2 0))) = 5 ∧
    xpar oddDatum 0
      (dLay (A false false false) (τ false false false (labels false false false 2 0))) = 1 := by
  have h₁ := decorated_cap true false false 2 0
  have h₂ := decorated_cap false false false 2 0
  rw [(shorter_empty 0).1, (shorter_empty 0).2] at h₁ h₂
  norm_num [b, wt, cupPar, ipar, oddDatum, Datum.h] at h₁ h₂
  exact ⟨h₁.1, h₁.2, h₂.1, h₂.2⟩

private def M (k : Bool) : Set (List (TMove (Letter Bool))) := {R k}
private def N (k : Bool) : Set (List (TMove (Letter Bool))) := {S k}

private theorem reducedM (ε k : Bool) : StrictReduced₂ (A ε k true) (R k) := by
  cases k
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([2] : List ℕ).Nodup
    simp
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([4, 6] : List ℕ).Nodup
    simp

private theorem reducedN (k : Bool) : StrictReduced₂ (a k true ++ b k true) (S k) := by
  cases k
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([] : List ℕ).Nodup
    simp
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([2] : List ℕ).Nodup
    simp

private theorem same_letter {s : List (ℕ × Letter Bool)}
    (hl : Lettered flipL s) {i j : ℕ} (h : Same s i j) :
    (s[j]?).map Prod.snd = ((s[i]?).map Prod.snd).map flipL := by
  rcases lt_or_gt_of_ne h.ne with hij | hji
  · simpa only [Option.map_map] using hl i j h hij
  · have hh := congrArg (Option.map flipL) (hl j i h.symm hji)
    simpa only [Option.map_map, Function.comp_def, flipL_flipL] using hh.symm

private theorem iso_nodup_letters {s t : List (ℕ × Letter Bool)}
    (hs : Valid s) (ht : Valid t) (hls : Lettered flipL s) (hlt : Lettered flipL t)
    (he : s.map Prod.snd = t.map Prod.snd) (hn : (s.map Prod.snd).Nodup) : Iso s t := by
  have forward {u v : List (ℕ × Letter Bool)} (hv : Valid v)
      (hlu : Lettered flipL u) (hlv : Lettered flipL v)
      (he : u.map Prod.snd = v.map Prod.snd) (hn : (v.map Prod.snd).Nodup)
      (i j : ℕ) (h : Same u i j) : Same v i j := by
    have hlen : u.length = v.length := by simpa using congrArg List.length he
    obtain ⟨k, hk, _⟩ := hv i (hlen ▸ h.lt_left)
    have h1 := same_letter hlu h
    have h2 := same_letter hlv hk
    simp only [← List.getElem?_map] at h1 h2
    rw [he] at h1
    have hj := h.lt_right
    have hjk : j = k := (List.Nodup.getElem?_inj (by simp only [List.length_map]; omega) hn).mp
      (h1.trans h2.symm)
    exact hjk ▸ hk
  exact ⟨he, fun i j => ⟨forward ht hls hlt he (he ▸ hn) i j,
    forward hs hlt hls he.symm hn i j⟩⟩

private theorem hM (ε k : Bool) : ∀ V ∈ M k,
    IsMatching₂ (A ε k true) [] V ∧ StrictReduced₂ (A ε k true) V := by
  intro V hv
  obtain rfl := Set.mem_singleton_iff.mp hv
  exact ⟨matching ε k true, reducedM ε k⟩

private theorem hN (k : Bool) : ∀ V ∈ N k,
    IsMatching₂ (a k true ++ b k true) [] V ∧ StrictReduced₂ (a k true ++ b k true) V := by
  intro V hv
  obtain rfl := Set.mem_singleton_iff.mp hv
  exact ⟨shorter_matching k true, reducedN k⟩

private theorem hMrep (ε k : Bool) : ∀ V, IsMatching₂ (A ε k true) [] V →
    StrictReduced₂ (A ε k true) V →
    ∃ W ∈ M k, Iso (pairing₂ (A ε k true) W) (pairing₂ (A ε k true) V) := by
  intro V h _
  refine ⟨R k, Set.mem_singleton _, ?_⟩
  apply iso_nodup_letters (matching ε k true).pairing_properties.1 h.pairing_properties.1
    (matching ε k true).pairing_properties.2.1 h.pairing_properties.2.1
    ((matching ε k true).pairing_properties.2.2.trans h.pairing_properties.2.2.symm)
  rw [(matching ε k true).pairing_properties.2.2]
  cases ε <;> cases k <;> decide

private theorem hNrep (k : Bool) : ∀ V, IsMatching₂ (a k true ++ b k true) [] V →
    StrictReduced₂ (a k true ++ b k true) V →
    ∃ W ∈ N k, Iso (pairing₂ (a k true ++ b k true) W) (pairing₂ (a k true ++ b k true) V) := by
  intro V h _
  refine ⟨S k, Set.mem_singleton _, ?_⟩
  apply iso_nodup_letters (shorter_matching k true).pairing_properties.1 h.pairing_properties.1
    (shorter_matching k true).pairing_properties.2.1 h.pairing_properties.2.1
    ((shorter_matching k true).pairing_properties.2.2.trans h.pairing_properties.2.2.symm)
  rw [(shorter_matching k true).pairing_properties.2.2]
  cases k <;> decide

private def C (ε k : Bool) : Set (List (TMove (Letter Bool))) :=
  {V | V ∈ M k ∧ Same (pairing₂ (A ε k true) V) (b k true).length ((b k true).length + 1)}

private theorem family_points (ε k : Bool) (V : C ε k) (t : ℕ)
    (ht : t ∈ leftEnds₂ (A ε k true) V.val) :
    (q k t).1 ≤ V.val.length ∧ OnStrand₂ (A ε k true) V.val t (q k t) := by
  rcases V with ⟨V, hV, _⟩
  obtain rfl := Set.mem_singleton_iff.mp hV
  exact points ε k true t ht

private theorem shorter_family_points (k : Bool) (V : N k) (t : ℕ)
    (ht : t ∈ leftEnds₂ (a k true ++ b k true) V.val) :
    (r t).1 ≤ V.val.length ∧ OnStrand₂ (a k true ++ b k true) V.val t (r t) := by
  rcases V with ⟨V, hV⟩
  obtain rfl := Set.mem_singleton_iff.mp hV
  exact shorter_points k true t ht

private def φ (ε k : Bool) (V : C ε k) (c : MatchingStrand (A ε k true) V.val → ℕ) :
    List (DTMove Bool) :=
  (exists_decorates₂_of_bounded_points (A ε k true) V.val (q k)
    (fun t ht => (family_points ε k V t ht).2)
    (fun t ht => (family_points ε k V t ht).1) c).choose

private theorem φ_valid (ε k : Bool) (V : C ε k)
    (c : MatchingStrand (A ε k true) V.val → ℕ) :
    Decorates₂ (A ε k true) V.val (q k) (strandCounts c) (φ ε k V c) :=
  (exists_decorates₂_of_bounded_points (A ε k true) V.val (q k)
    (fun t ht => (family_points ε k V t ht).2)
    (fun t ht => (family_points ε k V t ht).1) c).choose_spec.1

private def ψ (k : Bool) (V : N k) (c : MatchingStrand (a k true ++ b k true) V.val → ℕ) :
    List (DTMove Bool) :=
  (exists_decorates₂_of_bounded_points (a k true ++ b k true) V.val r
    (fun t ht => (shorter_family_points k V t ht).2)
    (fun t ht => (shorter_family_points k V t ht).1) c).choose

private theorem ψ_valid (k : Bool) (V : N k)
    (c : MatchingStrand (a k true ++ b k true) V.val → ℕ) :
    Decorates₂ (a k true ++ b k true) V.val r (strandCounts c) (ψ k V c) :=
  (exists_decorates₂_of_bounded_points (a k true ++ b k true) V.val r
    (fun t ht => (shorter_family_points k V t ht).2)
    (fun t ht => (shorter_family_points k V t ht).1) c).choose_spec.1

/-- Complete unique strict singleton families, with a true-coloured survivor
when nonempty. This fixture is separate from the repeated-false-colour shifted
example above; no false singleton coverage claim is used. The source fiber
contains the preimage of two cap dots and three independently chosen shorter dots. -/
theorem family_fibres (ε k : Bool) :
    let J := Σ V : C ε k, MatchingStrand (A ε k true) V.val → ℕ
    let K := Σ V : N k, MatchingStrand (a k true ++ b k true) V.val → ℕ
    let d := fun t : J => tableDegree oddDatum oddSymmetrizer 0 (dLay (A ε k true) (φ ε k t.1 t.2))
    let e := fun u : K => tableDegree oddDatum oddSymmetrizer 0
      (dLay (a k true ++ b k true) (ψ k u.1 u.2))
    let δ := 1 + if !ε then oddDatum.h false (wt oddDatum 0 (b k true))
      else -oddDatum.h false (wt oddDatum 0 (b k true))
    ∃ F : J ≃ ℕ × K,
      (∀ t, d t = e (F t).2 + δ + 2 * (F t).1) ∧
      (∀ z : ℤ, Set.Finite {t | d t = z} ∧
        Set.Finite {u : ℕ × K | e u.2 + δ + 2 * u.1 = z} ∧
        ∃ G : {t // d t = z} ≃ {u : ℕ × K // e u.2 + δ + 2 * u.1 = z},
          ∀ t, (G t).val = F t.val) ∧
      ∃ t, F t = (2, ⟨⟨S k, rfl⟩, fun _ => 3⟩) ∧
        d t = e ⟨⟨S k, rfl⟩, fun _ => 3⟩ + δ + 4 := by
  obtain ⟨F, _, hF⟩ := cap_labelled_family_degree_fibres (X := Bool → ℤ)
    (hM ε k) (hN k) (fun _ => q k) (fun _ => r)
    (fun V t ht => (family_points ε k V t ht).2)
    (fun V t ht => (shorter_family_points k V t ht).2)
    (φ ε k) (ψ k) (φ_valid ε k) (ψ_valid k) (hMrep ε k) (hNrep k)
    (fun V hv W hw _ => (Set.mem_singleton_iff.mp hv).trans (Set.mem_singleton_iff.mp hw).symm)
    (fun V hv W hw _ => (Set.mem_singleton_iff.mp hv).trans (Set.mem_singleton_iff.mp hw).symm)
  have h := hF oddDatum oddSymmetrizer 0
  dsimp only at h ⊢
  simp only [show oddSymmetrizer.d false = 1 from rfl, mul_one, one_mul] at h
  refine ⟨F, fun t => (h.1 t).1, ?_, ?_⟩
  · intro z
    refine ⟨(h.2 z).1, (h.2 z).2.1, F.subtypeEquiv ?_, fun _ => rfl⟩
    intro t
    simp only [A, (h.1 t).1]
  · let u : ℕ × (Σ V : N k, MatchingStrand (a k true ++ b k true) V.val → ℕ) :=
      (2, ⟨⟨S k, rfl⟩, fun _ => 3⟩)
    refine ⟨F.symm u, F.apply_symm_apply u, ?_⟩
    have hd := (h.1 (F.symm u)).1
    rw [F.apply_symm_apply] at hd
    exact hd

end OddMath.SKM.CapDecoratedNormalizationExamples
