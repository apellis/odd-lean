/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.CapStrands

/-! Cap strand consumers, in both orientations and with empty or nonempty
shorter boundaries. -/
noncomputable section
namespace OddMath.SKM.CapStrandsExamples
open StringDiagrams StringDiagrams.Chord

private def a (k : Bool) : List (Letter Bool) := if k then [(true, true)] else []
private def b (k : Bool) : List (Letter Bool) := if k then [(false, true)] else []
private def A (ε k : Bool) := a k ++ (ε, false) :: (!ε, false) :: b k
private def R (k : Bool) : List (TMove (Letter Bool)) :=
  if k then [.cap 1, .cap 0] else [.cap 0]
private def S (k : Bool) : List (TMove (Letter Bool)) := if k then [.cap 0] else []
private theorem hm (ε k : Bool) : IsMatching₂ (A ε k) [] (R k) := by
  cases ε <;> cases k
  · exact ⟨⟨⟨(2, (false, false)), (0, (true, false)),
      rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩
  · refine ⟨⟨?_, ?_⟩, rfl⟩
    · exact ⟨(4, (false, false)), (2, (true, false)), rfl, rfl, rfl, by decide⟩
    · exact ⟨⟨(6, (true, true)), (0, (false, true)), rfl, rfl, rfl, by decide⟩, trivial⟩
  · exact ⟨⟨⟨(2, (true, false)), (0, (false, false)),
      rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩
  · refine ⟨⟨?_, ?_⟩, rfl⟩
    · exact ⟨(4, (true, false)), (2, (false, false)), rfl, rfl, rfl, by decide⟩
    · exact ⟨⟨(6, (true, true)), (0, (false, true)), rfl, rfl, rfl, by decide⟩, trivial⟩

private theorem hn (k : Bool) : IsMatching₂ (a k ++ b k) [] (S k) := by
  cases k
  · exact ⟨trivial, rfl⟩
  · exact ⟨⟨⟨(2, (true, true)), (0, (false, true)), rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩

private theorem cap (ε k : Bool) :
    Same (pairing₂ (A ε k) (R k)) (b k).length ((b k).length + 1) := by
  cases ε <;> cases k <;> unfold Same idAt <;> decide


private theorem pair_iso {α : Type*} (m n : ℕ) (x y : α) :
    Iso [(m, x), (m, y)] [(n, x), (n, y)] := by
  refine ⟨rfl, fun i j => ?_⟩
  rcases i with _ | ⟨_ | i⟩ <;> rcases j with _ | ⟨_ | j⟩ <;>
    simp [Same, idAt]

private theorem pairingIso (ε k : Bool) :
    Iso (pairing₂ (a k ++ b k) (S k))
      (rmAt (pairing₂ (A ε k) (R k)) (b k).length) := by
  cases k
  · exact ⟨rfl, fun _ _ => Iff.rfl⟩
  · exact pair_iso 2 6 (true, true) (false, true)

private def E (ε k : Bool) :
    MatchingStrand (A ε k) (R k) ≃ Unit ⊕ MatchingStrand (a k ++ b k) (S k) :=
  matchingStrandEquivOfCap (hm ε k).pairing_properties.1 (cap ε k) (pairingIso ε k)

/-- Deleting either cap orientation has both strand roundtrips, including when
an additional differently coloured strand remains. -/
theorem strand_roundtrips (ε k : Bool) (j : MatchingStrand (A ε k) (R k))
    (z : Unit ⊕ MatchingStrand (a k ++ b k) (S k)) :
    (E ε k).symm (E ε k j) = j ∧ E ε k ((E ε k).symm z) = z :=
  ⟨(E ε k).symm_apply_apply j, (E ε k).apply_symm_apply z⟩

/-- The removed cap is false-coloured; every remaining strand keeps its colour. -/
theorem strand_colours (ε k : Bool) :
    matchingStrandColour (A ε k) (R k) ((E ε k).symm (Sum.inl ())) = false ∧
    ∀ j, matchingStrandColour (A ε k) (R k) ((E ε k).symm (Sum.inr j)) =
      matchingStrandColour (a k ++ b k) (S k) j :=
  ⟨matchingStrandColour_cap (a k) (b k) ε false (hm ε k) (cap ε k),
    matchingStrandColour_capRemaining (hm ε k).pairing_properties.1
      (cap ε k) (pairingIso ε k)⟩

private def L (ε k : Bool) :
    (MatchingStrand (A ε k) (R k) → ℕ) ≃ ℕ × (MatchingStrand (a k ++ b k) (S k) → ℕ) :=
  capLabelEquiv (hm ε k).pairing_properties.1 (cap ε k) (pairingIso ε k)

/-- Arbitrary natural labels, not just zero counts, have both roundtrips. -/
theorem label_roundtrips (ε k : Bool) (c : MatchingStrand (A ε k) (R k) → ℕ)
    (n : ℕ) (d : MatchingStrand (a k ++ b k) (S k) → ℕ) :
    (L ε k).symm (L ε k c) = c ∧ L ε k ((L ε k).symm (n, d)) = (n, d) :=
  ⟨(L ε k).symm_apply_apply c, (L ε k).apply_symm_apply (n, d)⟩

/-- Independent cap and remainder counts are recovered at their actual strands. -/
theorem label_values (ε k : Bool) (n m : ℕ) :
    (L ε k).symm (n, fun _ => m) ((E ε k).symm (Sum.inl ())) = n ∧
    ∀ j, (L ε k).symm (n, fun _ => m) ((E ε k).symm (Sum.inr j)) = m :=
  ⟨capLabelEquiv_symm_cap _ _ _ _ _, fun j => capLabelEquiv_symm_remaining _ _ _ _ _ j⟩

/-- The nonempty shorter boundary has a true-coloured strand carrying an
independent arbitrary count, distinct from the false-coloured cap count. -/
theorem nonempty_labels (ε : Bool) (n m : ℕ) :
    ∃ j : MatchingStrand (a true ++ b true) (S true),
      matchingStrandColour (a true ++ b true) (S true) j = true ∧
      (L ε true).symm (n, fun _ => m) ((E ε true).symm (Sum.inr j)) = m ∧
      (L ε true).symm (n, fun _ => m) ((E ε true).symm (Sum.inl ())) = n := by
  let j : MatchingStrand (a true ++ b true) (S true) := ⟨0, by
    apply mem_leftEnds₂.mpr
    refine ⟨by decide, ?_⟩
    simp⟩
  exact ⟨j, rfl, (label_values ε true n m).2 j, (label_values ε true n m).1⟩

/-- With empty shorter boundary only the cap count remains. -/
theorem empty_labels (ε : Bool) (n : ℕ) :
    IsEmpty (MatchingStrand (a false ++ b false) (S false)) ∧
      (L ε false).symm (n, fun _ => 0) ((E ε false).symm (Sum.inl ())) = n := by
  refine ⟨⟨fun j => ?_⟩, (label_values ε false n 0).1⟩
  have hj := (mem_leftEnds₂.mp j.property).1
  change j.val < 0 at hj
  omega

private def M (k : Bool) : Set (List (TMove (Letter Bool))) := {R k}
private def N (k : Bool) : Set (List (TMove (Letter Bool))) := {S k}

private theorem reducedM (ε k : Bool) : StrictReduced₂ (A ε k) (R k) := by
  cases k
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([2] : List ℕ).Nodup
    simp
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([4, 6] : List ℕ).Nodup
    simp

private theorem reducedN (k : Bool) : StrictReduced₂ (a k ++ b k) (S k) := by
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
    IsMatching₂ (A ε k) [] V ∧ StrictReduced₂ (A ε k) V := by
  intro V hv
  obtain rfl := Set.mem_singleton_iff.mp hv
  exact ⟨hm ε k, reducedM ε k⟩

private theorem hN (k : Bool) : ∀ V ∈ N k,
    IsMatching₂ (a k ++ b k) [] V ∧ StrictReduced₂ (a k ++ b k) V := by
  intro V hv
  obtain rfl := Set.mem_singleton_iff.mp hv
  exact ⟨hn k, reducedN k⟩

private theorem hMrep (ε k : Bool) : ∀ V, IsMatching₂ (A ε k) [] V →
    StrictReduced₂ (A ε k) V → ∃ W ∈ M k, Iso (pairing₂ (A ε k) W) (pairing₂ (A ε k) V) := by
  intro V h _
  refine ⟨R k, Set.mem_singleton _, ?_⟩
  apply iso_nodup_letters (hm ε k).pairing_properties.1 h.pairing_properties.1
    (hm ε k).pairing_properties.2.1 h.pairing_properties.2.1
    ((hm ε k).pairing_properties.2.2.trans h.pairing_properties.2.2.symm)
  rw [(hm ε k).pairing_properties.2.2]
  cases ε <;> cases k <;> decide

private theorem hNrep (k : Bool) : ∀ V, IsMatching₂ (a k ++ b k) [] V →
    StrictReduced₂ (a k ++ b k) V →
    ∃ W ∈ N k, Iso (pairing₂ (a k ++ b k) W) (pairing₂ (a k ++ b k) V) := by
  intro V h _
  refine ⟨S k, Set.mem_singleton _, ?_⟩
  apply iso_nodup_letters (hn k).pairing_properties.1 h.pairing_properties.1
    (hn k).pairing_properties.2.1 h.pairing_properties.2.1
    ((hn k).pairing_properties.2.2.trans h.pairing_properties.2.2.symm)
  rw [(hn k).pairing_properties.2.2]
  cases k <;> decide

/-- The complete singleton families instantiate the constructed family theorem;
all matching, strictness, completeness and uniqueness premises are proved. -/
theorem labelled_family (ε k : Bool) :
    ∃ F : (Σ V : {V // V ∈ M k ∧
        Same (pairing₂ (A ε k) V) (b k).length ((b k).length + 1)},
          MatchingStrand (A ε k) V.val → ℕ) ≃
        ℕ × (Σ W : {W // W ∈ N k}, MatchingStrand (a k ++ b k) W.val → ℕ),
      ∀ V c, (F ⟨V, c⟩).1 =
        c (capStrand (hM ε k V V.property.1).1.pairing_properties.1 V.property.2) :=
  cap_labelled_representatives_equiv (a k) (b k) ε false (M k) (N k)
    (hM ε k) (hN k) (hMrep ε k) (hNrep k)
    (fun _ hV _ hW _ =>
      (Set.mem_singleton_iff.mp hV).trans (Set.mem_singleton_iff.mp hW).symm)
    (fun _ hV _ hW _ =>
      (Set.mem_singleton_iff.mp hV).trans (Set.mem_singleton_iff.mp hW).symm)

end OddMath.SKM.CapStrandsExamples
