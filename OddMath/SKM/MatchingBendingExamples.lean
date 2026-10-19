import OddMath.SKM.MatchingBending

/-! One-strand boundary tests for both bending orientations, including an empty remaining word. -/

namespace OddMath.SKM.MatchingBendingExamples
open StringDiagrams.Chord

private theorem identity_matching {I : Type*} (x : Letter I) :
    IsMatching₂ [x] [x] [] := ⟨trivial, rfl⟩

private theorem identity_reduced {I : Type*} (x : Letter I) :
    StrictReduced₂ [x] [] := by
  exact ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩

private theorem cup_matching {I : Type*} (x : Letter I) :
    IsMatching₂ [] [flipL x, x] [.mv (.cup 0 (flipL x))] := by
  constructor
  · change 0 ≤ 0 ∧ True
    decide
  · change [flipL x, flipL (flipL x)] = [flipL x, x]
    rw [flipL_involutive x]

private theorem cup_reduced {I : Type*} (x : Letter I) :
    StrictReduced₂ [] [.mv (.cup 0 (flipL x))] := by
  exact ⟨⟨List.nodup_nil, by simp [tRun, tStep, tStart]⟩, List.nodup_singleton _⟩

private theorem same_two {I : Type*} {s : List (ℕ × Letter I)}
    (hv : Valid s) (hlen : s.length = 2) (i j : ℕ) :
    Same s i j ↔ i < 2 ∧ j < 2 ∧ i ≠ j := by
  constructor
  · intro h
    exact ⟨hlen ▸ h.lt_left, hlen ▸ h.lt_right, h.ne⟩
  · rintro ⟨hi, hj, hne⟩
    obtain ⟨k, hk, -⟩ := hv i (hlen ▸ hi)
    have hkl : k < 2 := hlen ▸ hk.lt_right
    have hkn := hk.ne
    have : k = j := by omega
    exact this ▸ hk

private theorem iso_two {I : Type*} {s t : List (ℕ × Letter I)}
    (hs : Valid s) (ht : Valid t) (hl : s.map Prod.snd = t.map Prod.snd)
    (hlen : s.length = 2) : Iso s t := by
  have hlen' : t.length = 2 := by
    have := congrArg List.length hl
    simp only [List.length_map] at this
    omega
  exact ⟨hl, fun i j => (same_two hs hlen i j).trans (same_two ht hlen' i j).symm⟩

/-- The full representative-family headline is inhabited by the identity and one cup.
Both letters of the cup have the same colour; the remaining lower word is empty. -/
theorem identity_cup_equiv {I : Type*} (x : Letter I) :
    ∃ E : {R : List (TMove (Letter I)) // R ∈ ({[]} : Set _)} ≃
        {S : List (TMove (Letter I)) // S ∈ ({[.mv (.cup 0 (flipL x))]} : Set _)},
      ∀ R, Iso (pairing₂ [] (E R).val) (pairing₂ [x] R.val) := by
  apply bending_representatives_equiv x [] [x] {[]} {[.mv (.cup 0 (flipL x))]}
  · intro R hR
    obtain rfl := Set.mem_singleton_iff.1 hR
    exact ⟨identity_matching x, identity_reduced x⟩
  · intro S hS
    obtain rfl := Set.mem_singleton_iff.1 hS
    exact ⟨cup_matching x, cup_reduced x⟩
  · intro R hR _
    refine ⟨[], Set.mem_singleton _, ?_⟩
    have hp := (identity_matching x).pairing_properties
    have hq := hR.pairing_properties
    apply iso_two hp.1 hq.1 (hp.2.2.trans hq.2.2.symm)
    rfl
  · intro R hR _
    refine ⟨[.mv (.cup 0 (flipL x))], Set.mem_singleton _, ?_⟩
    have hp := (cup_matching x).pairing_properties
    have hq := hR.pairing_properties
    apply iso_two hp.1 hq.1 (hp.2.2.trans hq.2.2.symm)
    rfl
  · intro R hR S hS _
    exact (Set.mem_singleton_iff.1 hR).trans (Set.mem_singleton_iff.1 hS).symm
  · intro R hR S hS _
    exact (Set.mem_singleton_iff.1 hR).trans (Set.mem_singleton_iff.1 hS).symm

-- Claim 2 orientation: up at the bottom becomes down at the top.
example : ∃ S : List (TMove (Letter Unit)), StrictReduced₂ [] S ∧
    XChain [] (tLay [] S) [(false, ()), (true, ())] ∧
    Iso (pairing₂ [] S) (pairing₂ [(true, ())] []) :=
  exists_bent_matching_layers (identity_matching (true, ()))

-- Claim 3 orientation: down at the bottom becomes up at the top.
example : ∃ S : List (TMove (Letter Unit)), StrictReduced₂ [] S ∧
    XChain [] (tLay [] S) [(true, ()), (false, ())] ∧
    Iso (pairing₂ [] S) (pairing₂ [(false, ())] []) :=
  exists_bent_matching_layers (identity_matching (false, ()))

end OddMath.SKM.MatchingBendingExamples
