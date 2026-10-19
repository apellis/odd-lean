import OddMath.SKM.PositiveDecoratedEnumeration

/-! Concrete canonical-family enumeration for empty boundaries and two repeated colours.
These instantiate the supporting enumeration for [BE2, arXiv:1701.04133v2,
Theorem 10.3, proof of Claim 1], with representative hypotheses proved. -/

namespace OddMath.SKM.PositiveDecoratedEnumerationExamples
open StringDiagrams.Chord

abbrev repeatedWord : List (Letter Unit) := [(true, ()), (true, ())]
abbrev repeatedFamily : Set (List (TMove (Letter Unit))) := {[], [.mv (.cross 0)]}

private theorem identity_matching : IsMatching₂ repeatedWord repeatedWord [] := ⟨trivial, rfl⟩
private theorem identity_reduced : StrictReduced₂ repeatedWord [] :=
  ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩

private theorem swap_matching :
    IsMatching₂ repeatedWord repeatedWord [.mv (.cross 0)] := by
  constructor
  · change 3 < 4 ∧ True
    decide
  · rfl

private theorem swap_reduced : StrictReduced₂ repeatedWord [.mv (.cross 0)] := by
  refine ⟨⟨List.nodup_singleton _, ?_⟩, List.nodup_nil⟩
  intro z hz
  change z ∈ [_] at hz
  obtain rfl := List.mem_singleton.mp hz
  change ¬ (s(2, 0) : Sym2 ℕ).IsDiag
  decide

private theorem family_matching : ∀ R ∈ repeatedFamily,
    IsMatching₂ repeatedWord repeatedWord R ∧ StrictReduced₂ repeatedWord R := by
  intro R hR
  rcases hR with rfl | hR
  · exact ⟨identity_matching, identity_reduced⟩
  · obtain rfl := Set.mem_singleton_iff.mp hR
    exact ⟨swap_matching, swap_reduced⟩

private theorem identity_pairs : ∀ r : Fin 2, Same (pairing₂ repeatedWord [])
    (2 - 1 - r.val) (2 + r.val) := by
  intro r
  fin_cases r <;> unfold Same <;> decide

private theorem swap_pairs : ∀ r : Fin 2,
    Same (pairing₂ repeatedWord [.mv (.cross 0)])
      (2 - 1 - r.val) (2 + ((Equiv.swap 0 1) r).val) := by
  intro r
  fin_cases r <;> unfold Same <;> decide

private theorem perm_two (e : Equiv.Perm (Fin 2)) :
    e = Equiv.refl _ ∨ e = Equiv.swap 0 1 := by
  have hn : e 0 ≠ e 1 := fun h => Fin.zero_ne_one (e.injective h)
  generalize h0 : e 0 = x
  generalize h1 : e 1 = y
  fin_cases x <;> fin_cases y
  · exact False.elim (hn (h0.trans h1.symm))
  · left
    ext r
    fin_cases r <;> simp [h0, h1]
  · right
    ext r
    fin_cases r <;> simp [h0, h1]
  · exact False.elim (hn (h0.trans h1.symm))

private theorem iso_of_positive_pairs {I : Type*} {n : ℕ} (a b : Fin n → I)
    {s t : List (ℕ × Letter I)} (hv : Valid s) (hv' : Valid t)
    (hs : s.map Prod.snd = dualW (List.ofFn fun r => (true, a r)) ++
      List.ofFn fun r => (true, b r))
    (ht : t.map Prod.snd = dualW (List.ofFn fun r => (true, a r)) ++
      List.ofFn fun r => (true, b r)) (e : Equiv.Perm (Fin n))
    (he : ∀ r, Same s (n - 1 - r.val) (n + (e r).val))
    (he' : ∀ r, Same t (n - 1 - r.val) (n + (e r).val)) : Iso s t := by
  have hlen : s.length = n + n := by
    have h := congrArg List.length hs
    simpa [length_dualW] using h
  have hlen' : t.length = n + n := by
    have h := congrArg List.length ht
    simpa [length_dualW] using h
  have partners (i : ℕ) (hi : i < n + n) : ∃ j, Same s i j ∧ Same t i j := by
    by_cases hin : i < n
    · let r : Fin n := ⟨n - 1 - i, by omega⟩
      have hr : n - 1 - r.val = i := by dsimp [r]; omega
      exact ⟨n + (e r).val, hr ▸ he r, hr ▸ he' r⟩
    · let r : Fin n := ⟨i - n, by omega⟩
      have hr : n + r.val = i := by dsimp [r]; omega
      refine ⟨n - 1 - (e.symm r).val, ?_, ?_⟩
      · simpa only [e.apply_symm_apply, hr] using (he (e.symm r)).symm
      · simpa only [e.apply_symm_apply, hr] using (he' (e.symm r)).symm
  refine ⟨hs.trans ht.symm, fun i j => ?_⟩
  constructor
  · intro h
    obtain ⟨k, hk, hk'⟩ := partners i (by simpa [hlen] using h.lt_left)
    exact (hv.unique hk h) ▸ hk'
  · intro h
    obtain ⟨k, hk, hk'⟩ := partners i (by simpa [hlen'] using h.lt_left)
    exact (hv'.unique hk' h) ▸ hk

private theorem family_coverage : ∀ R', IsMatching₂ repeatedWord repeatedWord R' →
    StrictReduced₂ repeatedWord R' →
    ∃ R ∈ repeatedFamily, Iso (pairing₂ repeatedWord R) (pairing₂ repeatedWord R') := by
  intro R' hR' _
  obtain ⟨hv, hl, hs⟩ := hR'.pairing_properties
  obtain ⟨e, he, _⟩ := positive_pairing_equiv (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) hv hl hs
  rcases perm_two e with rfl | rfl
  · refine ⟨[], by simp [repeatedFamily], ?_⟩
    exact iso_of_positive_pairs (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ())
      identity_matching.pairing_properties.1 hv identity_matching.pairing_properties.2.2 hs
      (Equiv.refl _) identity_pairs he.2
  · refine ⟨[.mv (.cross 0)], by simp [repeatedFamily], ?_⟩
    exact iso_of_positive_pairs (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ())
      swap_matching.pairing_properties.1 hv swap_matching.pairing_properties.2.2 hs
      (Equiv.swap 0 1) swap_pairs he.2

private theorem identity_not_iso_swap :
    ¬ Iso (pairing₂ repeatedWord []) (pairing₂ repeatedWord [.mv (.cross 0)]) := by
  intro h
  have hp := (h.2 1 2).1 (identity_pairs 0)
  have hn : ¬ Same (pairing₂ repeatedWord [.mv (.cross 0)]) 1 2 := by unfold Same; decide
  exact hn hp

private theorem family_unique : ∀ R ∈ repeatedFamily, ∀ S ∈ repeatedFamily,
    Iso (pairing₂ repeatedWord R) (pairing₂ repeatedWord S) → R = S := by
  intro R hR S hS h
  have hr : R = [] ∨ R = [.mv (.cross 0)] := by simpa [repeatedFamily] using hR
  have hs : S = [] ∨ S = [.mv (.cross 0)] := by simpa [repeatedFamily] using hS
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
  · rfl
  · exact False.elim (identity_not_iso_swap h)
  · exact False.elim (identity_not_iso_swap h.symm)
  · rfl

/-- Both matchings of two repeated colours, with all representative hypotheses proved. -/
theorem repeated_enumeration :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      Nonempty (({w : Equiv.Perm (Fin 2) // ∀ r, (fun _ => ()) r = (fun _ => ()) (w r)} ×
        (Fin 2 → ℕ)) ≃ {L // L ∈ decoratedFamily₂ repeatedWord repeatedFamily
          (fun R c => topDotMoves repeatedWord R (topPositionExtension repeatedFamily p R)
            (fun j => c j))}) := by
  obtain ⟨p, hp, E, hE, F, hF⟩ := positive_decorated_enumeration
    (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) repeatedFamily
    family_matching family_coverage family_unique
  exact ⟨p, hp, ⟨F⟩⟩

/-- Joint injectivity specializes to the two representatives of repeated colours. -/
theorem repeated_joint_injective
    (p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2) :
    Function.Injective (fun z : {R // R ∈ repeatedFamily} × (Fin 2 → ℕ) =>
      dLay repeatedWord (topDotMoves repeatedWord z.1.val
        (fun j => (p z.1 j).val) (fun j => z.2 (p z.1 j)))) :=
  positive_topDotMoves_joint_injective (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ())
    repeatedFamily family_matching p

/-- Nonuniform top counts separate both different matchings and different decorations. -/
theorem repeated_decorations_distinct :
    ∃ p : ∀ R : {R // R ∈ repeatedFamily}, MatchingStrand repeatedWord R.val ≃ Fin 2,
      (∀ R (j : MatchingStrand repeatedWord R.val),
        OnStrand₂ repeatedWord R.val j.val (R.val.length, (p R j).val)) ∧
      let f := fun z : {R // R ∈ repeatedFamily} × (Fin 2 → ℕ) =>
        dLay repeatedWord (topDotMoves repeatedWord z.1.val
          (fun j => (p z.1 j).val) (fun j => z.2 (p z.1 j)))
      let R : {R // R ∈ repeatedFamily} := ⟨[], by simp [repeatedFamily]⟩
      let S : {R // R ∈ repeatedFamily} := ⟨[.mv (.cross 0)], by simp [repeatedFamily]⟩
      f (R, ![1, 2]) ≠ f (S, ![1, 2]) ∧ f (S, ![1, 2]) ≠ f (S, ![2, 1]) := by
  obtain ⟨p, hp, _⟩ := repeated_enumeration
  refine ⟨p, hp, ?_, ?_⟩
  · intro h
    have he := repeated_joint_injective p h
    have hr := congrArg (fun z => z.1.val) he
    cases hr
  · intro h
    have he := repeated_joint_injective p h
    have hc := congrArg (fun z => z.2 0) he
    norm_num at hc

/-- The empty colour type and empty boundaries need no default position. -/
theorem empty_enumeration :
    ∃ p : ∀ R : {R : List (TMove (Letter Empty)) // R ∈ ({[]} : Set _)},
        MatchingStrand [] R.val ≃ Fin 0,
      Nonempty (({w : Equiv.Perm (Fin 0) // ∀ r, (Fin.elim0 r : Empty) = Fin.elim0 (w r)} ×
        (Fin 0 → ℕ)) ≃ {L // L ∈ decoratedFamily₂ [] ({[]} : Set _)
          (fun R c => topDotMoves [] R (topPositionExtension {[]} p R) (fun j => c j))}) := by
  let a : Fin 0 → Empty := Fin.elim0
  have hm : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, a r)) [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ (List.ofFn fun r => (true, a r)) [] :=
    ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  obtain ⟨p, hp, E, hE, F, hF⟩ := positive_decorated_enumeration a a {[]}
    (by intro R hR; obtain rfl := Set.mem_singleton_iff.mp hR; exact ⟨hm, hr⟩)
    (by
      intro R hR _
      refine ⟨[], Set.mem_singleton _, ?_⟩
      exact iso_of_positive_pairs a a hm.pairing_properties.1 hR.pairing_properties.1
        hm.pairing_properties.2.2 hR.pairing_properties.2.2 (Equiv.refl _)
        (fun r => Fin.elim0 r) (fun r => Fin.elim0 r))
    (by
      intro R hR S hS _
      exact (Set.mem_singleton_iff.mp hR).trans (Set.mem_singleton_iff.mp hS).symm)
  exact ⟨p, ⟨F⟩⟩

end OddMath.SKM.PositiveDecoratedEnumerationExamples
