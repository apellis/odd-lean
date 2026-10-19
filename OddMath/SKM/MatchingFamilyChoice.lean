/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.Claim5Coefficients

/-! # Choices of decorated matching families

Internal representative and distinguished-point choices of BE2, §8, needed
for the length and interchange induction in Theorem 10.3.
-/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove

private theorem prefix_id_transport {I : Type*} (n : ℕ)
    (R : List (TMove (Letter I))) (T : TState (Letter I))
    (hR : TFits flipL n T R) (j : ℕ) (hj : j < n) (hjt : j < T.st.length) :
    tRen n T R (idD T.st j) = idD (tRun flipL n T R).st j := by
  induction R generalizing T with
  | nil => rfl
  | cons m R ih =>
    have hm : (shiftT n m).Ok flipL 0 T.st := (ok_shift n T.st m).mp hR.1
    have hn : ¬ CapLeg (shiftT n m) j := by
      cases m with
      | mv m => simp [shiftT, CapLeg]
      | cap g => simp only [shiftT, CapLeg]; omega
    have hp : tPos (shiftT n m) j = j := by
      rcases m with (⟨g, a⟩ | p) | g
      · simp [shiftT, shiftM, tPos, movePos, show j < n + g by omega]
      · simp [shiftT, shiftM, tPos, movePos, Chord.tau,
          show j ≠ n + p by omega, show j ≠ n + p + 1 by omega]
      · simp [shiftT, tPos, show j < n + g by omega]
    have hs := idD_tStep hm hjt hn
    rw [hp, ← tStep_shift] at hs
    have hr : stepRen 0 T (shiftT n m) (idD T.st j) = stepRen n T m (idD T.st j) := by
      cases m <;> simp only [stepRen, shiftT, Nat.zero_add]
    rw [hr] at hs
    change tRen n (tStep flipL n T m) R (stepRen n T m (idD T.st j)) = _
    rw [← hs.2]
    exact ih _ hR.2 hs.1

/-- A bent lower endpoint determines a bounded point just above the bottom
boundary, with its strand identifier followed through every cap. -/
theorem onStrand₂_bottom {I : Type*} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R)
    {j : ℕ} (hj : j < a.length) :
    OnStrand₂ a R j (0, a.length - 1 - j) := by
  constructor
  · simpa using (show a.length - 1 - j < a.length by omega)
  · simp only [List.take_zero, List.drop_zero, tRun, List.foldl_nil]
    have hs := (tStart_mirror a).2 j hj
    have he : a.length + (a.length - 1 - j) = 2 * a.length - 1 - j := by omega
    rw [he]
    have hi : idD (tStart a).st (2 * a.length - 1 - j) = idD (tStart a).st j := by
      have hh := hs.2.2
      rw [idAt_eq_idD hs.lt_left, idAt_eq_idD hs.lt_right] at hh
      exact Option.some.inj hh.symm
    rw [hi]
    exact prefix_id_transport a.length R (tStart a) hR.1 j hj hs.lt_left

/-- Every strand admits a distinguished point at a boundary height. -/
theorem matching_bounded_points {I : Type*} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R) :
    ∃ q : ℕ → ℕ × ℕ, ∀ j ∈ leftEnds₂ a R,
      (q j).1 ≤ R.length ∧ OnStrand₂ a R j (q j) := by
  classical
  refine ⟨fun j => if j < a.length then (0, a.length - 1 - j)
    else (R.length, j - a.length), ?_⟩
  intro j hj
  have hjl := (mem_leftEnds₂.mp hj).1
  have hlen : (pairing₂ a R).length = a.length + b.length := by
    have h := congrArg List.length hR.pairing_properties.2.2
    simpa only [List.length_map, List.length_append, length_dualW] using h
  dsimp only
  split_ifs with h
  · exact ⟨Nat.zero_le _, onStrand₂_bottom hR h⟩
  · refine ⟨le_rfl, ?_, ?_⟩
    · simpa only [List.take_length, hR.2] using (show j - a.length < b.length by omega)
    · simp only [List.take_length, List.drop_length, tRen, id_eq]
      rw [Nat.add_sub_cancel' (by omega : a.length ≤ j)]
      rfl

/-- Choose exactly one strict representative of each realized pairing. -/
theorem exists_unique_matching_representatives {I : Type*} (a b : List (Letter I)) :
    ∃ M : Set (List (TMove (Letter I))),
      (∀ R ∈ M, IsMatching₂ a b R ∧ StrictReduced₂ a R) ∧
      (∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ a R) (pairing₂ a S) → R = S) ∧
      (∀ R, IsMatching₂ a b R → StrictReduced₂ a R →
        ∃ S ∈ M, Iso (pairing₂ a S) (pairing₂ a R)) := by
  classical
  let V := {R : List (TMove (Letter I)) // IsMatching₂ a b R ∧ StrictReduced₂ a R}
  let s : Setoid V :=
    { r := fun R S => Iso (pairing₂ a R.val) (pairing₂ a S.val)
      iseqv := ⟨fun _ => Iso.refl _, fun h => h.symm, fun h k => h.trans k⟩ }
  let f : Quotient s → List (TMove (Letter I)) := fun q => q.out.val
  refine ⟨Set.range f, ?_, ?_, ?_⟩
  · rintro R ⟨q, rfl⟩
    exact q.out.property
  · rintro R ⟨q, rfl⟩ S ⟨r, rfl⟩ h
    have he : q = r := by
      rw [← Quotient.out_eq q, ← Quotient.out_eq r]
      exact Quotient.sound h
    exact congrArg f he
  · intro R hR hr
    let v : V := ⟨R, hR, hr⟩
    let q : Quotient s := Quotient.mk s v
    refine ⟨f q, ⟨q, rfl⟩, ?_⟩
    exact Quotient.exact (Quotient.out_eq q)

/-- Complete source-shaped families for an empty upper boundary exist without
any root datum, sign, degree or auxiliary existence premise. -/
theorem exists_complete_coefficientFamily {I : Type*} (a : List (Letter I)) :
    ∃ F : CoefficientFamily a, F.Complete := by
  classical
  obtain ⟨M, hM, hu, hc⟩ := exists_unique_matching_representatives a []
  have hp (R : M) := matching_bounded_points (hM R R.property).1
  choose q hq using hp
  have hd (R : M) (c : MatchingStrand a R.val → ℕ) :=
    exists_decorates₂_of_bounded_points a R.val (q R)
      (fun j hj => (hq R j hj).2) (fun j hj => (hq R j hj).1) c
  choose τ hτ using hd
  exact ⟨⟨M, hM, hu, q, fun R j hj => (hq R j hj).2,
    τ, fun R c => (hτ R c).1⟩, hc⟩

end OddMath.SKM
