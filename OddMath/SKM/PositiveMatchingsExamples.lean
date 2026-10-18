import OddMath.SKM.PositiveMatchings

/-! Boundary cases and finite consequences of the positive-pairing classification. -/

open OddMath.SKM StringDiagrams.Chord

-- Empty boundaries are included, even for an empty colour type.
example : ∃! e : Fin 0 ≃ Fin 0,
    (∀ r, (Fin.elim0 r : Empty) = Fin.elim0 (e r)) ∧
      ∀ r, Same ([] : List (ℕ × Letter Empty)) (0 - 1 - r.val) (0 + (e r).val) := by
  apply positive_pairing_equiv (fun r => Fin.elim0 r) (fun r => Fin.elim0 r)
  · intro i hi; simp at hi
  · intro i j h; have := h.lt_left; simp at this
  · simp [dualW]

-- Repeated colours permit a nontrivial permutation.
example : ∃ s : List (ℕ × Letter Unit), Valid s ∧ Lettered flipL s ∧
    s.map Prod.snd = dualW (List.ofFn fun _ : Fin 2 => (true, ())) ++
      List.ofFn (fun _ : Fin 2 => (true, ())) ∧
    ∀ r : Fin 2, Same s (2 - 1 - r.val) (2 + ((Equiv.swap 0 1) r).val) :=
  exists_positive_pairing (fun _ => ()) (fun _ => ()) (Equiv.swap 0 1) (fun _ => rfl)

example {I : Type*} {c d : ℕ} (a : Fin c → I) (b : Fin d → I) (h : c ≠ d)
    (R : List (TMove (Letter I))) :
    ¬ IsMatching₂ (List.ofFn fun r => (true, a r)) (List.ofFn fun r => (true, b r)) R :=
  fun hR => h (hR.positive_length_eq a b)

section Representatives
variable {I : Type*} {n : ℕ} (a b : Fin n → I)
    (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R ∧
      StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (hrep : ∀ R', IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R' →
      StrictReduced₂ (List.ofFn fun r => (true, a r)) R' →
      ∃ R ∈ M, Iso (pairing₂ (List.ofFn fun r => (true, a r)) R)
        (pairing₂ (List.ofFn fun r => (true, a r)) R'))
    (huniq : ∀ R ∈ M, ∀ S ∈ M,
      Iso (pairing₂ (List.ofFn fun r => (true, a r)) R)
        (pairing₂ (List.ofFn fun r => (true, a r)) S) → R = S)

-- Finiteness is a consequence, not a hypothesis on M.
example : Finite {R // R ∈ M} := by
  obtain ⟨E, -⟩ := positive_representatives_equiv a b M hM hrep huniq
  exact Finite.of_injective E E.injective

-- The equivalence records the actual strand endpoints in pairing₂.
example (R : {R // R ∈ M}) : ∃ w : Equiv.Perm (Fin n),
    (∀ r, a r = b (w r)) ∧ ∀ r,
      Same (pairing₂ (List.ofFn fun r => (true, a r)) R.val)
        (n - 1 - r.val) (n + (w r).val) := by
  obtain ⟨E, hE⟩ := positive_representatives_equiv a b M hM hrep huniq
  exact ⟨(E R).val, (E R).property, hE R⟩
end Representatives
