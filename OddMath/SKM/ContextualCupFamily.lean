import OddMath.SKM.CapStrands
import OddMath.SKM.Nondegeneracy

/-! Adjacent target cup classes with arbitrary source and target contexts. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
variable {I : Type*}

theorem cup_deleted_properties (a P Q : List (Letter I)) (ε : Bool) (i : I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ (ε, i) :: (!ε, i) :: Q) R)
    (hc : Same (pairing₂ a R) (a.length + P.length) (a.length + P.length + 1)) :
    Valid (rmAt (pairing₂ a R) (a.length + P.length)) ∧
    Lettered flipL (rmAt (pairing₂ a R) (a.length + P.length)) ∧
    (rmAt (pairing₂ a R) (a.length + P.length)).map Prod.snd = dualW a ++ (P ++ Q) := by
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  refine ⟨hv.rmAt hc, hl.rmAt hc.lt_right, ?_⟩
  rw [map_rmAt, hs]
  have hn : a.length + P.length = (dualW a ++ P).length := by simp [length_dualW]
  rw [hn, ← List.append_assoc]
  simpa only [List.append_assoc] using
    (show rmAt ((dualW a ++ P) ++ (ε, i) :: (!ε, i) :: Q) (dualW a ++ P).length =
      (dualW a ++ P) ++ Q by
        generalize dualW a ++ P = K
        simp [rmAt])

theorem exists_strictReduced_cup_delete (a P Q : List (Letter I)) (ε : Bool) (i : I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ (ε, i) :: (!ε, i) :: Q) R)
    (hc : Same (pairing₂ a R) (a.length + P.length) (a.length + P.length + 1)) :
    ∃ S, IsMatching₂ a (P ++ Q) S ∧ StrictReduced₂ a S ∧
      Iso (pairing₂ a S) (rmAt (pairing₂ a R) (a.length + P.length)) := by
  obtain ⟨hv, hl, hs⟩ := cup_deleted_properties a P Q ε i hR hc
  exact exists_strictReduced_matching hv hl hs

def cupInsertedPairing (a P : List (Letter I)) (ε : Bool) (i : I)
    (S : List (TMove (Letter I))) : List (ℕ × Letter I) :=
  let T := tRun flipL a.length (tStart a) S
  insAt T.st (a.length + P.length) (T.nxt, (ε, i)) (T.nxt, (!ε, i))

theorem cup_inserted_properties (a P Q : List (Letter I)) (ε : Bool) (i : I)
    {S : List (TMove (Letter I))} (hS : IsMatching₂ a (P ++ Q) S) :
    Valid (cupInsertedPairing a P ε i S) ∧
    Lettered flipL (cupInsertedPairing a P ε i S) ∧
    (cupInsertedPairing a P ε i S).map Prod.snd =
      dualW a ++ (P ++ (ε, i) :: (!ε, i) :: Q) ∧
    Same (cupInsertedPairing a P ε i S) (a.length + P.length) (a.length + P.length + 1) ∧
    rmAt (cupInsertedPairing a P ε i S) (a.length + P.length) = pairing₂ a S := by
  obtain ⟨hv, hl, hs⟩ := hS.pairing_properties
  have hb : a.length + P.length ≤ (pairing₂ a S).length := by
    have := congrArg List.length hs
    simp only [List.length_map, List.length_append, length_dualW] at this
    omega
  have hf := ((tInv_tStart a).run hS.1).fresh
  change (∀ x ∈ pairing₂ a S, x.1 < (tRun flipL a.length (tStart a) S).nxt) at hf
  have hn := fun x hx => (hf x hx).ne
  change Valid (insAt _ _ _ _) ∧ Lettered flipL (insAt _ _ _ _) ∧ _
  refine ⟨hv.insAt hb hn _ _, hl.insAt flipL_involutive hb hn (ε, i), ?_,
    (same_insAt_iff hb hn _ _).mpr (Or.inl ⟨rfl, rfl⟩), rmAt_insAt _ _ _ _ hb⟩
  change (insAt (pairing₂ a S) (a.length + P.length) _ _).map Prod.snd = _
  rw [map_insAt, hs]
  have he : a.length + P.length = (dualW a ++ P).length := by simp [length_dualW]
  rw [he, ← List.append_assoc]
  simp only [insAt, List.take_left, List.drop_left]
  exact List.append_assoc _ _ _

/-- Critical-point records always use previously allocated strand ids. -/
theorem tCrit_lt_nxt {T : TState (Letter I)} {cl : List ℕ} {R : List (TMove (Letter I))}
    {k : ℕ} (hT : TInv T) (hR : TFits flipL k T R) (hcl : ∀ c ∈ cl, c < T.nxt) :
    ∀ c ∈ tCrit flipL k T cl R, c < (tRun flipL k T R).nxt := by
  induction R generalizing T cl with
  | nil => exact hcl
  | cons m R ih =>
      apply ih (hT.step hR.1) hR.2
      intro c hc
      cases m with
      | mv m =>
          cases m with
          | cup g x =>
              simp only [critStep, List.mem_append, List.mem_singleton] at hc
              rcases hc with hc | rfl
              · exact Nat.lt_trans (hcl c hc) (Nat.lt_succ_self _)
              · exact Nat.lt_succ_self _
          | cross g => exact hcl c hc
      | cap g =>
          obtain ⟨A, B, hA, _, _, _⟩ := hR.1
          have ha : idD T.st (k + g) < T.nxt := by
            have hid : idAt T.st (k + g) = some A.1 := by simp [idAt, hA]
            have he : idD T.st (k + g) = A.1 := by simp [idD, hid]
            rw [he]
            exact hT.fresh A (List.mem_of_getElem? hA)
          simp only [critStep, List.mem_append, List.mem_singleton, List.mem_map] at hc
          rcases hc with ⟨z, hz, rfl⟩ | rfl
          · unfold rlId
            split_ifs
            · exact ha
            · exact hcl z hz
          · exact ha

/-- Appending a contextual cup preserves strict reducedness literally. -/
theorem strictReduced_append_cup {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a b R) (hr : StrictReduced₂ a R) (p : ℕ) (x : Letter I) :
    StrictReduced₂ a (R ++ [.mv (.cup p x)]) := by
  constructor
  · simpa only [Reduced₂, tRun_snoc', tStep] using hr.1
  · change (tCrit flipL a.length (tStart a) [] (R ++ [.mv (.cup p x)])).Nodup
    rw [tCrit_snoc]
    apply List.Nodup.append hr.2 (List.nodup_singleton _)
    intro c hc he
    rw [List.mem_singleton] at he
    have hlt := tCrit_lt_nxt (tInv_tStart a) hR.1 (by simp) c hc
    omega

/-- The terminal contextual cup realizes insertion without replacing the
residual representative. -/
theorem matching_append_cup (a P Q : List (Letter I)) (ε : Bool) (i : I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ Q) R) :
    IsMatching₂ a (P ++ (ε, i) :: (!ε, i) :: Q) (R ++ [.mv (.cup P.length (ε, i))]) := by
  constructor
  · apply (tFits_snoc _ _ _ _).mpr
    refine ⟨hR.1, ?_⟩
    change a.length + P.length ≤ (pairing₂ a R).length
    have he := congrArg List.length hR.pairing_properties.2.2
    simp only [List.length_map, List.length_append, length_dualW] at he
    omega
  · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, hR.2, tLet, chStep_cup]
    rfl

@[simp] theorem pairing_append_cup (a P : List (Letter I)) (ε : Bool) (i : I)
    (R : List (TMove (Letter I))) :
    pairing₂ a (R ++ [.mv (.cup P.length (ε, i))]) = cupInsertedPairing a P ε i R := by
  rw [pairing₂, tRun_snoc']
  rfl

end OddMath.SKM
