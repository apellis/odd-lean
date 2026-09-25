import OddMath.Frontier.TableauReverseWord

namespace OddMath.Frontier.TableauStripUniqueness
abbrev State (n : ℕ) := TableauWordInsertion.State n

def enumeration (ps qs : List (ℕ × ℕ)) : Prop :=
  ps.Pairwise (fun p q => q.2 < p.2) →
    qs.Pairwise (fun p q => q.2 < p.2) → ps.toFinset = qs.toFinset → ps = qs

def preimage (n : ℕ) (A B : State n) (u v : List (Fin n)) : Prop :=
  A.1 = B.1 → u.Sorted (· ≤ ·) → v.Sorted (· ≤ ·) →
    (TableauWordInsertion.run n A u).1 = (TableauWordInsertion.run n B v).1 →
      (A, u) = (B, v)

/-!
Fulton, Young Tableaux §1.1, printed p11 / frozen PDF23, lines791–799:
uniqueness of the inner tableau and weakly increasing inserted word.
The existing source-qualified weak-order transcription is preserved. English
zero-based cells; Fin n represents positive labels val+1. No existence assertion.
-/

theorem ordered_enumeration_unique (ps qs : List (ℕ × ℕ)) : enumeration ps qs := by
  classical
  unfold enumeration
  induction ps generalizing qs with
  | nil =>
    intro _ _ he
    cases qs with
    | nil => rfl
    | cons q qs =>
      have hm : q ∈ ([] : List (ℕ × ℕ)).toFinset :=
        he.symm ▸ List.mem_toFinset.mpr List.mem_cons_self
      simp at hm
  | cons p ps ih =>
    intro hp hq he
    cases qs with
    | nil => simp at he
    | cons q qs =>
      have hpm : p ∈ q :: qs := List.mem_toFinset.mp
        (he ▸ List.mem_toFinset.mpr List.mem_cons_self)
      have hqm : q ∈ p :: ps := List.mem_toFinset.mp
        (he.symm ▸ List.mem_toFinset.mpr List.mem_cons_self)
      have hp' := List.pairwise_cons.mp hp
      have hq' := List.pairwise_cons.mp hq
      have hpq : p = q := by
        rcases List.mem_cons.mp hpm with heq | hpt
        · exact heq
        · rcases List.mem_cons.mp hqm with heq | hqt
          · exact heq.symm
          · have h₁ := hp'.1 q hqt
            have h₂ := hq'.1 p hpt
            omega
      subst q
      have hnp : p ∉ ps := by
        intro h
        have := hp'.1 p h
        omega
      have hnq : p ∉ qs := by
        intro h
        have := hq'.1 p h
        omega
      have ht : ps.toFinset = qs.toFinset := by
        have hh := congrArg (fun s : Finset (ℕ × ℕ) => s.erase p) he
        simpa [hnp, hnq] using hh
      exact congrArg (List.cons p) (ih qs hp'.2 hq'.2 ht)

theorem weak_preimage_unique (n : ℕ) (A B : State n) (u v : List (Fin n)) :
    preimage n A B u v := by
  intro hshape hu hv hfinal
  have hp := (TableauWordInsertion.run_horizontal n A u hu).1
  have hq := (TableauWordInsertion.run_horizontal n B v hv).1
  have hset : (TableauWordInsertion.run n A u).2.toFinset =
      (TableauWordInsertion.run n B v).2.toFinset := by
    rw [(TableauWordInsertion.run_spec n A u).2.2.2,
      (TableauWordInsertion.run_spec n B v).2.2.2, hshape, hfinal]
  have hhistory : (TableauWordInsertion.run n A u).2.reverse =
      (TableauWordInsertion.run n B v).2.reverse :=
    ordered_enumeration_unique _ _ (by simpa only [List.pairwise_reverse] using hp)
      (by simpa only [List.pairwise_reverse] using hq) (by simpa using hset)
  have hA := TableauReverseWord.reverse_after_run n A u
  have hB := TableauReverseWord.reverse_after_run n B v
  unfold TableauReverseWord.afterRun at hA hB
  dsimp only at hA hB
  rw [hfinal, hhistory] at hA
  exact Option.some.inj (hA.symm.trans hB)

#print axioms ordered_enumeration_unique
#print axioms weak_preimage_unique
end OddMath.Frontier.TableauStripUniqueness
