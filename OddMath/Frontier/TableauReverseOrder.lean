import OddMath.Frontier.TableauReverseWord
import OddMath.Frontier.TableauReversePair

namespace OddMath.Frontier.TableauReverseOrder
abbrev State (n : ℕ) := TableauWordInsertion.State n

def spec (n : ℕ) (S : State n) (ps : List (ℕ × ℕ)) : Prop :=
  ps.Pairwise (fun p q => q.2 < p.2) →
    ∀ Q, TableauReverseWord.reverseRun n S ps = some Q → Q.2.Sorted (· ≤ ·)

/-!
Fulton, Young Tableaux §1.1, printed p11 / frozen PDF23, lines794–799.
The actual recursive output is chronological: the current removed letter is
appended last. Adjacent recovered-letter inequalities bound the entire earlier
word by transitivity; no strip, positivity-of-alphabet, or totality premise.
-/

private theorem earlier_le (n : ℕ) (ps : List (ℕ × ℕ)) :
    ∀ (S : State n) (p : ℕ × ℕ) (hp : TableauCorner.IsCorner S.1 p),
    let R := TableauReverseOutput.remove n S.1 S.2.1 S.2.2 p hp
    let S' : State n := ⟨TableauCorner.eraseShape S.1 p hp, ⟨R.tableau,R.bounded⟩⟩
    (p :: ps).Pairwise (fun p q => q.2 < p.2) →
    ∀ Q, TableauReverseWord.reverseRun n S' ps = some Q →
    ∀ a ∈ Q.2, a ≤ R.letter := by
  classical
  induction ps with
  | nil =>
    intro S p hp R S' hps Q hQ a ha
    simp only [TableauReverseWord.reverseRun, Option.some.injEq] at hQ
    subst Q
    simp at ha
  | cons q qs ih =>
    intro S p hp R S' hps Q hQ
    by_cases hq : TableauCorner.IsCorner S'.1 q
    · let U := TableauReverseOutput.remove n S'.1 S'.2.1 S'.2.2 q hq
      let S'' : State n := ⟨TableauCorner.eraseShape S'.1 q hq, ⟨U.tableau,U.bounded⟩⟩
      simp only [TableauReverseWord.reverseRun, dif_pos hq] at hQ
      change (TableauReverseWord.reverseRun n S'' qs).map
        (fun P => (P.1,P.2 ++ [U.letter])) = some Q at hQ
      cases ht : TableauReverseWord.reverseRun n S'' qs with
      | none => simp [ht] at hQ
      | some P =>
        rw [ht] at hQ
        have he : (P.1,P.2 ++ [U.letter]) = Q := Option.some.inj hQ
        subst Q
        have htail := (List.pairwise_cons.mp hps).2
        have hcol : q.2 < p.2 := (List.pairwise_cons.mp hps).1 q (by simp)
        have hpair : U.letter ≤ R.letter :=
          TableauReversePair.remove_pair_order n S.1 S.2.1 S.2.2 p hp q hq hcol
        have hb := ih S' q hq htail P ht
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact le_trans (hb a ha) hpair
        · have heq : a = U.letter := List.mem_singleton.mp ha
          exact heq ▸ hpair
    · simp [TableauReverseWord.reverseRun, hq] at hQ

theorem reverse_order (n : ℕ) (S : State n) (ps : List (ℕ × ℕ)) : spec n S ps := by
  classical
  induction ps generalizing S with
  | nil =>
    intro hps Q hQ
    simp only [TableauReverseWord.reverseRun, Option.some.injEq] at hQ
    subst Q
    exact List.sorted_nil
  | cons p ps ih =>
    intro hps Q hQ
    by_cases hp : TableauCorner.IsCorner S.1 p
    · let R := TableauReverseOutput.remove n S.1 S.2.1 S.2.2 p hp
      let S' : State n := ⟨TableauCorner.eraseShape S.1 p hp, ⟨R.tableau,R.bounded⟩⟩
      simp only [TableauReverseWord.reverseRun, dif_pos hp] at hQ
      change (TableauReverseWord.reverseRun n S' ps).map
        (fun P => (P.1,P.2 ++ [R.letter])) = some Q at hQ
      cases ht : TableauReverseWord.reverseRun n S' ps with
      | none => simp [ht] at hQ
      | some P =>
        rw [ht] at hQ
        have he : (P.1,P.2 ++ [R.letter]) = Q := Option.some.inj hQ
        subst Q
        have hs := ih S' (List.pairwise_cons.mp hps).2 P ht
        have hb := earlier_le n ps S p hp hps P ht
        apply List.pairwise_append.mpr
        refine ⟨hs, by simp, ?_⟩
        intro a ha b hbmem
        have heq : b = R.letter := List.mem_singleton.mp hbmem
        exact heq ▸ hb a ha
    · simp [TableauReverseWord.reverseRun, hp] at hQ

end OddMath.Frontier.TableauReverseOrder
