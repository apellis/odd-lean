import OddMath.Frontier.TableauWordInsertion
import OddMath.Frontier.TableauStripCorners
import OddMath.Frontier.TableauInsertionInverse

namespace OddMath.Frontier.TableauReverseWord
open OddMath.Frontier
abbrev State (n : ℕ) := TableauWordInsertion.State n

noncomputable def reverseRun (n : ℕ) :
    State n → List (ℕ × ℕ) → Option (State n × List (Fin n))
  | S, [] => some (S, [])
  | S, p :: ps => by
    classical
    exact if hp : TableauCorner.IsCorner S.1 p then
      let R := TableauReverseOutput.remove n S.1 S.2.1 S.2.2 p hp
      let S' : State n := ⟨TableauCorner.eraseShape S.1 p hp, ⟨R.tableau, R.bounded⟩⟩
      (reverseRun n S' ps).map (fun Q => (Q.1, Q.2 ++ [R.letter]))
    else none

def spec (n : ℕ) (S : State n) (ps : List (ℕ × ℕ)) : Prop :=
  ∀ Q, reverseRun n S ps = some Q →
    Q.2.length = ps.length ∧ Q.1.1.cells ⊆ S.1.cells ∧ ps.Nodup ∧
      ps.toFinset = S.1.cells \ Q.1.1.cells ∧
      TableauWordInsertion.run n Q.1 Q.2 = (S, ps.reverse)

def ofPeels (n : ℕ) (μ : YoungDiagram) (S : State n)
    (ps : List (ℕ × ℕ)) : Prop :=
  TableauStripCorners.PeelsTo μ S.1 ps →
    ∃ Q, reverseRun n S ps = some Q ∧ Q.1.1 = μ

def afterRun (n : ℕ) (S : State n) (w : List (Fin n)) : Prop :=
  let R := TableauWordInsertion.run n S w
  reverseRun n R.1 R.2.reverse = some (S, w)

/-!
Fulton, Young Tableaux §1.1, printed p11 / frozen PDF23, lines785–802:
reverse bumps return the inserted letters last-to-first. Here the list is
reversed back to chronological order, for arbitrary words and deletion lists.
No horizontal-strip or recovered-letter order assertion is used or made.
-/

private theorem run_append (n : ℕ) (S : State n) (u v : List (Fin n)) :
    TableauWordInsertion.run n S (u ++ v) =
      let P := TableauWordInsertion.run n S u
      let Q := TableauWordInsertion.run n P.1 v
      (Q.1, P.2 ++ Q.2) := by
  induction u generalizing S with
  | nil => simp [TableauWordInsertion.run]
  | cons a u ih => simp [TableauWordInsertion.run, ih]

private theorem reconstruct (n : ℕ) (S : State n) (ps : List (ℕ × ℕ)) :
    ∀ Q, reverseRun n S ps = some Q →
      TableauWordInsertion.run n Q.1 Q.2 = (S, ps.reverse) := by
  classical
  induction ps generalizing S with
  | nil =>
    intro Q h
    simp only [reverseRun, Option.some.injEq] at h
    subst Q
    rfl
  | cons p ps ih =>
    intro Q h
    by_cases hp : TableauCorner.IsCorner S.1 p
    · let R := TableauReverseOutput.remove n S.1 S.2.1 S.2.2 p hp
      let S' : State n := ⟨TableauCorner.eraseShape S.1 p hp, ⟨R.tableau,R.bounded⟩⟩
      simp only [reverseRun, dif_pos hp] at h
      change (reverseRun n S' ps).map (fun P => (P.1,P.2 ++ [R.letter])) = some Q at h
      cases ht : reverseRun n S' ps with
      | none => simp [ht] at h
      | some P =>
        rw [ht] at h
        have he : (P.1,P.2 ++ [R.letter]) = Q := Option.some.inj h
        subst Q
        have hf := ih S' P ht
        have hi := TableauInsertionInverse.insert_after_remove n S.1 S.2.1 S.2.2 p hp
        rw [run_append, hf]
        simp only [TableauWordInsertion.run, List.append_nil]
        rw [hi.1, hi.2.1]
        simp only [List.reverse_cons]
    · simp [reverseRun, hp] at h

theorem reverse_spec (n : ℕ) (S : State n) (ps : List (ℕ × ℕ)) : spec n S ps := by
  intro Q h
  have hf := reconstruct n S ps Q h
  have hs := TableauWordInsertion.run_spec n Q.1 Q.2
  unfold TableauWordInsertion.spec at hs
  rw [hf] at hs
  dsimp only at hs
  exact ⟨by simpa using hs.1.symm, hs.2.2.1, by simpa using hs.2.1,
    by simpa using hs.2.2.2, hf⟩

theorem reverse_of_peels (n : ℕ) (μ : YoungDiagram) (S : State n)
    (ps : List (ℕ × ℕ)) : ofPeels n μ S ps := by
  classical
  induction ps generalizing S with
  | nil =>
    intro h
    exact ⟨(S,[]), rfl, h⟩
  | cons p ps ih =>
    intro h
    obtain ⟨hp, ht⟩ := h
    let R := TableauReverseOutput.remove n S.1 S.2.1 S.2.2 p hp
    let S' : State n := ⟨TableauCorner.eraseShape S.1 p hp, ⟨R.tableau,R.bounded⟩⟩
    obtain ⟨Q, hQ, hμ⟩ := ih S' ht
    refine ⟨(Q.1,Q.2 ++ [R.letter]), ?_, hμ⟩
    simp only [reverseRun, dif_pos hp]
    rw [hQ]
    rfl

private theorem reverse_append (n : ℕ) (S : State n) (ps qs : List (ℕ × ℕ)) :
    reverseRun n S (ps ++ qs) =
      (reverseRun n S ps).bind (fun P =>
        (reverseRun n P.1 qs).map (fun Q => (Q.1, Q.2 ++ P.2))) := by
  classical
  induction ps generalizing S with
  | nil => simp [reverseRun]
  | cons p ps ih =>
    by_cases hp : TableauCorner.IsCorner S.1 p
    · let R := TableauReverseOutput.remove n S.1 S.2.1 S.2.2 p hp
      let S' : State n := ⟨TableauCorner.eraseShape S.1 p hp, ⟨R.tableau,R.bounded⟩⟩
      simp only [List.cons_append, reverseRun, dif_pos hp]
      rw [ih]
      cases ht : reverseRun n S' ps with
      | none => simp [ht, S', R]
      | some P =>
        cases hq : reverseRun n P.1 qs <;> simp [ht, hq, S', R, List.append_assoc]
    · simp [reverseRun, hp]

theorem reverse_after_run (n : ℕ) (S : State n) (w : List (Fin n)) : afterRun n S w := by
  classical
  induction w generalizing S with
  | nil => rfl
  | cons a w ih =>
    let I := TableauInsertion.insert n S.1 S.2.1 S.2.2 a
    let S' : State n := ⟨I.shape, ⟨I.tableau,I.bounded⟩⟩
    let P := TableauWordInsertion.run n S' w
    have ht := ih S'
    change reverseRun n P.1 P.2.reverse = some (S',w) at ht
    change reverseRun n P.1 (I.newCell :: P.2).reverse = some (S,a :: w)
    rw [List.reverse_cons, reverse_append, ht]
    have hp := TableauCorner.insert_newCell_corner n S.1 S.2.1 S.2.2 a
    have hi := TableauInsertionInverse.remove_after_insert n S.1 S.2.1 S.2.2 a
    change (reverseRun n S' [I.newCell]).map (fun Q => (Q.1,Q.2 ++ w)) = some (S,a :: w)
    dsimp only [S', I]
    simp only [reverseRun, dif_pos hp]
    rw [hi.1, hi.2.1]
    rfl

end OddMath.Frontier.TableauReverseWord
