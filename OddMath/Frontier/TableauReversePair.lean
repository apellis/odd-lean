import OddMath.Frontier.TableauInsertionInverse
import OddMath.Frontier.TableauBumpStrict

/-!
Recovered-letter order for two genuine right-to-left corner removals.
Fulton, Young Tableaux §1.1, printed p11 / frozen PDF23, lines785–802.
Reinsert the two actual returned letters, transport the second insertion across
full dependent state equality, then contradict the strict Row Bumping Lemma.
-/
namespace OddMath.Frontier.TableauReversePair
open OddMath.Frontier TableauSign TableauEvaluation

def pair_order (n : ℕ) (ν : YoungDiagram) (T : PositiveTableau ν)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : TableauCorner.IsCorner ν p)
    (q : ℕ × ℕ) (hq : TableauCorner.IsCorner (TableauCorner.eraseShape ν p hp) q) : Prop :=
  let R := TableauReverseOutput.remove n ν T hT p hp
  let Q := TableauReverseOutput.remove n (TableauCorner.eraseShape ν p hp)
    R.tableau R.bounded q hq
  q.2 < p.2 → Q.letter ≤ R.letter

/-- Weak order of the actual letters, with no horizontal-strip or success premise. -/
theorem remove_pair_order (n : ℕ) (ν : YoungDiagram) (T : PositiveTableau ν)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : TableauCorner.IsCorner ν p)
    (q : ℕ × ℕ) (hq : TableauCorner.IsCorner (TableauCorner.eraseShape ν p hp) q) :
    pair_order n ν T hT p hp q hq := by
  let μ := TableauCorner.eraseShape ν p hp
  let R := TableauReverseOutput.remove n ν T hT p hp
  let ξ := TableauCorner.eraseShape μ q hq
  let Q := TableauReverseOutput.remove n μ R.tableau R.bounded q hq
  let I := TableauInsertion.insert n ξ Q.tableau Q.bounded Q.letter
  let J := TableauInsertion.insert n I.shape I.tableau I.bounded R.letter
  have hp_inv := TableauInsertionInverse.insert_after_remove n ν T hT p hp
  have hq_inv := TableauInsertionInverse.insert_after_remove n μ R.tableau R.bounded q hq
  have hI : I.newCell = q := hq_inv.2.1
  have hJ : J.newCell = p := by
    have he := congrArg
      (fun s : Σ ζ : YoungDiagram, {U : PositiveTableau ζ // InAlphabet n U} =>
        (TableauInsertion.insert n s.1 s.2.1 s.2.2 R.letter).newCell) hq_inv.1
    exact he.trans hp_inv.2.1
  change q.2 < p.2 → Q.letter ≤ R.letter
  intro hcol
  by_contra horder
  have hlt : R.letter < Q.letter := lt_of_not_ge horder
  have hc := (TableauBumpStrict.insert_pair_gt n ξ Q.tableau Q.bounded
    Q.letter R.letter hlt).2.2.1
  change J.newCell.2 ≤ I.newCell.2 at hc
  rw [hI, hJ] at hc
  exact (not_le_of_gt hcol) hc

#print axioms pair_order
#print axioms remove_pair_order
end OddMath.Frontier.TableauReversePair
