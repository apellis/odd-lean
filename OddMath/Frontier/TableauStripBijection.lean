import OddMath.Frontier.TableauReverseOrder
import OddMath.Frontier.TableauStripUniqueness

namespace OddMath.Frontier.TableauStripBijection
abbrev State (n : ℕ) := TableauWordInsertion.State n

def reconstruction (n : ℕ) (μ : YoungDiagram) (S : State n) : Prop :=
  TableauStripCorners.Horizontal μ S.1 →
    ∃! Q : State n × List (Fin n),
      Q.1.1 = μ ∧ Q.2.Sorted (· ≤ ·) ∧
      Q.2.length = (S.1.cells \ μ.cells).card ∧
      (TableauWordInsertion.run n Q.1 Q.2).1 = S

def Inputs (n : ℕ) (μ : YoungDiagram) (r : ℕ) :=
  {Q : State n × List (Fin n) //
    Q.1.1 = μ ∧ Q.2.Sorted (· ≤ ·) ∧ Q.2.length = r}

def Outputs (n : ℕ) (μ : YoungDiagram) (r : ℕ) :=
  {S : State n // TableauStripCorners.Horizontal μ S.1 ∧
    (S.1.cells \ μ.cells).card = r}

/-!
Fulton, Young Tableaux §1.1, printed p11 / frozen PDF23, lines785–802,
especially788–799. Source-qualified weak-order transcription retained.
English zero-based cells; Fin n labels denote positive values val+1.
The outer state is arbitrary: choose a right-to-left skew-cell enumeration,
reverse actual insertion, recover weak order, and use full-state uniqueness.
No history or inverse certificate is assumed; n=0 and empty strips are included.
-/

theorem strip_exists_unique (n : ℕ) (μ : YoungDiagram) (S : State n) :
    reconstruction n μ S := by
  intro h
  obtain ⟨ps, ho, he, hp⟩ := TableauStripCorners.exists_peel_order μ S.1 h
  obtain ⟨Q, hQ, hμ⟩ := TableauReverseWord.reverse_of_peels n μ S ps hp
  have hs := TableauReverseWord.reverse_spec n S ps Q hQ
  have hw := TableauReverseOrder.reverse_order n S ps ho Q hQ
  have hlen : Q.2.length = (S.1.cells \ μ.cells).card := by
    rw [← he, List.toFinset_card_of_nodup hs.2.2.1]
    exact hs.1
  have hf : (TableauWordInsertion.run n Q.1 Q.2).1 = S :=
    congrArg Prod.fst hs.2.2.2.2
  refine ⟨Q, ⟨hμ, hw, hlen, hf⟩, ?_⟩
  intro P hP
  exact TableauStripUniqueness.weak_preimage_unique n P.1 Q.1 P.2 Q.2
    (hP.1.trans hμ.symm) hP.2.1 hw (hP.2.2.2.trans hf.symm)

private theorem run_card (n : ℕ) (S : State n) (w : List (Fin n)) :
    ((TableauWordInsertion.run n S w).1.1.cells \ S.1.cells).card = w.length := by
  have hs := TableauWordInsertion.run_spec n S w
  rw [← hs.2.2.2, List.toFinset_card_of_nodup hs.2.1]
  exact hs.1

private noncomputable def forward (n : ℕ) (μ : YoungDiagram) (r : ℕ)
    (x : Inputs n μ r) : Outputs n μ r :=
  ⟨(TableauWordInsertion.run n x.val.1 x.val.2).1, by
    rcases x with ⟨⟨S, w⟩, hshape, hsorted, hlength⟩
    dsimp only at hshape ⊢
    subst μ
    have hs := TableauWordInsertion.run_spec n S w
    have hh := TableauWordInsertion.run_horizontal n S w hsorted
    exact ⟨⟨hs.2.2.1, hh.2⟩, (run_card n S w).trans hlength⟩⟩

private theorem forward_bijective (n : ℕ) (μ : YoungDiagram) (r : ℕ) :
    Function.Bijective (forward n μ r) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact TableauStripUniqueness.weak_preimage_unique n x.val.1 y.val.1 x.val.2 y.val.2
      (x.property.1.trans y.property.1.symm) x.property.2.1 y.property.2.1
      (congrArg Subtype.val h)
  · intro y
    obtain ⟨Q, hQ, _⟩ := strip_exists_unique n μ y.val y.property.1
    let x : Inputs n μ r := ⟨Q, hQ.1, hQ.2.1, hQ.2.2.1.trans y.property.2⟩
    refine ⟨x, Subtype.ext ?_⟩
    exact hQ.2.2.2

/-- Insertion on full bounded tableaux and weakly increasing chronological words. -/
noncomputable def insertionEquiv (n : ℕ) (μ : YoungDiagram) (r : ℕ) :
    Inputs n μ r ≃ Outputs n μ r :=
  Equiv.ofBijective (forward n μ r) (forward_bijective n μ r)

theorem insertionEquiv_apply (n : ℕ) (μ : YoungDiagram) (r : ℕ) (x : Inputs n μ r) :
    (insertionEquiv n μ r x).val = (TableauWordInsertion.run n x.val.1 x.val.2).1 := rfl

end OddMath.Frontier.TableauStripBijection
