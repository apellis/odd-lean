import OddMath.SKM.PositiveMatchingDots

/-! Empty and repeated-colour fixtures for the finite dot-decoration bridge. -/

noncomputable section
namespace OddMath.SKM.PositiveMatchingDotsExamples
open StringDiagrams.Chord DTMove

private def emptyColour : Fin 0 → Empty := Fin.elim0

example : ∃ p : MatchingStrand (List.ofFn fun r => (true, emptyColour r)) [] → Fin 0,
    Function.Bijective p ∧
      ∀ j : MatchingStrand (List.ofFn fun r => (true, emptyColour r)) [],
      OnStrand₂ (List.ofFn fun r => (true, emptyColour r)) [] j (0, (p j).val) :=
  positive_top_points emptyColour emptyColour (R := []) ⟨trivial, rfl⟩

example (n : MatchingStrand ([] : List (Letter Empty)) [] → ℕ) :
    topDotMoves [] [] (fun _ => 0) n = [] := by
  simp [topDotMoves, leftEnds₂, pairing₂, tStart, tRun, cupMoves, run]

private def colours : Fin 2 → Unit := fun _ => ()
private def A : List (Letter Unit) := List.ofFn fun r => (true, colours r)
private def R : List (TMove (Letter Unit)) := [.mv (.cross 0)]

private theorem matching : IsMatching₂ A A R := by
  constructor
  · change 3 < 4 ∧ True
    decide
  · rfl

private def position (j : MatchingStrand A R) : Fin 2 :=
  ⟨j.val, (positive_mem_leftEnds₂ colours colours matching j).mp j.property⟩

private theorem position_injective : Function.Injective position := by
  intro j k h
  exact Subtype.ext (congrArg Fin.val h)

private theorem position_onStrand (j : MatchingStrand A R) :
    OnStrand₂ A R j (R.length, (position j).val) := by
  rcases j with ⟨j, hj⟩
  have h := (positive_mem_leftEnds₂ colours colours matching j).mp hj
  interval_cases j <;> dsimp only [position] <;> unfold OnStrand₂ <;> decide

private def counts (j : MatchingStrand A R) : ℕ := if j.val = 0 then 1 else 2

-- The two strands remain separate although their colours coincide.
example : Fintype.card (MatchingStrand A R) = 2 := by
  obtain ⟨p, hp, -⟩ := positive_top_points colours colours matching
  simpa [A] using Fintype.card_congr (Equiv.ofBijective p hp)

example : ∀ j : MatchingStrand A R, OnStrand₂ A R j (R.length, (position j).val) :=
  position_onStrand

example : Decorates₂ A R (fun j => (R.length, strandPosition (fun j => (position j).val) j))
    (strandCounts counts) (topDotMoves A R (fun j => (position j).val) counts) :=
  topDotMoves_decorates A R _ counts

example : DOk₂ A (topDotMoves A R (fun j => (position j).val) counts) :=
  topDotMoves_valid colours matching position counts

example : XChain A (dLay A (topDotMoves A R (fun j => (position j).val) counts)) A :=
  xChain_topDotMoves colours matching position counts

example : Function.Injective (topDotMoves A R (fun j => (position j).val)) :=
  topDotMoves_injective A R _ (fun _ _ h => position_injective (Fin.ext h))

example : Function.Injective (fun n => dLay A (topDotMoves A R (fun j => (position j).val) n)) :=
  dLay_topDotMoves_injective colours matching position position_injective

private def crossing : List (LayerData Unit) := [([], Shape.cross () (), [])]
private theorem crossing_layers : crossing.map ofL = tLay A R := rfl

-- These are instantiated on a repeated-colour matching and a nonzero count vector;
-- the root datum and symmetrizer remain arbitrary.
example {X : Type*} [AddCommGroup X] (D : Datum Unit X) (sy : Symmetrizer D) (μ : X) :
    (crossing ++ topDotLayers colours position counts).map ofL =
      dLay A (topDotMoves A R (fun j => (position j).val) counts) ∧
    gsum D sy μ (crossing ++ topDotLayers colours position counts) =
      gsum D sy μ crossing + ((leftEnds₂ A R).attach.map fun j =>
        (counts j : ℤ) * (2 * sy.d (colours (position j)))).sum :=
  topDotMoves_degree D sy μ colours matching position counts crossing crossing_layers

example {X : Type*} [AddCommGroup X] (D : Datum Unit X) (μ : X) :
    xpar D μ (dLay A (topDotMoves A R (fun j => (position j).val) counts)) =
      xpar D μ (tLay A R) + ((leftEnds₂ A R).attach.map fun j =>
        (counts j : ZMod 2) * D.parity (colours (position j))).sum :=
  topDotMoves_parity D μ colours matching position counts

end OddMath.SKM.PositiveMatchingDotsExamples
