/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.EvenBridge.Functor
import OddMath.SKM.TableIsotopy
import Categorification.Diagrams.KL3.CanonDeg

/-!
# Degrees of chord diagrams in `𝔘(𝔤)` and in KL III's `U`

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, (1.13) (the degrees
of the generating 2-morphisms), and A. D. Lauda, M. Khovanov, *A categorification of quantum
sl(n)* III, arXiv:0807.3250, Definition 3.1 (the degrees of its generators).

The layers `chordLay l E` of a chord diagram in `𝔘(𝔤)` (with the leftward cups and caps
`η'`, `ε'` and the downward and rightward crossings written through the generators) and the
layers `chL l E` of the same chord diagram in `U` have the same degree, for every symmetrizable
datum `D` compatible with the Cartan datum `C` and the symmetrizer `symmetrizer D C hc`
(`tableDegree_chordLay`). Cups have degree `dᵢ (1 ∓ ⟨i, ν⟩)` on both sides and a crossing of two
strands has degree `-i·j` if they have the same orientation and `0` otherwise.
-/

noncomputable section

namespace OddMath.SKM.EvenBridge

open StringDiagrams StringDiagrams.Chord Categorification.KL3 Categorification.QuantumGroup

universe u v

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
  (C : CartanDatum I) (hc : Compatible D C)

/-- Shorthand for the KL III weight datum of `D`. -/
local notation "RD" => weightDatum D C hc

theorem chStep_eq_lst (l : List (Letter I)) (m : Move (Letter I)) :
    chStep l m = Diagram.lst l m := rfl

/-- **A chord diagram has the same degree in `𝔘(𝔤)` and in `U`.** -/
theorem tableDegree_chordLay (μ : X) :
    ∀ (l : List (Letter I)) (E : List (Move (Letter I))),
      tableDegree D (symmetrizer D C hc) μ (chordLay l E) = Diagram.sdegSum RD μ (Diagram.chL l E)
  | _, [] => rfl
  | l, m :: E => by
    rw [chordLay, Diagram.chL, tableDegree_append, Diagram.sdegSum_append,
      tableDegree_chordLay μ _ E, chStep_eq_lst]
    congr 1
    rcases m with ⟨g, x⟩ | p
    · simp only [moveLay, Diagram.mvL, tableDegree_whisk, tableDegree_cup, Diagram.sdegSum,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Diagram.sdeg,
        symmetrizer_d, wt_eq D C hc]
      obtain ⟨_ | _, i⟩ := x
      · simp [UDot.sgn, weightDatum_pair]
      · simp [UDot.sgn, weightDatum_pair]
        ring_nf
        simp
    · simp only [moveLay, Diagram.mvL]
      rcases l.drop p with _ | ⟨x, _ | ⟨y, r⟩⟩
      · rfl
      · rfl
      · rw [tableDegree_whisk, tableDegree_cross, Diagram.sdegSum_map_whL, Diagram.sdegSum_xLay,
          symmetrizer_d, d_eq hc, mul_neg, UDot.di_mul_A]

end OddMath.SKM.EvenBridge
