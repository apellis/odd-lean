import OddMath.SKM.PointedCupMatching
import OddMath.SKM.PairedSorting
import OddMath.SKM.SpanClosed
import OddMath.SKM.MixedRealization

/-! Literal cup serializers evaluate to the native paired rows. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams StringDiagrams.Chord Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

 theorem dLay_upward_replicate (P Q : List (Letter I)) (i : I) (n : ℕ) :
    dLay (P ++ up i :: Q) (List.replicate n (.dt P.length)) =
      (dotsL P i Q n).map ofL := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, dLay, ih, dotsL, List.map_cons]
    simp [dotOn, xDotL, xwhL, ofL]

 theorem paired_cup_dn_evaluation (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    xev cs μ [] [dn i, up i]
      (xCupL (dn i) ++ dLay [dn i, up i] (List.replicate n (.dt 1))) =
      hLM D Sc i μ n := by
  rw [show dLay [dn i, up i] (List.replicate n (.dt 1)) =
    (dotsL [dn i] i [] n).map ofL from dLay_upward_replicate [dn i] [] i n]
  exact xev_map_ofL cs μ [] [dn i, up i] (etaL i n)

 theorem paired_cup_up_evaluation (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    xev cs μ [] [up i, dn i]
      (xCupL (up i) ++ dLay [up i, dn i] (List.replicate n (.dt 0))) =
      etaP cs i μ ≫ cpow (uLM D Sc i μ) n := by
  rw [show dLay [up i, dn i] (List.replicate n (.dt 0)) =
    (dotsL [] i [dn i] n).map ofL from dLay_upward_replicate [] [dn i] i n,
    xev_append cs _ (xChain_xCupL (up i)), xev_map_ofL, xCupL_up, flipL_up, xev_lcup]
  congr 1
  exact cl_dotsL_eq_pow μ [] i [dn i] n rfl

theorem dLay_cupDecoratedMoves_local {a P Q : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ Q) R)
    (ε : Bool) (i : I) (n : ℕ) {ds : List (DTMove I)} (hd : DTMove.tmoves ds = R) :
    dLay a (cupDecoratedMoves P ε i n ds) = dLay a ds ++
      (xCupL (ε, i) ++ dLay [(ε, i), (!ε, i)]
        (List.replicate n (.dt (if ε then 0 else 1)))).map (xwhL P Q) := by
  rw [dLay_cupDecoratedMoves hR ε i n hd, List.map_append, List.append_assoc]
  congr 1
  cases ε
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    rw [show P ++ (false, i) :: (true, i) :: Q =
      (P ++ [dn i]) ++ up i :: Q by simp [dn, up],
      show P.length + 1 = (P ++ [dn i]).length by simp,
      dLay_upward_replicate]
    rw [show dLay [(false, i), (true, i)] (List.replicate n (.dt 1)) =
      (dotsL [dn i] i [] n).map ofL from dLay_upward_replicate [dn i] [] i n]
    simp [dotsL, List.map_replicate, xwhL, ofL]
  · simp only [↓reduceIte, Bool.not_true]
    rw [show dLay (P ++ (true, i) :: (false, i) :: Q)
        (List.replicate n (.dt P.length)) =
      (dotsL P i (dn i :: Q) n).map ofL from dLay_upward_replicate P (dn i :: Q) i n]
    rw [show dLay [(true, i), (false, i)] (List.replicate n (.dt 0)) =
      (dotsL [] i [dn i] n).map ofL from dLay_upward_replicate [] [dn i] i n]
    simp [dotsL, List.map_replicate, xwhL, ofL]

theorem xev_cupDecoratedMoves_split (cs : CScalars Sc) (μ : X)
    {a P Q : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ Q) R) (ε : Bool) (i : I) (n : ℕ)
    {ds : List (DTMove I)} (hd : DTMove.tmoves ds = R)
    (hds : XChain a (dLay a ds) (P ++ Q)) :
    xev cs μ a (P ++ (ε, i) :: (!ε, i) :: Q)
        (dLay a (cupDecoratedMoves P ε i n ds)) =
      xev cs μ a (P ++ Q) (dLay a ds) ≫
        xev cs μ (P ++ Q) (P ++ (ε, i) :: (!ε, i) :: Q)
          ((xCupL (ε, i) ++ dLay [(ε, i), (!ε, i)]
            (List.replicate n (.dt (if ε then 0 else 1)))).map (xwhL P Q)) := by
  rw [dLay_cupDecoratedMoves_local hR ε i n hd, xev_append cs _ hds]

theorem paired_cup_dn_context (cs : CScalars Sc) (μ : X)
    (P Q : List (Letter I)) (i : I) (n : ℕ) :
    xev cs μ (P ++ Q) (P ++ dn i :: up i :: Q)
      ((xCupL (dn i) ++ dLay [dn i, up i] (List.replicate n (.dt 1))).map (xwhL P Q)) =
      plcW μ (P ++ Q) (P ++ dn i :: up i :: Q) P Q [] [dn i, up i]
        (hLM D Sc i (wt D μ Q) n) := by
  have hc : XChain [] (xCupL (dn i) ++
      dLay [dn i, up i] (List.replicate n (.dt 1))) [dn i, up i] := by
    rw [show dLay [dn i, up i] (List.replicate n (.dt 1)) =
      (dotsL [dn i] i [] n).map ofL from dLay_upward_replicate [dn i] [] i n]
    exact XChain.of_sChain (sChain_etaL i n)
  rw [xev_eq_plcW (cs := cs) μ P Q hc (by simp [xCupL]), paired_cup_dn_evaluation]

 theorem paired_cup_up_context (cs : CScalars Sc) (μ : X)
    (P Q : List (Letter I)) (i : I) (n : ℕ) :
    xev cs μ (P ++ Q) (P ++ up i :: dn i :: Q)
      ((xCupL (up i) ++ dLay [up i, dn i] (List.replicate n (.dt 0))).map (xwhL P Q)) =
      plcW μ (P ++ Q) (P ++ up i :: dn i :: Q) P Q [] [up i, dn i]
        (etaP cs i (wt D μ Q) ≫ cpow (uLM D Sc i (wt D μ Q)) n) := by
  have hc : XChain [] (xCupL (up i) ++
      dLay [up i, dn i] (List.replicate n (.dt 0))) [up i, dn i] := by
    rw [show dLay [up i, dn i] (List.replicate n (.dt 0)) =
      (dotsL [] i [dn i] n).map ofL from dLay_upward_replicate [] [dn i] i n]
    exact (xChain_xCupL (up i)).append (XChain.of_sChain (sChain_dotsL [] i [dn i] n))
  rw [xev_eq_plcW (cs := cs) μ P Q hc (by simp [xCupL]), paired_cup_up_evaluation]

namespace PointedMatching
 theorem appendCup_local_layers {a P Q : List (Letter I)}
    (F : PointedMatching a (P ++ Q)) (ε : Bool) (i : I)
    (b : ℕ) (n : MatchingStrand a F.moves → ℕ) :
    (F.appendCup ε i).layers ((terminalCupCountsEquiv F.matching ε i).symm (b, n)) =
      F.layers n ++ (xCupL (ε, i) ++ dLay [(ε, i), (!ε, i)]
        (List.replicate b (.dt (if ε then 0 else 1)))).map (xwhL P Q) := by
  rw [F.appendCup_layers]
  exact (dLay_cupDecoratedMoves F.matching ε i b (F.decorates n).1).symm.trans
    (dLay_cupDecoratedMoves_local F.matching ε i b (F.decorates n).1)

theorem appendCup_dn_eval {a P Q : List (Letter I)}
    (F : PointedMatching a (P ++ Q)) (cs : CScalars Sc) (μ : X) (i : I)
    (b : ℕ) (n : MatchingStrand a F.moves → ℕ) :
    xev cs μ a (P ++ dn i :: up i :: Q)
      ((F.appendCup false i).layers ((terminalCupCountsEquiv F.matching false i).symm (b, n))) =
    xev cs μ a (P ++ Q) (F.layers n) ≫
      plcW μ (P ++ Q) (P ++ dn i :: up i :: Q) P Q [] [dn i, up i]
        (hLM D Sc i (wt D μ Q) b) := by
  have hc : XChain a (F.layers n) (P ++ Q) :=
    matching_dLay_chain F.matching (F.serialize n) (F.decorates n).1
  rw [appendCup_local_layers, xev_append cs _ hc]
  exact congrArg (fun z => xev cs μ a (P ++ Q) (F.layers n) ≫ z)
    (paired_cup_dn_context cs μ P Q i b)

theorem appendCup_up_eval {a P Q : List (Letter I)}
    (F : PointedMatching a (P ++ Q)) (cs : CScalars Sc) (μ : X) (i : I)
    (b : ℕ) (n : MatchingStrand a F.moves → ℕ) :
    xev cs μ a (P ++ up i :: dn i :: Q)
      ((F.appendCup true i).layers ((terminalCupCountsEquiv F.matching true i).symm (b, n))) =
    xev cs μ a (P ++ Q) (F.layers n) ≫
      plcW μ (P ++ Q) (P ++ up i :: dn i :: Q) P Q [] [up i, dn i]
        (etaP cs i (wt D μ Q) ≫ cpow (uLM D Sc i (wt D μ Q)) b) := by
  have hc : XChain a (F.layers n) (P ++ Q) :=
    matching_dLay_chain F.matching (F.serialize n) (F.decorates n).1
  rw [appendCup_local_layers, xev_append cs _ hc]
  exact congrArg (fun z => xev cs μ a (P ++ Q) (F.layers n) ≫ z)
    (paired_cup_up_context cs μ P Q i b)
end PointedMatching
end OddMath.SKM
