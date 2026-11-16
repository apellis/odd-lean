import OddMath.SKM.PairedTargetColumns

/-! The actual cap components of the paired target columns. Low rows are
normalized in abstract SYM so that they have the scalar unit diagonal. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace MatchingBasisChoice
variable {a P Q : List (Letter I)} (B : MatchingBasisChoice a (P ++ Q))
  (cs : CScalars Sc) (μ : X) (i : I)

/-- The contextual identity endomorphism on the residual boundary. -/
theorem residualContext_id :
    plcAt (D := D) (Sc := Sc) μ (P ++ Q) (P ++ Q) P Q
      (𝟙 ((pres D Sc).obj (ob D (wt D μ Q) []))) = 𝟙 _ := by
  dsimp only [plcAt]
  rw [plcW_apply, plcL_id, Category.id_comp,
    cl_comp (show SChain (P ++ Q) [] (P ++ [] ++ Q) from by
      change P ++ Q = P ++ [] ++ Q; simp)
      (show SChain (P ++ [] ++ Q) [] (P ++ Q) from by
        change P ++ [] ++ Q = P ++ Q; simp), List.nil_append, cl_nil]

/-- A cap output column, using the exact scalar diagonal below the cutoff. -/
def targetCapColumn (N b s : ℕ) (r : B.Labels) : B.Labels →₀ SYM D k :=
  if b + s < N then
    if b + s = N - 1 then (cs.c (wt D μ Q) i : k) • Finsupp.single r 1 else 0
  else B.targetLoopLift cs μ r
    (etaP cs i (wt D μ Q) ≫ cpow (uLM D Sc i (wt D μ Q)) b ≫ eLM D Sc i (wt D μ Q) s)

theorem targetCapColumn_eval (N b s : ℕ) (r : B.Labels)
    (hN : D.h i (wt D μ Q) = (N : ℤ)) (hpos : 0 < N) :
    B.expansion cs μ (B.targetCapColumn cs μ i N b s r) =
      xev cs μ a (P ++ Q) (B.layers r) ≫
        plcAt μ (P ++ Q) (P ++ Q) P Q
          (etaP cs i (wt D μ Q) ≫ cpow (uLM D Sc i (wt D μ Q)) b ≫
            eLM D Sc i (wt D μ Q) s) := by
  by_cases hbs : b + s < N
  · rw [targetCapColumn, ite_eq_left hbs,
      paired_target_low cs i (wt D μ Q) b s (by omega)]
    by_cases he : b + s = N - 1
    · rw [ite_eq_left he, ite_eq_left (show ((b + s : ℕ) : ℤ) = D.h i (wt D μ Q) - 1 by omega), map_smul, map_smul, B.expansion_single]
      change (cs.c (wt D μ Q) i : k) • rightAction cs μ _ 1 = _
      rw [rightAction_one, residualContext_id, Linear.comp_smul, Category.comp_id]
    · rw [ite_eq_right he, ite_eq_right (show ¬ ((b + s : ℕ) : ℤ) = D.h i (wt D μ Q) - 1 by omega), map_zero, map_zero, Limits.comp_zero]
  · rw [targetCapColumn, ite_eq_right hbs, B.targetLoopLift_eval]

/-- The low pivot is exactly a scalar unit, not a chosen expansion of one. -/
theorem targetCapColumn_pivot (N b : ℕ) (r : B.Labels) (hb : b < N) :
    B.targetCapColumn cs μ i N b (N - 1 - b) r =
      (cs.c (wt D μ Q) i : k) • Finsupp.single r 1 := by
  rw [targetCapColumn, ite_eq_left (by omega), ite_eq_left (by omega)]

/-- Every strictly earlier paired input vanishes at a low pivot cap. -/
theorem targetCapColumn_below (N b d : ℕ) (r : B.Labels)
    (hb : b < N) (hd : d < b) :
    B.targetCapColumn cs μ i N d (N - 1 - b) r = 0 := by
  rw [targetCapColumn, ite_eq_left (by omega), ite_eq_right (by omega)]

end MatchingBasisChoice
end OddMath.SKM
