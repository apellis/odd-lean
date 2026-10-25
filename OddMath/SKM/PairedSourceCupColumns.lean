import OddMath.SKM.PairedSourceUpwardColumns

/-! The cup components of the paired source columns. Low rows are
normalized in abstract SYM so that they have the scalar unit diagonal. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace SameColourSourceFrame
variable {P Q Z : List (Letter I)} {i : I} (B : SameColourSourceFrame P Q Z i)
  (cs : CScalars Sc) (μ : X)

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

/-- A cup output column, using the exact scalar diagonal below the cutoff. -/
def sourceCupColumn (N b s : ℕ) (r : B.residual.Labels) : B.residual.Labels →₀ SYM D k :=
  if b + s < N then
    if b + s = N - 1 then (↑(cs.c (wt D μ Q) i)⁻¹ : k) • Finsupp.single r 1 else 0
  else B.sourceLoopLift cs μ r
    (hLM D Sc i (wt D μ Q) s ≫ cpow (uRM D Sc i (wt D μ Q)) b ≫ epsP cs i (wt D μ Q))

theorem sourceCupColumn_eval (N b s : ℕ) (r : B.residual.Labels)
    (hN : -D.h i (wt D μ Q) = (N : ℤ)) (hpos : 0 < N) :
    B.residual.expansion cs μ (B.sourceCupColumn cs μ N b s r) =
      plcAt μ (P ++ Q) (P ++ Q) P Q
          (hLM D Sc i (wt D μ Q) s ≫ cpow (uRM D Sc i (wt D μ Q)) b ≫
            epsP cs i (wt D μ Q)) ≫ xev cs μ (P ++ Q) Z (B.residual.layers r) := by
  by_cases hbs : b + s < N
  · rw [sourceCupColumn, ite_eq_left hbs,
      paired_source_low cs i (wt D μ Q) s b (by omega)]
    by_cases he : b + s = N - 1
    · rw [ite_eq_left he, ite_eq_left (show ((s + b : ℕ) : ℤ) = -D.h i (wt D μ Q) - 1 by omega), map_smul, map_smul, B.residual.expansion_single]
      change (↑(cs.c (wt D μ Q) i)⁻¹ : k) • MatchingBasisChoice.rightAction cs μ _ 1 = _
      rw [MatchingBasisChoice.rightAction_one, residualContext_id, Linear.smul_comp, Category.id_comp]
    · rw [ite_eq_right he, ite_eq_right (show ¬ ((s + b : ℕ) : ℤ) = -D.h i (wt D μ Q) - 1 by omega), map_zero, map_zero, Limits.zero_comp]
  · rw [sourceCupColumn, ite_eq_right hbs, B.sourceLoopLift_eval]

/-- The low pivot is exactly a scalar unit, not a chosen expansion of one. -/
theorem sourceCupColumn_pivot (N b : ℕ) (r : B.residual.Labels) (hb : b < N) :
    B.sourceCupColumn cs μ N b (N - 1 - b) r =
      (↑(cs.c (wt D μ Q) i)⁻¹ : k) • Finsupp.single r 1 := by
  rw [sourceCupColumn, ite_eq_left (by omega), ite_eq_left (by omega)]

/-- Every strictly earlier paired input vanishes at a low pivot cup. -/
theorem sourceCupColumn_below (N b d : ℕ) (r : B.residual.Labels)
    (hb : b < N) (hd : d < b) :
    B.sourceCupColumn cs μ N d (N - 1 - b) r = 0 := by
  rw [sourceCupColumn, ite_eq_left (by omega), ite_eq_right (by omega)]

end SameColourSourceFrame
end OddMath.SKM
