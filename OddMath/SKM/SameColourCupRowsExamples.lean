import OddMath.SKM.SameColourCupRows
import OddMath.SKM.MixedCrossingLocalExamples

/-! Complete paired rows for an odd datum, with both contexts nonempty. -/
noncomputable section
namespace OddMath.SKM.SameColourCupRowsExamples
open CategoryTheory StringDiagrams Presentation
private abbrev D := MixedCrossingLocalExamples.oddDatum
private def Sc : Scalars D ℚ where
  t := fun _ _ => 1
  t_self := by intros; rfl
  t_symm_of_d_eq_zero := by intros; rfl
  s := fun _ _ _ _ => 0
  s_symm := by intros; rfl
  s_eq_zero := by intros; rfl
  two_isUnit := by intro _; exact isUnit_iff_ne_zero.mpr (by norm_num)
private def cs : CScalars Sc where
  c := fun _ _ => 1
  shift := by intros; simp [Sc]
private abbrev P : List (Letter Bool) := [up false]
private abbrev Q : List (Letter Bool) := [dn true]
private abbrev a : List (Letter Bool) := P ++ Q

/-- Both cup orientations use a complete residual family, at every dot count. -/
theorem complete_cup_rows :
    ∃ (B : MatchingBasisChoice a (P ++ Q))
      (F : MatchingBasisChoice a (P ++ up false :: dn false :: Q))
      (G : MatchingBasisChoice a (P ++ dn false :: up false :: Q))
      (e : F.Labels ≃ G.Labels) (p : ℕ × B.Labels ↪ F.Labels),
      (∀ b r, xev cs 0 a (P ++ up false :: dn false :: Q) (F.layers (p (b, r))) =
        xev cs 0 a (P ++ Q) (B.layers r) ≫
          plcW 0 (P ++ Q) (P ++ up false :: dn false :: Q) P Q [] [up false, dn false]
            (etaP cs false (wt D 0 Q) ≫ cpow (uLM D Sc false (wt D 0 Q)) b)) ∧
      (∀ b r, xev cs 0 a (P ++ dn false :: up false :: Q) (G.layers (e (p (b, r)))) =
        xev cs 0 a (P ++ Q) (B.layers r) ≫
          plcW 0 (P ++ Q) (P ++ dn false :: up false :: Q) P Q [] [dn false, up false]
            (hLM D Sc false (wt D 0 Q) b)) := by
  obtain ⟨B, F, G, e, p, _, hF, hG⟩ := exists_same_colour_cup_rows cs 0 a P Q false
  exact ⟨B, F, G, e, p, hF, hG⟩

#print axioms exists_same_colour_cup_rows
#print axioms complete_cup_rows
end OddMath.SKM.SameColourCupRowsExamples
