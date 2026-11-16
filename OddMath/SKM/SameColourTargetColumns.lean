import OddMath.SKM.PairedTargetColumns

/-! Attach finite paired columns to the complete swapped matching choice.
All coefficients remain in abstract SYM, with residual lifts at global μ. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace MatchingBasisChoice
variable {a P Q : List (Letter I)} (B : MatchingBasisChoice a (P ++ Q))
  (cs : CScalars Sc) (μ : X) (i : I)
  (G : MatchingBasisChoice a (P ++ dn i :: up i :: Q))
  (p : ℕ × B.Labels ↪ G.Labels)

/-- Insert all paired rows into the complete swapped family. -/
def pairedRowsInclusion : ((B.Labels × ℕ) →₀ SYM D k) →ₗ[k] (G.Labels →₀ SYM D k) :=
  Finsupp.lmapDomain (SYM D k) k (fun r => p (r.2, r.1))

theorem pairedRowsInclusion_eval
    (hp : ∀ b r, xev cs μ a (P ++ dn i :: up i :: Q) (G.layers (p (b, r))) =
      xev cs μ a (P ++ Q) (B.layers r) ≫ targetCupRows (Sc := Sc) μ P Q i b)
    (v : (B.Labels × ℕ) →₀ SYM D k) :
    G.expansion cs μ (B.pairedRowsInclusion (D := D) (k := k) i G p v) =
      B.postRowsExpansion cs μ (targetCupRows (Sc := Sc) μ P Q i) v := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single r d =>
    obtain ⟨r, b⟩ := r
    simp only [pairedRowsInclusion, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rw [G.expansion_single, B.postRowsExpansion_single, hp]

/-- The positive-height paired column, now in the complete target choice. -/
theorem targetPositiveColumn_in_choice
    (hp : ∀ b r, xev cs μ a (P ++ dn i :: up i :: Q) (G.layers (p (b, r))) =
      xev cs μ a (P ++ Q) (B.layers r) ≫ targetCupRows (Sc := Sc) μ P Q i b)
    (N b : ℕ) (r : B.Labels) (d : SYM D k)
    (hN : D.h i (wt D μ Q) = (N : ℤ)) (hpos : 0 < N) :
    G.expansion cs μ (B.pairedRowsInclusion i G p
      (MatchingTransition.rightColumn (k := k) (B.targetPositiveColumn cs μ i N b r) d)) =
      rightAction cs μ (xev cs μ a (P ++ Q) (B.layers r) ≫
        plcW μ (P ++ Q) (P ++ dn i :: up i :: Q) P Q [] [dn i, up i]
          (etaP cs i (wt D μ Q) ≫ cpow (uLM D Sc i (wt D μ Q)) b ≫
            sgM D Sc i (wt D μ Q))) d := by
  rw [B.pairedRowsInclusion_eval cs μ i G p hp,
    B.postRowsExpansion_rightColumn, B.targetPositiveColumn_eval cs μ i N b r hN hpos]

/-- The nonpositive-height paired column, with both finite correction sums
included, in the complete target choice. -/
theorem targetNonpositiveColumn_in_choice
    (hp : ∀ b r, xev cs μ a (P ++ dn i :: up i :: Q) (G.layers (p (b, r))) =
      xev cs μ a (P ++ Q) (B.layers r) ≫ targetCupRows (Sc := Sc) μ P Q i b)
    (N b : ℕ) (r : B.Labels) (d : SYM D k)
    (hN : -D.h i (wt D μ Q) = (N : ℤ)) :
    G.expansion cs μ (B.pairedRowsInclusion i G p
      (MatchingTransition.rightColumn (k := k) (B.targetNonpositiveColumn cs μ i N b r) d)) =
      rightAction cs μ (xev cs μ a (P ++ Q) (B.layers r) ≫
        plcW μ (P ++ Q) (P ++ dn i :: up i :: Q) P Q [] [dn i, up i]
          (etaP cs i (wt D μ Q) ≫ cpow (uLM D Sc i (wt D μ Q)) b ≫
            sgM D Sc i (wt D μ Q))) d := by
  rw [B.pairedRowsInclusion_eval cs μ i G p hp,
    B.postRowsExpansion_rightColumn, B.targetNonpositiveColumn_eval cs μ i N b r hN]

end MatchingBasisChoice
end OddMath.SKM
