import OddMath.SKM.SameColourTargetFrame
import OddMath.SKM.PairedTargetCapColumns

/-! Cap component columns for the complete paired target frame. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- Compose contextual placements through any propositionally equal boundary.
This avoids rewriting the boundary inside dependent Hom types. -/
theorem plcW_comp_at (μ : X) (s t mid u v a b c : List (Letter I))
    (hm : mid = u ++ b ++ v)
    (g₁ : (pres D Sc).obj (ob D (wt D μ v) a) ⟶ (pres D Sc).obj (ob D (wt D μ v) b))
    (g₂ : (pres D Sc).obj (ob D (wt D μ v) b) ⟶ (pres D Sc).obj (ob D (wt D μ v) c)) :
    plcW μ s mid u v a b g₁ ≫ plcW μ mid t u v b c g₂ =
      plcW μ s t u v a c (g₁ ≫ g₂) := by
  subst mid
  exact (plcW_comp μ s t u v a b c g₁ g₂).symm

namespace SameColourTargetFrame
variable {cs : CScalars Sc} {μ : X} {a P Q : List (Letter I)} {i : I}
  (F : SameColourTargetFrame cs μ a P Q i)

def targetCap (s : ℕ) :
    (pres D Sc).obj (ob D μ (P ++ up i :: dn i :: Q)) ⟶
      (pres D Sc).obj (ob D μ (P ++ Q)) :=
  plcW μ (P ++ up i :: dn i :: Q) (P ++ Q) P Q [up i, dn i] []
    (eLM D Sc i (wt D μ Q) s)

/-- Native cap-component evaluation, with arbitrary abstract SYM input. -/
theorem cap_column (N b s : ℕ) (r : F.residual.Labels) (d : SYM D k)
    (hN : D.h i (wt D μ Q) = (N : ℤ)) (hpos : 0 < N) :
    F.residual.expansion cs μ (MatchingTransition.rightColumn (k := k)
      (F.residual.targetCapColumn cs μ i N b s r) d) =
    F.original.expansion cs μ (Finsupp.single (F.paired (b, r)) d) ≫
      targetCap (Sc := Sc) (μ := μ) (P := P) (Q := Q) (i := i) s := by
  rw [F.residual.expansion_rightColumn, F.residual.targetCapColumn_eval cs μ i N b s r hN hpos,
    F.original.expansion_single, F.original_row]
  simp only [MatchingBasisChoice.rightAction, targetCap, Category.assoc]
  rw [plcW_comp_at μ (P ++ Q) (P ++ Q) (P ++ up i :: dn i :: Q)
    P Q [] [up i, dn i] [] (by simp)]
  simp only [plcAt, Category.assoc]

end SameColourTargetFrame
end OddMath.SKM
