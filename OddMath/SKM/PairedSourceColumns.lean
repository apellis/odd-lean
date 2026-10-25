import OddMath.SKM.PairedSourceEvaluation

/-! Full-SYM source coefficient columns in the actual complete swapped frame.
The cap twists the residual coefficient, independently of the crossing or
remainder-component twist on the input coefficient. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

theorem MatchingBasisChoice.source_expansion_single (cs : CScalars Sc) (μ : X)
    {a b : List (Letter I)} (A : MatchingBasisChoice a b) (r : A.Labels) (d : SYM D k) :
    A.expansion cs μ (Finsupp.single r d) =
      MatchingBasisChoice.rightAction cs μ (xev cs μ a b (A.layers r)) d :=
  A.expansion_single cs μ r d

theorem sourceParityTwist_zero : SYM.parityTwist D k 0 = LinearMap.id := by
  apply (SYM.coefficientBasis D k).ext
  intro a
  simp only [SYM.parityTwist_basis, zero_mul, zsign_zero, one_smul, LinearMap.id_apply]

theorem sourceParityTwist_one (q : ZMod 2) : SYM.parityTwist D k q 1 = 1 := by
  have H : SYM.coefficientBasis D k (0, ∅) = 1 := by
    apply (SYM.polynomialExteriorEquiv D k).injective
    rw [SYM.coefficientBasis_projection, SYM.oddExteriorBasis_empty]
    change 1 = (SYM.polynomialExteriorProjection D k) 1
    exact (map_one (SYM.polynomialExteriorProjection D k)).symm
  rw [← H, SYM.parityTwist_basis]
  simp [zsign_zero]

/-- Native contextual cap rows of the swapped source family. -/
def sourceCapRows (μ : X) (P Q : List (Letter I)) (i : I) (m : ℕ) :
    (pres D Sc).obj (ob D μ (P ++ up i :: dn i :: Q)) ⟶
      (pres D Sc).obj (ob D μ (P ++ Q)) :=
  plcW μ (P ++ up i :: dn i :: Q) (P ++ Q) P Q [up i, dn i] []
    (eLM D Sc i (wt D μ Q) m)

theorem sourceCapRows_eq_cl (μ : X) (P Q : List (Letter I)) (i : I) (m : ℕ) :
    sourceCapRows (Sc := Sc) μ P Q i m =
      cl D Sc μ (P ++ up i :: dn i :: Q) (P ++ Q) ((epsL i m).map (whL P Q)) := by
  simp only [sourceCapRows, eLM, plcW_apply, plcL_cl]
  exact cl_cast _ (by simp) (by simp)

theorem sourceCapRows_mem_parity (μ : X) (P Q : List (Letter I)) (i : I) (m : ℕ) :
    sourceCapRows (Sc := Sc) μ P Q i m ∈
      homPar D Sc μ (P ++ up i :: dn i :: Q) (P ++ Q) ((m : ZMod 2) * D.parity i) := by
  rw [sourceCapRows_eq_cl]
  simpa only [parsum_map_whL, parsum_epsL] using
    cl_mem_homPar' (D := D) (Sc := Sc) μ (P ++ up i :: dn i :: Q) (P ++ Q)
      ((epsL i m).map (whL P Q))

namespace SameColourSourceFrame
variable {P Q Z : List (Letter I)} {i : I} (F : SameColourSourceFrame P Q Z i)
  (cs : CScalars Sc) (μ : X)

theorem swappedPairedInclusion_eval (v : (F.residual.Labels × ℕ) →₀ SYM D k) :
    F.swapped.expansion cs μ (F.swappedPairedInclusion v) =
      F.residual.preRowsExpansion cs μ (sourceCapRows (Sc := Sc) μ P Q i) v := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single r d =>
    obtain ⟨r, b⟩ := r
    simp only [swappedPairedInclusion, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rw [F.swapped.expansion_single, F.residual.preRowsExpansion_single]
    simp only [swappedPaired, Function.Embedding.trans_apply, Equiv.toEmbedding_apply]
    rw [F.swapped_row]
    rfl

/-- Fixed finite unit column, with precisely the cap's residual twist. -/
def capResidualColumn (m : ℕ) (v : F.residual.Labels →₀ SYM D k) :
    (F.residual.Labels × ℕ) →₀ SYM D k :=
  F.residual.residualRow m (labelParityTwist
    (fun _ => (m : ZMod 2) * D.parity i) v)

/-- Actual evaluation in the complete swapped family, for arbitrary input
coefficients and arbitrary component parity. Multiplication order is inherited
from `rightColumn`, not silently commuted in the supercommutative algebra. -/
theorem capResidualColumn_eval (m : ℕ) (v : F.residual.Labels →₀ SYM D k)
    (q : ZMod 2) (d : SYM D k) :
    F.swapped.expansion cs μ (F.swappedPairedInclusion
      (MatchingTransition.rightColumn (k := k) (F.capResidualColumn m v)
        (SYM.parityTwist D k q d))) =
      MatchingBasisChoice.rightAction cs μ
        (sourceCapRows (Sc := Sc) μ P Q i m ≫ F.residual.expansion cs μ v)
        (SYM.parityTwist D k q d) := by
  rw [F.swappedPairedInclusion_eval]
  exact F.residual.preRowsExpansion_twistedColumn cs μ _ m _
    (sourceCapRows_mem_parity μ P Q i m) v q d

/-- Formal zero-index lift has exactly one cap row and no residual correction. -/
theorem capResidualColumn_single_one (m : ℕ) (r : F.residual.Labels) :
    F.capResidualColumn (D := D) (k := k) m (Finsupp.single r 1) =
      Finsupp.single (r, m) 1 := by
  simp [capResidualColumn, labelParityTwist_single, sourceParityTwist_one]

end SameColourSourceFrame
end OddMath.SKM
