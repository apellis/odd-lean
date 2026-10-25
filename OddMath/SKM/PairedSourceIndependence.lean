import OddMath.SKM.PairedSourceUpwardIndependence
import OddMath.SKM.PairedSourceNormalization

/-! Triangular conversion from downward cap dots to upward cap dots and
independence of the completed paired source family. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

theorem sourceUpwardCap_mem_parity (cs : CScalars Sc) (μ : X)
    (P Q : List (Letter I)) (i : I) (b : ℕ) :
    sourceUpwardCap cs μ P Q i b ∈
      homPar D Sc μ (P ++ dn i :: up i :: Q) (P ++ Q)
        ((b : ZMod 2) * D.parity i + ipar D i (wt D μ Q)) := by
  have hp (n : ℕ) : cpow (uRM D Sc i (wt D μ Q)) n ∈
      homPar D Sc (wt D μ Q) [dn i, up i] [dn i, up i] ((n : ZMod 2) * D.parity i) := by
    induction n with
    | zero =>
      simpa only [cpow_zero, Nat.cast_zero, zero_mul, parsum_nil, cl_nil] using
        cl_mem_homPar' (D := D) (Sc := Sc) (wt D μ Q) [dn i, up i] [dn i, up i] []
    | succ n ih =>
      rw [cpow_succ]
      have hd : uRM D Sc i (wt D μ Q) ∈
          homPar D Sc (wt D μ Q) [dn i, up i] [dn i, up i] (D.parity i) := by
        simpa only [parsum_dotsL, Nat.cast_one, one_mul] using
          cl_mem_homPar' (D := D) (Sc := Sc) (wt D μ Q) [dn i, up i] [dn i, up i]
            (dotsL [dn i] i [] 1)
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using comp_mem_homPar ih hd
  have H := plcL_mem μ P Q (comp_mem_homPar (hp b) (epsP_mem cs i (wt D μ Q)))
  rw [sourceUpwardCap, plcW_apply]
  simpa only [parsum_nil, zero_add, add_zero] using
    comp_mem_homPar (cl_mem_homPar' (D := D) (Sc := Sc) μ
      (P ++ dn i :: up i :: Q) (P ++ [dn i, up i] ++ Q) [])
      (comp_mem_homPar H (cl_mem_homPar' (D := D) (Sc := Sc) μ
        (P ++ [] ++ Q) (P ++ Q) []))

namespace SameColourSourceFrame
variable {P Q Z : List (Letter I)} {i : I} (F : SameColourSourceFrame P Q Z i)
  (cs : CScalars Sc) (μ : X)

def normalizationScalar (i : I) (b : ℕ) : k :=
  (source_cap_downward_triangular cs i (wt D μ Q) b).choose

def normalizationLoop (i : I) (b : ℕ) : End ((pres D Sc).obj (ob D (wt D μ Q) [])) :=
  (source_cap_downward_triangular cs i (wt D μ Q) b).choose_spec.choose

theorem normalization_spec (i : I) (b : ℕ) :
    IsUnit (normalizationScalar (Q := Q) cs μ i b) ∧
    (b = 0 → normalizationLoop (Q := Q) cs μ i b = 0) ∧
    cpow (dLM D Sc i (wt D μ Q)) b ≫ epsP cs i (wt D μ Q) =
      normalizationScalar (Q := Q) cs μ i b • (cpow (uRM D Sc i (wt D μ Q)) b ≫ epsP cs i (wt D μ Q)) +
      cpow (uRM D Sc i (wt D μ Q)) (b - 1) ≫ epsP cs i (wt D μ Q) ≫
        normalizationLoop (Q := Q) cs μ i b :=
  (source_cap_downward_triangular cs i (wt D μ Q) b).choose_spec.choose_spec

def normalizationColumn (b : ℕ) (r : F.residual.Labels) : (F.residual.Labels × ℕ) →₀ SYM D k :=
  normalizationScalar (Q := Q) cs μ i b • Finsupp.single (r, b) 1 +
    if b = 0 then 0 else
      F.residual.residualRow (b - 1) (labelParityTwist
        (fun _ => ((b - 1 : ℕ) : ZMod 2) * D.parity i + ipar D i (wt D μ Q))
        (F.sourceLoopLift cs μ r (normalizationLoop (Q := Q) cs μ i b)))

def normalizationComparison : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    ((F.residual.Labels × ℕ) →₀ SYM D k) :=
  Finsupp.lsum k (fun r => MatchingTransition.rightColumn (k := k)
    (F.normalizationColumn cs μ r.2 r.1))

def pairedExpansion : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    ((pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q)) ⟶ (pres D Sc).obj (ob D μ Z)) :=
  (F.original.expansion cs μ).comp F.originalPairedInclusion

@[simp] theorem pairedExpansion_single (r : F.residual.Labels) (b : ℕ) (d : SYM D k) :
    F.pairedExpansion cs μ (Finsupp.single (r, b) d) =
      F.original.expansion cs μ (Finsupp.single (F.paired (b, r)) d) := by
  simp [pairedExpansion, originalPairedInclusion]

theorem normalizationColumn_eval (b : ℕ) (r : F.residual.Labels) :
    F.upwardExpansion (cs := cs) (μ := μ) (F.normalizationColumn cs μ b r) =
      xev cs μ (P ++ dn i :: up i :: Q) Z (F.original.layers (F.paired (b, r))) := by
  rw [F.original_row, (normalization_spec (Q := Q) cs μ i b).2.2,
    map_add, map_smul, Preadditive.add_comp, Linear.smul_comp, normalizationColumn, map_add, map_smul,
    F.upwardExpansion_single, MatchingBasisChoice.rightAction_one]
  congr 1
  by_cases hb : b = 0
  · rw [ite_eq_left hb, map_zero, (normalization_spec (Q := Q) cs μ i b).2.1 hb,
      Limits.comp_zero, Limits.comp_zero, map_zero, Limits.zero_comp]
  · rw [ite_eq_right hb, upwardExpansion,
      F.residual.preRowsExpansion_residualRow cs μ _ (b - 1) _
        (sourceUpwardCap_mem_parity cs μ P Q i (b - 1)), F.sourceLoopLift_eval, ← Category.assoc]
    dsimp only [sourceUpwardCap, plcAt]
    rw [sourcePlcW_comp_at μ _ _ (P ++ Q) P Q [dn i, up i] [] [] (by simp)]
    simp only [Category.assoc]

theorem normalizationComparison_eval (f : (F.residual.Labels × ℕ) →₀ SYM D k) :
    F.upwardExpansion (cs := cs) (μ := μ) (F.normalizationComparison cs μ f) =
      F.pairedExpansion cs μ f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single r d =>
    obtain ⟨r, b⟩ := r
    rw [normalizationComparison, Finsupp.lsum_single, upwardExpansion,
      F.residual.preRowsExpansion_rightColumn, ← upwardExpansion,
      F.normalizationColumn_eval, F.pairedExpansion_single, F.original.source_expansion_single]

theorem normalizationColumn_above (b m : ℕ) (r t : F.residual.Labels) (hm : b ≤ m) :
    F.normalizationColumn cs μ b r (t, m) =
      normalizationScalar (Q := Q) cs μ i b • Finsupp.single (r, b) (1 : SYM D k) (t, m) := by
  classical
  rw [normalizationColumn, Finsupp.add_apply, Finsupp.smul_apply]
  by_cases hb : b = 0
  · simp [hb]
  · rw [ite_eq_right hb, F.residual.residualRow_apply_ne (b - 1) m (by omega), add_zero]

theorem normalizationComparison_injective : Function.Injective (F.normalizationComparison cs μ) := by
  classical
  have hz (f : (F.residual.Labels × ℕ) →₀ SYM D k) (hf : F.normalizationComparison cs μ f = 0) : f = 0 := by
    apply OrientedReduction.eq_zero_of_crossing_dot_coefficients Prod.snd (fun _ => 0)
      (fun row col d => F.normalizationColumn cs μ col.2 col.1 row * d)
      _ (fun _ _ _ _ h => by omega) _ _ f
    · intro row
      have H := congrArg (fun v : (F.residual.Labels × ℕ) →₀ SYM D k => v row) hf
      simpa [normalizationComparison, Finsupp.lsum_apply, Finsupp.sum,
        Finsupp.finsetSum_apply, MatchingTransition.rightColumn] using H
    · intro row col d hc
      rw [F.normalizationColumn_above cs μ col.2 row.2 col.1 row.1 (by omega)]
      have hn : col ≠ row := by intro he; subst col; omega
      simp [hn]
    · intro row col d hc _ hn
      rw [F.normalizationColumn_above cs μ col.2 row.2 col.1 row.1 (by omega)]
      simp [hn]
    · intro row d hd
      rw [F.normalizationColumn_above cs μ row.2 row.2 row.1 row.1 le_rfl] at hd
      simp only [Finsupp.single_eq_same, smul_mul_assoc, one_mul] at hd
      exact (normalization_spec (Q := Q) cs μ i row.2).1.smul_eq_zero.mp hd
  intro f g he
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, he, sub_self]

theorem pairedExpansion_injective
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (hB : Function.Injective (F.residual.expansion cs μ)) :
    Function.Injective (F.pairedExpansion cs μ) := by
  intro f g he
  apply F.normalizationComparison_injective cs μ
  apply F.upwardExpansion_injective hG hB
  rw [F.normalizationComparison_eval, F.normalizationComparison_eval, he]

#print axioms pairedExpansion_injective
end SameColourSourceFrame
end OddMath.SKM
