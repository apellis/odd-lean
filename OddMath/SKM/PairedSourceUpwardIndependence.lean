import OddMath.SKM.PairedSourceDetection

/-! All-height independence with upward cap dots, before the triangular
conversion of the completed source serializer. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

def sourceUpwardCap (cs : CScalars Sc) (μ : X) (P Q : List (Letter I)) (i : I) (b : ℕ) :
    (pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q)) ⟶
      (pres D Sc).obj (ob D μ (P ++ Q)) :=
  plcW μ (P ++ dn i :: up i :: Q) (P ++ Q) P Q [dn i, up i] []
    (cpow (uRM D Sc i (wt D μ Q)) b ≫ epsP cs i (wt D μ Q))

def sourceCupRows (μ : X) (P Q : List (Letter I)) (i : I) (s : ℕ) :
    (pres D Sc).obj (ob D μ (P ++ Q)) ⟶
      (pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q)) :=
  plcW μ (P ++ Q) (P ++ dn i :: up i :: Q) P Q [] [dn i, up i]
    (hLM D Sc i (wt D μ Q) s)

theorem sourceCupRows_mem_parity (μ : X) (P Q : List (Letter I)) (i : I) (s : ℕ) :
    sourceCupRows (Sc := Sc) μ P Q i s ∈
      homPar D Sc μ (P ++ Q) (P ++ dn i :: up i :: Q) ((s : ZMod 2) * D.parity i) := by
  have H : sourceCupRows (Sc := Sc) μ P Q i s =
      cl D Sc μ (P ++ Q) (P ++ dn i :: up i :: Q) ((etaL i s).map (whL P Q)) := by
    simp only [sourceCupRows, hLM, plcW_apply, plcL_cl]
    exact cl_cast _ (by simp) (by simp)
  rw [H]
  simpa only [parsum_map_whL, parsum_etaL] using
    cl_mem_homPar' (D := D) (Sc := Sc) μ (P ++ Q) (P ++ dn i :: up i :: Q)
      ((etaL i s).map (whL P Q))

theorem sourceCupRows_rightAction (cs : CScalars Sc) (μ : X)
    (P Q Z : List (Letter I)) (i : I) (s : ℕ)
    (f : (pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q)) ⟶ (pres D Sc).obj (ob D μ Z))
    (d : SYM D k) :
    sourceCupRows (Sc := Sc) μ P Q i s ≫ MatchingBasisChoice.rightAction cs μ f d =
      MatchingBasisChoice.rightAction cs μ (sourceCupRows (Sc := Sc) μ P Q i s ≫ f)
        (SYM.parityTwist D k ((s : ZMod 2) * D.parity i) d) := by
  dsimp only [MatchingBasisChoice.rightAction]
  rw [← Category.assoc, ← source_target_twist cs μ (sourceCupRows_mem_parity μ P Q i s),
    Category.assoc]

namespace SameColourSourceFrame
variable {cs : CScalars Sc} {μ : X} {P Q Z : List (Letter I)} {i : I}
  (F : SameColourSourceFrame P Q Z i)

def upwardExpansion : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    ((pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q)) ⟶ (pres D Sc).obj (ob D μ Z)) :=
  F.residual.preRowsExpansion cs μ (sourceUpwardCap cs μ P Q i)

def nonnegativeComparison (N : ℕ) : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    ((F.residual.Labels × ℕ) →₀ SYM D k) :=
  Finsupp.lsum k (fun r => (MatchingTransition.rightColumn (k := k)
    (F.sourceNonnegativeColumn cs μ N r.2 r.1)).comp (SYM.parityTwist D k (D.parity i)))

def negativeComparison (N : ℕ) : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    ((F.residual.Labels × ℕ) →₀ SYM D k) :=
  Finsupp.lsum k (fun r => (MatchingTransition.rightColumn (k := k)
    (F.sourceNegativeColumn cs μ N r.2 r.1)).comp (SYM.parityTwist D k (D.parity i)))

def cupComparison (N s : ℕ) : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    (F.residual.Labels →₀ SYM D k) :=
  Finsupp.lsum k (fun r => (MatchingTransition.rightColumn (k := k)
    (F.sourceCupColumn cs μ N r.2 s r.1)).comp
      (SYM.parityTwist D k ((s : ZMod 2) * D.parity i)))

@[simp] theorem upwardExpansion_single (r : F.residual.Labels) (b : ℕ) (d : SYM D k) :
    F.upwardExpansion (cs := cs) (μ := μ) (Finsupp.single (r, b) d) =
      MatchingBasisChoice.rightAction cs μ
        (sourceUpwardCap cs μ P Q i b ≫ xev cs μ (P ++ Q) Z (F.residual.layers r)) d := by
  rw [upwardExpansion, F.residual.preRowsExpansion_single]
  rfl

theorem nonnegativeComparison_eval (N : ℕ) (hN : D.h i (wt D μ Q) = (N : ℤ))
    (f : (F.residual.Labels × ℕ) →₀ SYM D k) :
    F.swapped.expansion cs μ (F.swappedPairedInclusion (F.nonnegativeComparison (cs := cs) (μ := μ) N f)) =
      sameColourSourceCross (Sc := Sc) μ P Q i ≫ F.upwardExpansion (cs := cs) (μ := μ) f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Preadditive.comp_add, hf, hg]
  | single r d =>
    obtain ⟨r, b⟩ := r
    rw [nonnegativeComparison, Finsupp.lsum_single, LinearMap.comp_apply,
      F.swappedPairedInclusion_eval, F.residual.preRowsExpansion_rightColumn,
      F.sourceNonnegativeColumn_eval cs μ N b r hN, F.upwardExpansion_single,
      sameColourSourceCross_rightAction]
    congr 1
    simp only [← Category.assoc]
    dsimp only [sameColourSourceCross, sourceUpwardCap]
    rw [sourcePlcW_comp_at μ _ _ (P ++ dn i :: up i :: Q) P Q
      [up i, dn i] [dn i, up i] [] (by simp)]
    simp only [Category.assoc]

theorem negativeComparison_eval (N : ℕ) (hN : -D.h i (wt D μ Q) = (N : ℤ))
    (hpos : 0 < N) (f : (F.residual.Labels × ℕ) →₀ SYM D k) :
    F.swapped.expansion cs μ (F.swappedPairedInclusion (F.negativeComparison (cs := cs) (μ := μ) N f)) =
      sameColourSourceCross (Sc := Sc) μ P Q i ≫ F.upwardExpansion (cs := cs) (μ := μ) f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Preadditive.comp_add, hf, hg]
  | single r d =>
    obtain ⟨r, b⟩ := r
    rw [negativeComparison, Finsupp.lsum_single, LinearMap.comp_apply,
      F.swappedPairedInclusion_eval, F.residual.preRowsExpansion_rightColumn,
      F.sourceNegativeColumn_eval cs μ N b r hN hpos, F.upwardExpansion_single,
      sameColourSourceCross_rightAction]
    congr 1
    simp only [← Category.assoc]
    dsimp only [sameColourSourceCross, sourceUpwardCap]
    rw [sourcePlcW_comp_at μ _ _ (P ++ dn i :: up i :: Q) P Q
      [up i, dn i] [dn i, up i] [] (by simp)]
    simp only [Category.assoc]

theorem cupComparison_eval (N s : ℕ) (hN : -D.h i (wt D μ Q) = (N : ℤ))
    (hpos : 0 < N) (f : (F.residual.Labels × ℕ) →₀ SYM D k) :
    F.residual.expansion cs μ (F.cupComparison (cs := cs) (μ := μ) N s f) =
      sourceCupRows (Sc := Sc) μ P Q i s ≫ F.upwardExpansion (cs := cs) (μ := μ) f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Preadditive.comp_add, hf, hg]
  | single r d =>
    obtain ⟨r, b⟩ := r
    rw [cupComparison, Finsupp.lsum_single, LinearMap.comp_apply,
      F.residual.expansion_rightColumn, F.sourceCupColumn_eval cs μ N b s r hN hpos,
      F.upwardExpansion_single, sourceCupRows_rightAction]
    congr 1
    simp only [← Category.assoc]
    dsimp only [sourceCupRows, sourceUpwardCap, plcAt]
    rw [sourcePlcW_comp_at μ _ _ (P ++ dn i :: up i :: Q) P Q
      [] [dn i, up i] [] (by simp)]
    simp only [Category.assoc]

theorem upwardExpansion_injective
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (hB : Function.Injective (F.residual.expansion cs μ)) :
    Function.Injective (F.upwardExpansion (cs := cs) (μ := μ)) := by
  classical
  have hz (f : (F.residual.Labels × ℕ) →₀ SYM D k) (hf : F.upwardExpansion (cs := cs) (μ := μ) f = 0) : f = 0 := by
    by_cases hh : 0 ≤ D.h i (wt D μ Q)
    · let N := (D.h i (wt D μ Q)).toNat
      have hN : D.h i (wt D μ Q) = (N : ℤ) := by dsimp [N]; omega
      have hc : F.nonnegativeComparison (cs := cs) (μ := μ) N f = 0 := by
        apply F.swappedPairedInclusion_injective
        apply hG
        rw [F.nonnegativeComparison_eval N hN, hf, Limits.comp_zero, map_zero, map_zero]
      apply F.sourceNonnegativeColumns_detect cs μ N f
      intro row
      have H := congrArg (fun v : (F.residual.Labels × ℕ) →₀ SYM D k => v (row.1, row.2 + N)) hc
      simpa [nonnegativeComparison, Finsupp.lsum_apply, Finsupp.sum,
        Finsupp.finsetSum_apply, MatchingTransition.rightColumn] using H
    · let N := (-D.h i (wt D μ Q)).toNat
      have hN : -D.h i (wt D μ Q) = (N : ℤ) := by dsimp [N]; omega
      have hpos : 0 < N := by omega
      have hc : F.negativeComparison (cs := cs) (μ := μ) N f = 0 := by
        apply F.swappedPairedInclusion_injective
        apply hG
        rw [F.negativeComparison_eval N hN hpos, hf, Limits.comp_zero, map_zero, map_zero]
      have he (s : ℕ) : F.cupComparison (cs := cs) (μ := μ) N s f = 0 := by
        apply hB
        rw [F.cupComparison_eval N s hN hpos, hf, Limits.comp_zero, map_zero]
      apply F.sourceNegativeColumns_detect cs μ N f
      intro row
      by_cases hr : row.2 < N
      · have H := congrArg (fun v : F.residual.Labels →₀ SYM D k => v row.1) (he (N - 1 - row.2))
        simpa [sourceNegativeEntry, hr, cupComparison, Finsupp.lsum_apply, Finsupp.sum,
          Finsupp.finsetSum_apply, MatchingTransition.rightColumn] using H
      · have H := congrArg (fun v : (F.residual.Labels × ℕ) →₀ SYM D k => v (row.1, row.2 - N)) hc
        simpa [sourceNegativeEntry, hr, negativeComparison, Finsupp.lsum_apply, Finsupp.sum,
          Finsupp.finsetSum_apply, MatchingTransition.rightColumn] using H
  intro f g he
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, he, sub_self]

#print axioms upwardExpansion_injective
end SameColourSourceFrame
end OddMath.SKM
