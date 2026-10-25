import OddMath.SKM.PairedTargetCaps
import OddMath.SKM.PairedTargetDetection

/-! Independence of the actual paired target sector at nonpositive height,
obtained from the complete swapped matching family's independence. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace SameColourTargetFrame
variable {cs : CScalars Sc} {μ : X} {a P Q : List (Letter I)} {i : I}
  (F : SameColourTargetFrame cs μ a P Q i)

def originalPairedInclusion : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    (F.original.Labels →₀ SYM D k) :=
  Finsupp.lmapDomain (SYM D k) k (fun r => F.paired (r.2, r.1))

def pairedExpansion : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ (P ++ up i :: dn i :: Q))) :=
  (F.original.expansion cs μ).comp F.originalPairedInclusion

def nonpositiveComparison (N : ℕ) : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    ((F.residual.Labels × ℕ) →₀ SYM D k) :=
  Finsupp.lsum k (fun r => MatchingTransition.rightColumn (k := k)
    (F.residual.targetNonpositiveColumn cs μ i N r.2 r.1))

@[simp] theorem pairedExpansion_single (r : F.residual.Labels) (b : ℕ) (d : SYM D k) :
    F.pairedExpansion (Finsupp.single (r, b) d) =
      F.original.expansion cs μ (Finsupp.single (F.paired (b, r)) d) := by
  simp [pairedExpansion, originalPairedInclusion]

theorem nonpositiveComparison_eval (N : ℕ) (hN : -D.h i (wt D μ Q) = (N : ℤ))
    (f : (F.residual.Labels × ℕ) →₀ SYM D k) :
    F.swapped.expansion cs μ
      (F.residual.pairedRowsInclusion i F.swapped F.swappedPaired (F.nonpositiveComparison N f)) =
    F.pairedExpansion f ≫ sameColourTargetCross (Sc := Sc) μ P Q i := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Preadditive.add_comp, hf, hg]
  | single r d =>
    obtain ⟨r, b⟩ := r
    rw [nonpositiveComparison, Finsupp.lsum_single, F.pairedExpansion_single]
    exact F.nonpositive_column N b r d hN

/-- The native principal coefficient map itself is injective. -/
theorem nonpositiveComparison_injective (N : ℕ) :
    Function.Injective (F.nonpositiveComparison N) := by
  have hz (f : (F.residual.Labels × ℕ) →₀ SYM D k)
      (hf : F.nonpositiveComparison N f = 0) : f = 0 := by
    apply F.residual.targetNonpositiveColumns_detect cs μ i N f
    intro row
    have H := congrArg (fun v : (F.residual.Labels × ℕ) →₀ SYM D k => v (row.1, N + row.2)) hf
    simpa [nonpositiveComparison, Finsupp.lsum_apply, Finsupp.sum,
      Finsupp.finsetSum_apply, MatchingTransition.rightColumn] using H
  intro f g he
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, he, sub_self]

/-- Nonpositive-height paired descent for complete native matching choices.
Only independence of the swapped boundary is needed for this sector. -/
theorem pairedExpansion_injective_nonpositive
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (hheight : D.h i (wt D μ Q) ≤ 0) : Function.Injective F.pairedExpansion := by
  let N := (-D.h i (wt D μ Q)).toNat
  have hN : -D.h i (wt D μ Q) = (N : ℤ) := by dsimp [N]; omega
  have hin : Function.Injective
      (F.residual.pairedRowsInclusion (D := D) (k := k) i F.swapped F.swappedPaired) := by
    apply Finsupp.mapDomain_injective
    intro r s he
    have H := F.swappedPaired.injective he
    exact Prod.ext (congrArg Prod.snd H) (congrArg Prod.fst H)
  intro f g he
  apply F.nonpositiveComparison_injective N
  apply hin
  apply hG
  rw [F.nonpositiveComparison_eval N hN, F.nonpositiveComparison_eval N hN, he]

def positiveComparison (N : ℕ) : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    ((F.residual.Labels × ℕ) →₀ SYM D k) :=
  Finsupp.lsum k (fun r => MatchingTransition.rightColumn (k := k)
    (F.residual.targetPositiveColumn cs μ i N r.2 r.1))

def capComparison (N s : ℕ) : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    (F.residual.Labels →₀ SYM D k) :=
  Finsupp.lsum k (fun r => MatchingTransition.rightColumn (k := k)
    (F.residual.targetCapColumn cs μ i N r.2 s r.1))

theorem positiveComparison_eval (N : ℕ) (hN : D.h i (wt D μ Q) = (N : ℤ))
    (hpos : 0 < N) (f : (F.residual.Labels × ℕ) →₀ SYM D k) :
    F.swapped.expansion cs μ
      (F.residual.pairedRowsInclusion i F.swapped F.swappedPaired (F.positiveComparison N f)) =
    F.pairedExpansion f ≫ sameColourTargetCross (Sc := Sc) μ P Q i := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Preadditive.add_comp, hf, hg]
  | single r d =>
    obtain ⟨r, b⟩ := r
    rw [positiveComparison, Finsupp.lsum_single, F.pairedExpansion_single]
    exact F.positive_column N b r d hN hpos

theorem capComparison_eval (N s : ℕ) (hN : D.h i (wt D μ Q) = (N : ℤ))
    (hpos : 0 < N) (f : (F.residual.Labels × ℕ) →₀ SYM D k) :
    F.residual.expansion cs μ (F.capComparison N s f) =
      F.pairedExpansion f ≫ targetCap (Sc := Sc) (μ := μ) (P := P) (Q := Q) (i := i) s := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Preadditive.add_comp, hf, hg]
  | single r d =>
    obtain ⟨r, b⟩ := r
    rw [capComparison, Finsupp.lsum_single, F.pairedExpansion_single]
    exact F.cap_column N b s r d hN hpos

/-- Positive-height paired descent. The shortened boundary is used precisely
for the low cap rows, while the swapped boundary handles all shifted rows. -/
theorem pairedExpansion_injective_positive
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (hB : Function.Injective (F.residual.expansion cs μ))
    (hheight : 0 < D.h i (wt D μ Q)) : Function.Injective F.pairedExpansion := by
  classical
  let N := (D.h i (wt D μ Q)).toNat
  have hN : D.h i (wt D μ Q) = (N : ℤ) := by dsimp [N]; omega
  have hpos : 0 < N := by omega
  have hin : Function.Injective
      (F.residual.pairedRowsInclusion (D := D) (k := k) i F.swapped F.swappedPaired) := by
    apply Finsupp.mapDomain_injective
    intro r s he
    have H := F.swappedPaired.injective he
    exact Prod.ext (congrArg Prod.snd H) (congrArg Prod.fst H)
  have hz (f : (F.residual.Labels × ℕ) →₀ SYM D k) (hf : F.pairedExpansion f = 0) : f = 0 := by
    have hc : F.positiveComparison N f = 0 := by
      apply hin
      apply hG
      rw [F.positiveComparison_eval N hN hpos, hf, Limits.zero_comp, map_zero, map_zero]
    have he (s : ℕ) : F.capComparison N s f = 0 := by
      apply hB
      rw [F.capComparison_eval N s hN hpos, hf, Limits.zero_comp, map_zero]
    apply F.residual.targetPositiveColumns_detect cs μ i N f
    intro row
    by_cases hr : row.2 < N
    · have H := congrArg (fun v : F.residual.Labels →₀ SYM D k => v row.1) (he (N - 1 - row.2))
      simpa [MatchingBasisChoice.targetPositiveEntry, hr, capComparison,
        Finsupp.lsum_apply, Finsupp.sum, Finsupp.finsetSum_apply,
        MatchingTransition.rightColumn] using H
    · have H := congrArg (fun v : (F.residual.Labels × ℕ) →₀ SYM D k => v (row.1, row.2 - N)) hc
      simpa [MatchingBasisChoice.targetPositiveEntry, hr, positiveComparison,
        Finsupp.lsum_apply, Finsupp.sum, Finsupp.finsetSum_apply,
        MatchingTransition.rightColumn] using H
  intro f g he
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, he, sub_self]

/-- All-height independence of the paired target sector of a complete frame. -/
theorem pairedExpansion_injective
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (hB : Function.Injective (F.residual.expansion cs μ)) :
    Function.Injective F.pairedExpansion := by
  by_cases hheight : 0 < D.h i (wt D μ Q)
  · exact F.pairedExpansion_injective_positive hG hB hheight
  · exact F.pairedExpansion_injective_nonpositive hG (by omega)

#print axioms pairedExpansion_injective
end SameColourTargetFrame
end OddMath.SKM
