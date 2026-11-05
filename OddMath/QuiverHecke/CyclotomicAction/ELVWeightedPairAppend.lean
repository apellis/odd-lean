import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing

/-! # Weighted quotient comparison for a pair of appended strands

The same-colour crossing and mate comparison in DeformedActionAssembly §5
and DeformedMatrixComparison (2), (4) needs the canonical two-strand append
square. The pair preserves the complete weighted coefficient annihilator,
including odd generators, before the two canonical induction flattenings
are attached. The final comparison with iterated induction is separate.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i j : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "K" => CyclotomicCrossingTensor.append D Sc cutoff j
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "U" => truncatedAppend D Sc cutoff N [j]

/-- Successive old appends preserve the literal full coefficient basis. -/
theorem pairAppend_oldCoefficientBasis (v : List I) (a : SKM.SYM.CoefficientIndex D) :
    (J ⋙ K).map (oldCoefficientBasis D Sc cutoff v a) =
      oldCoefficientBasis D Sc cutoff (v ++ [i] ++ [j]) a := by
  rw [Functor.comp_map, append_oldCoefficientBasis, append_oldCoefficientBasis]

/-- The literal quotient square for two successive appends; no list-word
reassociation or content equivalence is inserted. -/
theorem pairAppend_truncate : (J ⋙ K) ⋙ Q = Q ⋙ (T ⋙ U) := by
  refine Functor.hext (F := (J ⋙ K) ⋙ Q) (G := Q ⋙ (T ⋙ U)) (fun _ => rfl) ?_
  intro v w f
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
  rfl

private theorem coefficient_slide_object
    {v w : OldCategory D Sc cutoff} (a : SKM.SYM.CoefficientIndex D) (g : v ⟶ w) :
    g ≫ oldCoefficientBasis D Sc cutoff w.word a =
      oldCoefficientBasis D Sc cutoff v.word a ≫ twist k (a.2.card : ZMod 2) g := by
  cases v
  cases w
  exact oldCoefficientBasis_slide D Sc cutoff _ _ a g

private theorem induced_kills_of_coefficient_image
    (L : OldCategory D Sc cutoff ⥤ OldCategory D Sc cutoff)
    [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (hL : ∀ (v : OldCategory D Sc cutoff) (a : SKM.SYM.CoefficientIndex D),
      L.map (oldCoefficientBasis D Sc cutoff v.word a) =
        oldCoefficientBasis D Sc cutoff (L.obj v).word a)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    KillsWeightedCoefficients D Sc cutoff N (BalancedInduction.induced L M) := by
  intro w a ha
  change BalancedInduction.postcompose L M.toFunctor
    (oldCoefficientBasis D Sc cutoff w a) = 0
  apply BalancedInduction.hom_ext
  intro v g b
  rw [BalancedInduction.postcompose_tensor, coefficient_slide_object, ← hL v a,
    BalancedInduction.balance]
  have hz : M.toFunctor.map (oldCoefficientBasis D Sc cutoff v.word a) = 0 := hM v.word a ha
  rw [hz, LinearMap.zero_apply]
  exact BalancedInduction.tensor_zero_right L M.toFunctor v _

/-- Induction along the successive-append functor preserves the exact
weighted coefficient annihilator. The input is any annihilated old module. -/
theorem pairInduced_killsWeightedCoefficients
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    KillsWeightedCoefficients D Sc cutoff N (BalancedInduction.induced (J ⋙ K) M) :=
  induced_kills_of_coefficient_image D Sc cutoff N (J ⋙ K)
    (fun v a => pairAppend_oldCoefficientBasis D Sc cutoff i j v.word a) M hM

section Comparison
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "JP" => J ⋙ K
local notation "TP" => T ⋙ U
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "FP" => BalancedInduction.induced JP RM
local notation "hFP" => pairInduced_killsWeightedCoefficients D Sc cutoff N i j RM
  (weightedRestriction_kills D Sc cutoff N M)

private def pairQuotientCounit : (BalancedInduction.induction Q).obj RM ⟶ M :=
  (quotientInductionCounitIso D Sc cutoff N M).hom

local notation "P" => BalancedInduction.squareLinear JP Q Q TP
  (pairAppend_truncate D Sc cutoff N i j) RM M (pairQuotientCounit D Sc cutoff N M)

end Comparison

end OddMath.QuiverHecke.ELVOld
