import OddMath.QuiverHecke.CyclotomicAction.ELVProbeBlockDistinctQuadratic
import OddMath.QuiverHecke.CyclotomicAction.ELVOldPairPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionPairPolynomialMaps

/-! # Original-Sc quadratic in the independent selected OLD probe dots

Brundan–Ellis (1.7), DeformedActionAssembly §6 (9): the selected block
crossing square is the ordered polynomial in the separately chosen inner
and outer dot maps. The actual OLD quotient quadratic supplies every
source relation, and the original parameters are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Sc'" => parameterTwist D Sc
local notation "sw" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄
local notation "K" => probeOldBlockAppend D Sc' m j Λ h₁
local notation "U" => probeOldPairUpperAppend D Sc' m i j Λ h₁ h₂
local notation "hd₁" => probeOldBlockDotArrow_supernatural D Sc' m j Λ h₁
private theorem pairUpperDot_supernatural
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    IsSupernatural k (D.parity i)
      (probeAppendToDot D Sc' m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
        (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)) :=
  probeAppendToDot_supernatural D Sc' m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
    (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)
local notation "hd₂" => pairUpperDot_supernatural D Sc m i j Λ h₁ h₂

/-- The selected source polynomial uses the independent lower and upper OLD dots. -/
theorem probeOldBlockPairQuadraticArrow_pairDots
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (s : OldContentCategory D Sc' (probeCutoff D m) β.1.toList) :
    probeOldBlockPairQuadraticArrow D Sc m i j Λ h₁ h₂ β ε hε s =
      elvSignedPairQuadEval D Sc (R := End (((K β) ⋙ (U β ε hε)).obj s)) j i
        ((U β ε hε).map (probeOldBlockDotArrow D Sc' m j Λ h₁ β s))
        (probeAppendToDot D Sc' m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
          (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε) ((K β).obj s)) := by
  exact Distinct.signedQuadraticComponent_pairDots D Sc (probeCutoff D m) j i s.obj

include h₃ h₄ in
/-- The original polynomial of the independent source dots is even supernatural. -/
private theorem pairDots_supernatural (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    IsSupernatural k 0 (fun s => elvSignedPairQuadEval D Sc
      (R := End (((K β) ⋙ (U β ε hε)).obj s)) j i
      ((U β ε hε).map (probeOldBlockDotArrow D Sc' m j Λ h₁ β s))
      (probeAppendToDot D Sc' m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
        (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε) ((K β).obj s))) := by
  have h := probeOldBlockPairQuadraticArrow_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε
  change IsSupernatural k 0 (fun s => probeOldBlockPairQuadraticArrow D Sc m i j Λ h₁ h₂ β ε hε s) at h
  simpa only [probeOldBlockPairQuadraticArrow_pairDots] using h

/-- The selected flattening transports the source polynomial to the independent module dots. -/
theorem probeOldBlockPairQuadratic_pairDots (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : Superfunctor k (OldContentCategory D Sc' (probeCutoff D m) β.1.toList) (SVec k)) :
    probeOldBlockPairQuadratic D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε N =
      orderedPairOperatorPolynomial (R := End (induced (U β ε hε) (induced (K β) N))) D Sc j i
        ((induction (U β ε hε)).map (dotEnd (K β) (hd₁ β) N))
        (dotEnd (U β ε hε) (hd₂ β ε hε) ((induction (K β)).obj N)) := by
  have hP := pairDots_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε
  have he := transformComponent_congr_pointwise ((K β) ⋙ (U β ε hε))
    (probeOldBlockPairQuadraticArrow_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε) hP
    (probeOldBlockPairQuadraticArrow_pairDots D Sc m i j Λ h₁ h₂ β ε hε) N
  unfold probeOldBlockPairQuadratic
  rw [he]
  exact inductionComp_pairPolynomial D Sc j i (K β) (U β ε hε) (hd₁ β) (hd₂ β ε hε) hij.symm hP N

/-- The actual selected crossing square is the original-Sc polynomial of the two chosen dots. -/
theorem probeOldBlockDistinctCross_quadratic_dots (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : ProbeCanonicalModules D Sc' m β.1) :
    ((probeOldBlockDistinctCross D Sc' m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom ≫
      ((probeOldBlockDistinctCross D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε)).total N).hom =
      orderedPairOperatorPolynomial (R := End (induced (U β ε hε) (induced (K β) N.obj))) D Sc j i
        (((probeOldBlockPairInnerDotTo D Sc' m i j Λ h₁ h₂ β ε hε).total N).hom)
        (((probeOldBlockPairOuterDotTo D Sc' m i j Λ h₁ h₂ β ε hε).total N).hom) := by
  rw [probeOldBlockDistinctCross_quadratic_eq,
    probeOldBlockPairInnerDotTo_total, probeOldBlockPairOuterDotTo_total]
  exact probeOldBlockPairQuadratic_pairDots D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε N.obj
end OddMath.QuiverHecke
