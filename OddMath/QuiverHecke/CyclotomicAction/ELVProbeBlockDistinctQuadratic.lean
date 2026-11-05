import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridQuadratic
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeBlockDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ELVOldDistinctQuadratic

/-! # The original-parameter quadratic on selected OLD probe block pairs

Brundan–Ellis (1.7) and DeformedActionAssembly §6 (9): the two selected
positive rectangular crossings compose to the original ordered signed
polynomial, through the prescribed common-target induction chart. The
literal untruncated OLD relation supplies the quadratic, not an action premise.
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
local notation "J" => probeOldBlockAppend D Sc' m i Λ h₃
local notation "K" => probeOldBlockAppend D Sc' m j Λ h₁
local notation "L" => (fun β ε hε => probeOldPairUpperAppend D Sc' m j i Λ h₃ h₄ β ε (sw hε))
local notation "U" => probeOldPairUpperAppend D Sc' m i j Λ h₁ h₂
local notation "hc" => probeOldBlockDistinctCrossArrow_supernatural D Sc' m i j Λ h₁ h₂ h₃ h₄

/-- The literal original-Sc polynomial on the source pair, at its stored target. -/
def probeOldBlockPairQuadraticArrow (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (s : OldContentCategory D Sc' (probeCutoff D m) β.1.toList) :
    End (((K β) ⋙ (U β ε hε)).obj s) :=
  Distinct.signedQuadraticComponent D Sc (probeCutoff D m) j i s.obj

/-- No quadratic is assumed: this is the literal old source equation. -/
theorem probeOldBlockPairQuadraticArrow_source (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (s : OldContentCategory D Sc' (probeCutoff D m) β.1.toList) :
    sign k (D.parity i * D.parity j) •
      (probeOldBlockDistinctCrossArrow D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε) s ≫
        probeOldBlockDistinctCrossArrow D Sc' m i j Λ h₁ h₂ h₃ h₄ β ε hε s) =
      probeOldBlockPairQuadraticArrow D Sc m i j Λ h₁ h₂ β ε hε s := by
  exact Distinct.crossComponent_parameterUntwist D Sc (probeCutoff D m) hij s.obj

private theorem reverseCross_supernatural (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    IsSupernatural k (D.parity i * D.parity j)
      (probeOldBlockDistinctCrossArrow D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε)) := by
  simpa only [mul_comm] using
    probeOldBlockDistinctCrossArrow_supernatural D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε)

include h₃ h₄ in
/-- The original polynomial is an even supernatural source endomorphism. -/
theorem probeOldBlockPairQuadraticArrow_supernatural (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    IsSupernatural k 0 (probeOldBlockPairQuadraticArrow D Sc m i j Λ h₁ h₂ β ε hε) :=
  signedQuadratic_supernatural
    (reverseCross_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε) (hc β ε hε)
    (probeOldBlockPairQuadraticArrow_source D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε)

/-- The selected pair polynomial uses exactly its original flattening and inverse. -/
def probeOldBlockPairQuadratic (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : Superfunctor k (OldContentCategory D Sc' (probeCutoff D m) β.1.toList) (SVec k)) :
    End (induced (U β ε hε) (induced (K β) N)) :=
  (inductionComp (K β) (U β ε hε)).hom.app N ≫
    transformComponent
      (probeOldBlockPairQuadraticArrow_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε) N ≫
    (inductionComp (K β) (U β ε hε)).inv.app N

/-- The actual two rectangular crossings compose to that original-parameter polynomial. -/
theorem probeOldBlockDistinctCross_quadratic_eq (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : ProbeCanonicalModules D Sc' m β.1) :
    ((probeOldBlockDistinctCross D Sc' m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom ≫
      ((probeOldBlockDistinctCross D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε)).total N).hom =
      probeOldBlockPairQuadratic D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε N.obj := by
  rw [probeOldBlockDistinctCross_total, probeOldBlockDistinctCross_total]
  have hr := rectangularCrossComponent_signed_quadratic_of_parity (J β) (K β) (L β ε hε) (U β ε hε)
    (hc β ε hε)
    (probeOldBlockPairQuadraticArrow_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε)
    (probeOldBlockPairQuadraticArrow_source D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε)
    (probeOldBlockDistinctCrossArrow_supernatural D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε))
    (mul_comm _ _) N.obj
  unfold probeOldBlockPairQuadratic
  exact hr
end OddMath.QuiverHecke
