import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTripleLastPairComparison

/-! # Triple comparison through a pair at a specified output block

Brundan--Ellis (1.9), multicolour suffix transport. Retain the common
first predecessor and specified final block when the last two colours
are swapped. Both paths use their already selected charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)
  (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₃)
  (hε : blockSucc₂ D i j Λ h₂ h₃ (blockSucc D Λ l h₁ β) = ε)
local notation "β₁" => blockSucc D Λ l h₁ β
local notation "E₁" => elvEFunctor D Sc cutoff bound l Λ h₁
local notation "R₁" => Superfunctor.toFunctor (elvBlockEval D Sc cutoff bound Λ β₁)
local notation "R" => Superfunctor.toFunctor (elvBlockEval D Sc cutoff bound Λ β)
local notation "J" => Superfunctor.toFunctor (elvBlockInd D Sc cutoff bound l Λ h₁ β)
local notation "hc₁" => elvBlockSucc_content_eq D l Λ h₁ β
local notation "hQ" => elvWeightPair_content_eq D i j Λ h₂ h₃ β₁ ε hε
local notation "hT" => elvWeightTriple_content_eq D i j l Λ h₁ h₂ h₃ β ε hε
local notation "Q" => contentInductionTo D Sc cutoff bound (Subtype.val β₁) [j,i] (Subtype.val ε) hQ
local notation "L" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [l] (Subtype.val β₁) hc₁
  [j,i] (Subtype.val ε) hQ hT
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β ε hε
local notation "C₂" => elvWeightPairComparison D Sc cutoff bound i j Λ h₂ h₃ β₁ ε hε
local notation "hv" => elvEFunctor_blockSucc_eval D Sc cutoff bound l Λ h₁ β

/-- Native component, retaining the first-value dispatch under the chosen pair-word induction. -/
theorem elvWeightTripleComparison_lastBlock_hom
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (C₃).hom.app M = (C₂).hom.app ((E₁).obj M) ≫
      (Q).map ((eqToIso hv).hom.app M) ≫ (L).hom.app (M β) := by
  cases hε
  exact elvWeightTripleComparison_pairLast_hom D Sc cutoff bound i j l Λ h₁ h₂ h₃ β M

end OddMath.QuiverHecke.ELVOld
