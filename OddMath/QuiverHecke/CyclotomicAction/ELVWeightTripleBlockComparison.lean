import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTriplePairComparison

/-! # Triple comparisons at common stored predecessor blocks

Brundan--Ellis (1.9), multicolour triple transport. Swapped first pairs
share their actual second predecessor block while their successor
constructors have different orders. Retain that common block explicitly
in the already selected triple and pair comparisons.
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
  (β : WeightBlocks D Λ x₀) (δ : WeightBlocks D Λ x₂) (ε : WeightBlocks D Λ x₃)
  (hδ : blockSucc₂ D j l Λ h₁ h₂ β = δ)
  (hε : blockSucc D Λ i h₃ δ = ε)

include hδ hε in
/-- A common actual pair block supplies the selected triple predecessor witness. -/
theorem elvBlockSucc₃_eq_of_pair : elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε :=
  (congrArg (blockSucc D Λ i h₃) hδ).trans hε

include hε in
/-- The literal last-content equality at the chosen common block. -/
theorem elvBlockSucc_content_eq_of_eq : δ.1 + ([i] : Multiset I) = ε.1 :=
  (elvBlockSucc_content_eq D i Λ h₃ δ).trans (congrArg Subtype.val hε)

/-- Outer dispatch uses the actual common pair coordinate before flattening. -/
theorem elvEFunctor_comp₃_pairBlock :
    (elvEFunctor D Sc cutoff bound l Λ h₁ ⋙ elvEFunctor D Sc cutoff bound j Λ h₂) ⋙
      (elvInductionComponent D Sc cutoff bound i Λ h₃ ε).toFunctor =
    (elvEFunctor D Sc cutoff bound l Λ h₁ ⋙
      (elvInductionComponent D Sc cutoff bound j Λ h₂ δ).toFunctor) ⋙
      contentInductionTo D Sc cutoff bound δ.1 [i] ε.1
        (elvBlockSucc_content_eq_of_eq D i Λ h₃ δ ε hε) := by
  cases hε
  rw [elvInductionComponent_blockSucc]
  rfl

local notation "hc" => elvBlockSucc_content_eq_of_eq D i Λ h₃ δ ε hε
local notation "hp" => elvWeightPair_content_eq D j l Λ h₁ h₂ β δ hδ
local notation "ht" => elvWeightTriple_content_eq D i j l Λ h₁ h₂ h₃ β ε
  (elvBlockSucc₃_eq_of_pair D i j l Λ h₁ h₂ h₃ β δ ε hδ hε)
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β ε
  (elvBlockSucc₃_eq_of_pair D i j l Λ h₁ h₂ h₃ β δ ε hδ hε)
local notation "C₂" => elvWeightPairComparison D Sc cutoff bound j l Λ h₁ h₂ β δ hδ
local notation "R" => Superfunctor.toFunctor (elvBlockEval D Sc cutoff bound Λ β)
local notation "U" => contentInductionTo D Sc cutoff bound (Subtype.val δ) [i] (Subtype.val ε) hc
local notation "Q" => contentInductionTo D Sc cutoff bound (Subtype.val β) [l,j] (Subtype.val δ) hp
local notation "L" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [l,j] (Subtype.val δ)
  hp [i] (Subtype.val ε) hc ht

/-- The same selected factorization on native module components. -/
theorem elvWeightTripleComparison_pairBlock_hom
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (C₃).hom.app M =
      (eqToIso (elvEFunctor_comp₃_pairBlock D Sc cutoff bound i j l Λ h₁ h₂ h₃ δ ε hε)).hom.app M ≫
        (U).map ((C₂).hom.app M) ≫ (L).hom.app (M β) := by
  cases hδ
  cases hε
  exact elvWeightTripleComparison_pairFirst_hom D Sc cutoff bound i j l Λ h₁ h₂ h₃ β M

end OddMath.QuiverHecke.ELVOld
