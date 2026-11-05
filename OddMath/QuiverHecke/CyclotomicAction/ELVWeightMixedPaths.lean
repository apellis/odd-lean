import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPrefixComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuffixComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentUncorrectedBraid

/-! # The repeated-outer braid paths in common triple charts

Brundan--Ellis (1.9). All six given crossing maps retain their actual
intermediate weight blocks and independently selected comparison isos.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem compose_square {C : Type*} [Category* C]
    {X₀ X₁ X₂ W₀ W₁ W₂ : C}
    (e₀ : X₀ ⟶ W₀) (e₁ : X₁ ⟶ W₁) (e₂ : X₂ ⟶ W₂)
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (a : W₀ ⟶ W₁) (b : W₁ ⟶ W₂)
    (hf : f ≫ e₁ = e₀ ≫ a) (hg : g ≫ e₂ = e₁ ≫ b) :
    (f ≫ g) ≫ e₂ = e₀ ≫ (a ≫ b) := by
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]
private theorem path_difference_square {C : Type*} [Category* C] [Preadditive C]
    {X₀ X₁ X₂ W₀ W₁ W₂ : C}
    (e₀ : X₀ ⟶ W₀) (e₁ : X₁ ⟶ W₁) (e₂ : X₂ ⟶ W₂)
    (a₀ : X₀ ⟶ X₁) (a₁ : End X₁) (a₂ : X₁ ⟶ X₀)
    (b₀ : X₀ ⟶ X₂) (b₁ : End X₂) (b₂ : X₂ ⟶ X₀)
    (c₀ : W₀ ⟶ W₁) (c₁ : End W₁) (c₂ : W₁ ⟶ W₀)
    (d₀ : W₀ ⟶ W₂) (d₁ : End W₂) (d₂ : W₂ ⟶ W₀)
    (ha₀ : a₀ ≫ e₁ = e₀ ≫ c₀) (ha₁ : a₁ ≫ e₁ = e₁ ≫ c₁)
    (ha₂ : a₂ ≫ e₀ = e₁ ≫ c₂) (hb₀ : b₀ ≫ e₂ = e₀ ≫ d₀)
    (hb₁ : b₁ ≫ e₂ = e₂ ≫ d₁) (hb₂ : b₂ ≫ e₀ = e₂ ≫ d₂) :
    (a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂) ≫ e₀ =
      e₀ ≫ (c₀ ≫ c₁ ≫ c₂ - d₀ ≫ d₁ ≫ d₂) := by
  have ha := compose_square e₀ e₁ e₀ a₀ (a₁ ≫ a₂) c₀ (c₁ ≫ c₂) ha₀
    (compose_square e₁ e₁ e₀ a₁ a₂ c₁ c₂ ha₁ ha₂)
  have hb := compose_square e₀ e₂ e₀ b₀ (b₁ ≫ b₂) d₀ (d₁ ≫ d₂) hb₀
    (compose_square e₂ e₂ e₀ b₁ b₂ d₁ d₂ hb₁ hb₂)
  rw [Preadditive.sub_comp, ha, hb, Preadditive.comp_sub]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "a₀" => elvWeightSuffixCross D Sc cutoff bound i j i Λ hab hbc hcd hbe hed
local notation "a₁" => elvWeightPrefixCross D Sc cutoff bound j i i Λ hab hbe hab hbe hed
local notation "a₂" => elvWeightSuffixCross D Sc cutoff bound j i i Λ hab hbe hed hbc hcd
local notation "b₀" => elvWeightPrefixCross D Sc cutoff bound i j i Λ hab hbc haf hfc hcd
local notation "b₁" => elvWeightSuffixCross D Sc cutoff bound i i j Λ haf hfc hcd hfc hcd
local notation "b₂" => elvWeightPrefixCross D Sc cutoff bound i i j Λ haf hfc hab hbc hcd

variable (β : WeightBlocks D Λ a)
local notation "β₁" => blockSucc D Λ i hab β
local notation "δ" => blockSucc₂ D j i Λ hab hbc β
local notation "ε" => elvBlockSucc₃ D i j i Λ hab hbc hcd β
local notation "hA" => blockSucc₂_swap D i j Λ hbc hcd hbe hed (β := β₁) rfl
local notation "hB" => elvBlockSucc₃_eq_of_pair D i i j Λ haf hfc hcd β δ ε
  (blockSucc₂_swap D j i Λ hab hbc haf hfc rfl) rfl
local notation "h₀" => elvBlockTriple_content_eq D i j i Λ hab hbc hcd β
local notation "h₁" => elvWeightTriple_content_eq D j i i Λ hab hbe hed β ε hA
local notation "h₂" => elvWeightTriple_content_eq D i i j Λ haf hfc hcd β ε hB
local notation "C₀" => elvWeightTripleComparison D Sc cutoff bound i j i Λ hab hbc hcd β ε rfl
local notation "C₁" => elvWeightTripleComparison D Sc cutoff bound j i i Λ hab hbe hed β ε hA
local notation "C₂" => elvWeightTripleComparison D Sc cutoff bound i i j Λ haf hfc hcd β ε hB
local notation "c₀" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₁ h₀
  (contentNormalizedRight_mem D Sc i i j)) (D.parity i * D.parity j)
local notation "c₁" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₁ h₁
  (contentNormalizedLeft_mem D Sc i i j)) (D.parity i * D.parity i)
local notation "c₂" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₀ h₁
  (contentNormalizedRight_mem D Sc i j i)) (D.parity j * D.parity i)
local notation "d₀" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₂ h₀
  (contentNormalizedLeft_mem D Sc j i i)) (D.parity j * D.parity i)
local notation "d₁" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₂ h₂
  (contentNormalizedRight_mem D Sc j i i)) (D.parity i * D.parity i)
local notation "d₂" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₀ h₂
  (contentNormalizedLeft_mem D Sc i j i)) (D.parity i * D.parity j)

/-- Both paths of the prescribed weight braid intertwine through the same
source chart and the two independently chosen intermediate charts. -/
theorem elvWeightMixedPaths_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    ((a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε -
      (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε) ≫ (C₀).hom.app M =
    (C₀).hom.app M ≫
      (c₀ (M β) ≫ c₁ (M β) ≫ c₂ (M β) - d₀ (M β) ≫ d₁ (M β) ≫ d₂ (M β)) := by
  apply path_difference_square ((C₀).hom.app M) ((C₁).hom.app M) ((C₂).hom.app M)
    ((a₀).total M ε) ((a₁).total M ε) ((a₂).total M ε)
    ((b₀).total M ε) ((b₁).total M ε) ((b₂).total M ε)
    (c₀ (M β)) (c₁ (M β)) (c₂ (M β)) (d₀ (M β)) (d₁ (M β)) (d₂ (M β))
  · exact elvWeightSuffixCross_comparison D Sc cutoff bound i j i Λ hab hbc hcd hbe hed β ε rfl M
  · exact elvWeightPrefixCross_comparison D Sc cutoff bound j i i Λ hab hbe hab hbe hed
      β (blockSucc₂ D i i Λ hab hbe β) ε rfl hA M
  · exact elvWeightSuffixCross_comparison D Sc cutoff bound j i i Λ hab hbe hed hbc hcd β ε hA M
  · exact elvWeightPrefixCross_comparison D Sc cutoff bound i j i Λ hab hbc haf hfc hcd β δ ε rfl rfl M
  · exact elvWeightSuffixCross_comparison D Sc cutoff bound i i j Λ haf hfc hcd hfc hcd β ε hB M
  · exact elvWeightPrefixCross_comparison D Sc cutoff bound i i j Λ haf hfc hab hbc hcd β δ ε
      (blockSucc₂_swap D j i Λ hab hbc haf hfc rfl) rfl M

end OddMath.QuiverHecke.ELVOld
