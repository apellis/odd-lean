import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPrefixComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuffixComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentInductionTripleBraid

/-! # The six multicolour braid comparisons on the chosen weight paths

Brundan--Ellis (1.9), outside the repeated-outer correction case. All six
permutation paths keep the actual intermediate original-weight blocks.
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
private theorem braid_of_six_squares {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ X₄ X₅ W₀ W₁ W₂ W₃ W₄ W₅ : C}
    (e₀ : X₀ ≅ W₀) (e₁ : X₁ ≅ W₁) (e₂ : X₂ ≅ W₂)
    (e₃ : X₃ ≅ W₃) (e₄ : X₄ ≅ W₄) (e₅ : X₅ ≅ W₅)
    (a₀ : X₀ ⟶ X₁) (a₁ : X₁ ⟶ X₂) (a₂ : X₂ ⟶ X₃)
    (b₀ : X₀ ⟶ X₄) (b₁ : X₄ ⟶ X₅) (b₂ : X₅ ⟶ X₃)
    (c₀ : W₀ ⟶ W₁) (c₁ : W₁ ⟶ W₂) (c₂ : W₂ ⟶ W₃)
    (d₀ : W₀ ⟶ W₄) (d₁ : W₄ ⟶ W₅) (d₂ : W₅ ⟶ W₃)
    (ha₀ : a₀ ≫ e₁.hom = e₀.hom ≫ c₀) (ha₁ : a₁ ≫ e₂.hom = e₁.hom ≫ c₁)
    (ha₂ : a₂ ≫ e₃.hom = e₂.hom ≫ c₂) (hb₀ : b₀ ≫ e₄.hom = e₀.hom ≫ d₀)
    (hb₁ : b₁ ≫ e₅.hom = e₄.hom ≫ d₁) (hb₂ : b₂ ≫ e₃.hom = e₅.hom ≫ d₂)
    (hh : c₀ ≫ c₁ ≫ c₂ = d₀ ≫ d₁ ≫ d₂) :
    a₀ ≫ a₁ ≫ a₂ = b₀ ≫ b₁ ≫ b₂ := by
  have hA := compose_square e₀.hom e₁.hom e₃.hom a₀ (a₁ ≫ a₂) c₀ (c₁ ≫ c₂) ha₀
    (compose_square e₁.hom e₂.hom e₃.hom a₁ a₂ c₁ c₂ ha₁ ha₂)
  have hB := compose_square e₀.hom e₄.hom e₃.hom b₀ (b₁ ≫ b₂) d₀ (d₁ ≫ d₂) hb₀
    (compose_square e₄.hom e₅.hom e₃.hom b₁ b₂ d₁ d₂ hb₁ hb₂)
  exact (cancel_mono e₃.hom).1
    (hA.trans ((congrArg (fun z => e₀.hom ≫ z) hh).trans hB.symm))

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a bl bj bi clj cli cji d : X}
  (hal : a + D.α l = bl) (haj : a + D.α j = bj) (hai : a + D.α i = bi)
  (hlj : bl + D.α j = clj) (hli : bl + D.α i = cli) (hjl : bj + D.α l = clj)
  (hji : bj + D.α i = cji) (hil : bi + D.α l = cli) (hij : bi + D.α j = cji)
  (hd₁ : clj + D.α i = d) (hd₂ : cli + D.α j = d) (hd₃ : cji + D.α l = d)
local notation "a₀" => elvWeightSuffixCross D Sc cutoff bound i j l Λ hal hlj hd₁ hli hd₂
local notation "a₁" => elvWeightPrefixCross D Sc cutoff bound j i l Λ hal hli hai hil hd₂
local notation "a₂" => elvWeightSuffixCross D Sc cutoff bound j l i Λ hai hil hd₂ hij hd₃
local notation "b₀" => elvWeightPrefixCross D Sc cutoff bound i j l Λ hal hlj haj hjl hd₁
local notation "b₁" => elvWeightSuffixCross D Sc cutoff bound i l j Λ haj hjl hd₁ hji hd₃
local notation "b₂" => elvWeightPrefixCross D Sc cutoff bound l i j Λ haj hji hai hij hd₃

variable (β : WeightBlocks D Λ a)
local notation "βl" => blockSucc D Λ l hal β
local notation "βi" => blockSucc D Λ i hai β
local notation "βj" => blockSucc D Λ j haj β
local notation "δ₀" => blockSucc₂ D j l Λ hal hlj β
local notation "δA" => blockSucc₂ D i l Λ hal hli β
local notation "δB" => blockSucc₂ D i j Λ haj hji β
local notation "ε" => elvBlockSucc₃ D i j l Λ hal hlj hd₁ β
local notation "hA₁" => blockSucc₂_swap D i j Λ hlj hd₁ hli hd₂ (β := βl) rfl
local notation "hA₂" => elvBlockSucc₃_eq_of_pair D j l i Λ hai hil hd₂ β δA ε
  (blockSucc₂_swap D i l Λ hal hli hai hil rfl) hA₁
local notation "hA₃" => blockSucc₂_swap D j l Λ hil hd₂ hij hd₃ (β := βi) hA₂
local notation "hB₁" => elvBlockSucc₃_eq_of_pair D i l j Λ haj hjl hd₁ β δ₀ ε
  (blockSucc₂_swap D j l Λ hal hlj haj hjl rfl) rfl
local notation "hB₂" => blockSucc₂_swap D i l Λ hjl hd₁ hji hd₃ (β := βj) hB₁
local notation "C₀" => elvWeightTripleComparison D Sc cutoff bound i j l Λ hal hlj hd₁ β ε rfl
local notation "C₁" => elvWeightTripleComparison D Sc cutoff bound j i l Λ hal hli hd₂ β ε hA₁
local notation "C₂" => elvWeightTripleComparison D Sc cutoff bound j l i Λ hai hil hd₂ β ε hA₂
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound l j i Λ hai hij hd₃ β ε hA₃
local notation "C₄" => elvWeightTripleComparison D Sc cutoff bound i l j Λ haj hjl hd₁ β ε hB₁
local notation "C₅" => elvWeightTripleComparison D Sc cutoff bound l i j Λ haj hji hd₃ β ε hB₂
local notation "h₃" => elvBlockTriple_content_eq D i j l Λ hal hlj hd₁ β
local notation "h₅" => elvWeightTriple_content_eq D j i l Λ hal hli hd₂ β ε hA₁
local notation "h₄" => elvWeightTriple_content_eq D j l i Λ hai hil hd₂ β ε hA₂
local notation "h₀" => elvWeightTriple_content_eq D l j i Λ hai hij hd₃ β ε hA₃
local notation "h₂" => elvWeightTriple_content_eq D i l j Λ haj hjl hd₁ β ε hB₁
local notation "h₁" => elvWeightTriple_content_eq D l i j Λ haj hji hd₃ β ε hB₂
local notation "c₀" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₅ h₃
  (contentNormalizedRight_mem D Sc l i j)) (D.parity i * D.parity j)
local notation "c₁" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₄ h₅
  (contentNormalizedLeft_mem D Sc i l j)) (D.parity i * D.parity l)
local notation "c₂" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₀ h₄
  (contentNormalizedRight_mem D Sc i j l)) (D.parity j * D.parity l)
local notation "d₀" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₂ h₃
  (contentNormalizedLeft_mem D Sc j l i)) (D.parity j * D.parity l)
local notation "d₁" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₁ h₂
  (contentNormalizedRight_mem D Sc j i l)) (D.parity i * D.parity l)
local notation "d₂" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₀ h₁
  (contentNormalizedLeft_mem D Sc i j l)) (D.parity i * D.parity j)

/-- The two prescribed braid paths agree at every supported output block,
outside the repeated-outer corrected case. All six charts are chosen. -/
theorem elvWeightBraid_paths (hb : ¬ (i = l ∧ i ≠ j))
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε =
      (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε := by
  apply braid_of_six_squares ((C₀).app M) ((C₁).app M) ((C₂).app M)
    ((C₃).app M) ((C₄).app M) ((C₅).app M)
    ((a₀).total M ε) ((a₁).total M ε) ((a₂).total M ε)
    ((b₀).total M ε) ((b₁).total M ε) ((b₂).total M ε)
    (c₀ (M β)) (c₁ (M β)) (c₂ (M β)) (d₀ (M β)) (d₁ (M β)) (d₂ (M β))
  · exact elvWeightSuffixCross_comparison D Sc cutoff bound i j l Λ hal hlj hd₁ hli hd₂ β ε rfl M
  · exact elvWeightPrefixCross_comparison D Sc cutoff bound j i l Λ hal hli hai hil hd₂ β δA ε rfl hA₁ M
  · exact elvWeightSuffixCross_comparison D Sc cutoff bound j l i Λ hai hil hd₂ hij hd₃ β ε hA₂ M
  · exact elvWeightPrefixCross_comparison D Sc cutoff bound i j l Λ hal hlj haj hjl hd₁ β δ₀ ε rfl rfl M
  · exact elvWeightSuffixCross_comparison D Sc cutoff bound i l j Λ haj hjl hd₁ hji hd₃ β ε hB₁ M
  · exact elvWeightPrefixCross_comparison D Sc cutoff bound l i j Λ haj hji hai hij hd₃ β δB ε rfl hB₂ M
  · exact contentInduction_uncorrected_braid D Sc cutoff bound β.1 i j l hb ε.1
      h₀ h₁ h₂ h₃ h₄ h₅ (M β)

end OddMath.QuiverHecke.ELVOld
