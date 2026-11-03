import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockDistinctInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSignedMate

/-! # The diagonal matrix mate through canonical content charts

Brundan–Ellis (1.13)–(1.14): the prescribed negative-crossing grid mate
commutes with the selected full-content source and target charts. The
ambient map is the already inverted weighted diagonal matrix mate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
private theorem map_id_left {C : Type u} [Category.{u} C] (F : C ⥤ C)
    (v w z : C) (a : F.obj v ⟶ w) (b : w ⟶ z) :
    a ≫ b = F.map (𝟙 v) ≫ a ≫ b := by
  rw [F.map_id, Category.id_comp]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "δ" => γ + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "hK" => contentBlockCanonicalSum γ [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hK
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "Q₂" => contentInclusion D Sc cutoff N δ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sqJ" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hJ
local notation "sqK" => contentAppendTo_inclusion D Sc cutoff N γ [i] δ hK
local notation "hα₀" => contentBlockDistinctCross_supernatural D Sc cutoff N β i i
local notation "hχ" => truncatedEqualCross_supernatural D Sc cutoff N i

/-- The prescribed equal-colour crossing has the matrix degree p_i. -/
theorem contentBlockMatrixCross_supernatural :
    IsSupernatural k (D.parity i) (contentBlockDistinctCross D Sc cutoff N β i i) :=
  (SKM.zmod2_mul_self (D.parity i)) ▸ hα₀
local notation "hα" => contentBlockMatrixCross_supernatural D Sc cutoff N β i

private theorem negativeContentCross :
    IsSupernatural k (D.parity i * D.parity i)
      (fun s => -contentBlockDistinctCross D Sc cutoff N β i i s) where
  mem s := neg_mem ((hα₀).mem s)
  naturality hf := by
    rw [Preadditive.comp_neg, (hα₀).naturality hf, Preadditive.neg_comp, smul_neg]
private theorem negativeGlobalCross :
    IsSupernatural k (D.parity i * D.parity i)
      (fun s => -truncatedEqualCrossComponent D Sc cutoff N i s) where
  mem s := neg_mem ((hχ).mem s)
  naturality hf := by
    rw [Preadditive.comp_neg, (hχ).naturality hf, Preadditive.neg_comp, smul_neg]

/-- The whole given diagonal mate commutes with its chosen canonical content charts. -/
theorem contentBlockMatrixMate_square (M : ContentModules D Sc cutoff N γ)
    (t : ContentCategory D Sc cutoff N γ) :
    fullSquareTargetLinear K Q₂ Q₁ T sqK M ((K).obj t) ((T).obj ((Q₁).obj t))
        (congrArg (fun F => F.obj t) sqK) ∘ₗ
      orderedGridMateLinear J K hα M t =
      orderedMateLinear T hχ (induced Q₁ M) ((Q₁).obj t) ∘ₗ
        fullSquareOrdinarySourceLinear J Q₁ Q₀ T sqJ
          ((restriction J).obj M) T (induced Q₁ M)
          (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M) t := by
  have h := fullContentMate_square J J K K Q₀ Q₁ Q₁ Q₂ T T
    sqJ sqJ sqK sqK (negativeContentCross D Sc cutoff N β i)
    (negativeGlobalCross D Sc cutoff N i) M
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)
    (contentBlockDistinctRestriction_unit D Sc cutoff N β i M) (by
      intro s z g
      rw [Functor.map_comp, Functor.map_neg, map_twist]
      dsimp only [contentAppendTo, contentInclusion, Functor.comp_obj, Functor.comp_map]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact map_id_left T ((T).obj s.obj) _ _
        (-truncatedEqualCrossComponent D Sc cutoff N i s.obj)
        (twist k (D.parity i * D.parity i) ((T).map g))) t
  rw [rectangularMate_negative_eq_grid J K hα₀ M t,
    mixedMate_negative_eq_ordered T hχ (induced Q₁ M) ((Q₁).obj t)] at h
  have he := gridMateLinear_degree_eq J K hα₀ (SKM.zmod2_mul_self (D.parity i)) hα M t
  exact (congrArg (fun f => fullSquareTargetLinear K Q₂ Q₁ T sqK M ((K).obj t)
    ((T).obj ((Q₁).obj t)) (congrArg (fun F => F.obj t) sqK) ∘ₗ f) he).symm.trans h

end OddMath.QuiverHecke.ELVOld
