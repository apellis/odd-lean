import OddMath.SKM.WeakMatchingChoice
import OddMath.SKM.MatchingCoefficientPlacement

/-! Target placement of full coefficients for literal weak realizations. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc) (μ : X)
namespace WeakMatchingChoice
variable {a b : List (Letter I)} {F : MatchingBasisChoice a b} (W : WeakMatchingChoice F)

def targetCoefficientMap (t : F.Labels) :
    SYM D k →ₗ[k] ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) where
  toFun p := xev cs μ a b (W.layers t) ≫ bubAt D Sc μ b (betaSYM cs μ p)
  map_add' p q := by simp only [map_add, Preadditive.comp_add]
  map_smul' r p := by simp only [map_smul, Linear.comp_smul, RingHom.id_apply]

def targetExpansion : (F.Labels →₀ SYM D k) →ₗ[k]
    ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  Finsupp.lsum k (W.targetCoefficientMap cs μ)

@[simp] theorem targetExpansion_single (t : F.Labels) (p : SYM D k) :
    W.targetExpansion cs μ (Finsupp.single t p) =
      xev cs μ a b (W.layers t) ≫ bubAt D Sc μ b (betaSYM cs μ p) :=
  Finsupp.lsum_single k (W.targetCoefficientMap cs μ) t p


theorem expansion_injective_iff_target :
    Function.Injective (W.expansion cs μ) ↔ Function.Injective (W.targetExpansion cs μ) := by
  apply source_target_expansion_injective_iff cs μ
    (fun t => xev cs μ a b (W.layers t)) (fun t => xpar D μ (W.layers t))
    (fun t => xev_mem_homPar cs μ a b (W.layers t))
    (W.expansion cs μ) (W.targetExpansion cs μ)
  · exact W.expansion_single cs μ
  · exact W.targetExpansion_single cs μ

end WeakMatchingChoice
end OddMath.SKM
