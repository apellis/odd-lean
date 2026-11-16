import OddMath.SKM.Nondegeneracy

/-! Target-placement convention for full matching coefficients. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc) (μ : X)
namespace MatchingBasisChoice
variable {a b : List (Letter I)}

def targetCoefficientMap (F : MatchingBasisChoice a b) (t : F.Labels) :
    SYM D k →ₗ[k] ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) where
  toFun p := xev cs μ a b (F.layers t) ≫ bubAt D Sc μ b (betaSYM cs μ p)
  map_add' p q := by simp only [map_add, Preadditive.comp_add]
  map_smul' r p := by simp only [map_smul, Linear.comp_smul, RingHom.id_apply]

def targetExpansion (F : MatchingBasisChoice a b) :
    (F.Labels →₀ SYM D k) →ₗ[k]
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  Finsupp.lsum k (F.targetCoefficientMap cs μ)

@[simp] theorem targetExpansion_single (F : MatchingBasisChoice a b) (t : F.Labels) (p : SYM D k) :
    F.targetExpansion cs μ (Finsupp.single t p) =
      xev cs μ a b (F.layers t) ≫ bubAt D Sc μ b (betaSYM cs μ p) :=
  Finsupp.lsum_single k (F.targetCoefficientMap cs μ) t p

end MatchingBasisChoice
end OddMath.SKM
