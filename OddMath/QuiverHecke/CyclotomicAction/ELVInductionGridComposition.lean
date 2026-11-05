import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp

/-! # Composition of coend comparisons across a six-category grid

The two-letter comparison in DeformedActionAssembly §§5–6 must agree
with the selected single-letter comparisons and the canonical induction
flattenings. The coefficient calculation retains the intermediate object
transports, before the generic coend calculation is specialized to the
changing fixed-content scalar quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

section Squares
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type u}
  [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂]
  [Category.{u} D₀] [Category.{u} D₁] [Category.{u} D₂]
  (J : C₀ ⥤ C₁) (K : C₁ ⥤ C₂)
  (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂)
  (T : D₀ ⥤ D₁) (S : D₁ ⥤ D₂)
  (hJ : J ⋙ Q₁ = Q₀ ⋙ T) (hK : K ⋙ Q₂ = Q₁ ⋙ S)

include hJ hK in

end Squares

section Coefficients
variable {k : Type u} [CommRing k]
  {C₀ C₁ C₂ D₀ D₁ D₂ : Type u}
  [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂]
  [Category.{u} D₀] [Category.{u} D₁] [Category.{u} D₂]
  [Preadditive C₁] [Linear k C₁] [Preadditive C₂] [Linear k C₂]
  [Preadditive D₁] [Linear k D₁] [Preadditive D₂] [Linear k D₂]
  (J : C₀ ⥤ C₁) (K : C₁ ⥤ C₂) (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) [Q₁.Additive] [Q₁.Linear k]
  (Q₂ : C₂ ⥤ D₂) [Q₂.Additive] [Q₂.Linear k]
  (T : D₀ ⥤ D₁) (S : D₁ ⥤ D₂) (hJ : J ⋙ Q₁ = Q₀ ⋙ T) (hK : K ⋙ Q₂ = Q₁ ⋙ S)

end Coefficients

section Nested
variable {k : Type u} [CommRing k]
  {C₀ C₁ C₂ D₀ D₁ D₂ : Type u}
  [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂]
  [Category.{u} D₀] [Category.{u} D₁] [Category.{u} D₂]
  [Preadditive C₀] [Linear k C₀]
  [Preadditive C₁] [Linear k C₁] [Preadditive C₂] [Linear k C₂]
  [Supercategory k C₀] [Supercategory k C₁] [Supercategory k C₂]
  [Preadditive D₀] [Linear k D₀]
  [Preadditive D₁] [Linear k D₁] [Preadditive D₂] [Linear k D₂]
  [Supercategory k D₀] [Supercategory k D₁] [Supercategory k D₂]
  (J : C₀ ⥤ C₁) (K : C₁ ⥤ C₂) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (Q₀ : C₀ ⥤ D₀) [Q₀.Additive] [Q₀.Linear k] [IsSuperfunctor k Q₀]
  (Q₁ : C₁ ⥤ D₁) [Q₁.Additive] [Q₁.Linear k]
  (Q₂ : C₂ ⥤ D₂) [Q₂.Additive] [Q₂.Linear k]
  (T : D₀ ⥤ D₁) (S : D₁ ⥤ D₂) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  [S.Additive] [S.Linear k] [IsSuperfunctor k S]
  (hJ : J ⋙ Q₁ = Q₀ ⋙ T) (hK : K ⋙ Q₂ = Q₁ ⋙ S)
  (M : Superfunctor k D₀ (SVec k))
private abbrev coendPullback : Superfunctor k C₀ (SVec k) := ⟨Q₀ ⋙ M.toFunctor⟩
local notation "RM" => coendPullback (k := k) Q₀ M

end Nested
end OddMath.QuiverHecke.ELVOld.BalancedInduction
