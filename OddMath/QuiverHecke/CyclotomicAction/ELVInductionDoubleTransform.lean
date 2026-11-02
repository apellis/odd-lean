import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform

/-! # Homogeneous transformations on iterated induction

The equal-colour crossing in DeformedMatrixComparison (2), (4) is obtained
from its literal two-letter transformation using the chosen induction
flattening. The tensor formula below keeps its parity twist on the complete
composite coefficient arrow.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ v, (J ⋙ K).obj v ⟶ (J ⋙ K).obj v}
  (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k))

/-- The homogeneous two-letter transform, conjugated by the selected
induction-composition isomorphism on the literal iterated coends. -/
def doubleTransformLinear (w : B) :
    Obj K (induced J M).toFunctor w →ₗ[k] Obj K (induced J M).toFunctor w :=
  ((inductionComp J K).inv.app M).total w ∘ₗ
    transformLinear hα M w ∘ₗ ((inductionComp J K).hom.app M).total w

/-- The inverse flattening inserts a unit in the first induction; the
transformation twists the entire old composite coefficient, in its order. -/
theorem doubleTransformLinear_tensor (s : C) (v : A) (w : B)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) (b : M.obj s) :
    doubleTransformLinear J K hα M w
      (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b)) =
      tensor K (induced J M).toFunctor (J.obj s)
        (α s ≫ twist k p (K.map a ≫ g)) (tensor J M.toFunctor s (𝟙 _) b) := by
  have h₁ := inductionComp_hom_total_tensor J K M s v w g a b
  have h₂ := transformLinear_tensor hα M w s (K.map a ≫ g) b
  have h₃ := inductionComp_inv_total_tensor J K M s w
    (α s ≫ twist k p (K.map a ≫ g)) b
  unfold doubleTransformLinear
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  exact (congrArg (((inductionComp J K).inv.app M).total w)
    ((congrArg (transformLinear hα M w) h₁).trans h₂)).trans h₃

end OddMath.QuiverHecke.ELVOld.BalancedInduction
