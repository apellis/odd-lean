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

private def flattenLinear (w : B) :
    Obj K (induced J M).toFunctor w →ₗ[k] Obj (J ⋙ K) M.toFunctor w :=
  ((inductionComp J K).hom.app M).total w

private def unflattenLinear (w : B) :
    Obj (J ⋙ K) M.toFunctor w →ₗ[k] Obj K (induced J M).toFunctor w :=
  ((inductionComp J K).inv.app M).total w

private theorem flattenLinear_tensor (s : C) (v : A) (w : B)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) (b : M.obj s) :
    flattenLinear J K M w
      (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b)) =
    tensor (J ⋙ K) M.toFunctor s (K.map a ≫ g) b := by
  have h := inductionComp_hom_total_tensor J K M s v w g a b
  set_option backward.dsimp.instances true in
    dsimp only [flattenLinear, induction] at h ⊢
  exact h

private theorem unflattenLinear_tensor (s : C) (w : B)
    (g : K.obj (J.obj s) ⟶ w) (b : M.obj s) :
    unflattenLinear J K M w (tensor (J ⋙ K) M.toFunctor s g b) =
      tensor K (induced J M).toFunctor (J.obj s) g
        (tensor J M.toFunctor s (𝟙 _) b) := by
  have h := inductionComp_inv_total_tensor J K M s w g b
  set_option backward.dsimp.instances true in
    dsimp only [unflattenLinear, induction] at h ⊢
  exact h

/-- The homogeneous two-letter transform, conjugated by the selected
induction-composition isomorphism on the literal iterated coends. -/
def doubleTransformLinear (w : B) :
    Obj K (induced J M).toFunctor w →ₗ[k] Obj K (induced J M).toFunctor w :=
  unflattenLinear J K M w ∘ₗ transformLinear hα M w ∘ₗ flattenLinear J K M w

/-- The inverse flattening inserts a unit in the first induction; the
transformation twists the entire old composite coefficient, in its order. -/
theorem doubleTransformLinear_tensor (s : C) (v : A) (w : B)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) (b : M.obj s) :
    doubleTransformLinear J K hα M w
      (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b)) =
      tensor K (induced J M).toFunctor (J.obj s)
        (α s ≫ twist k p (K.map a ≫ g)) (tensor J M.toFunctor s (𝟙 _) b) := by
  rw [doubleTransformLinear, LinearMap.comp_apply, LinearMap.comp_apply,
    flattenLinear_tensor, transformLinear_tensor, unflattenLinear_tensor]

private theorem transformComponent_total (w : B) :
    (transformComponent hα M).total w = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

/-- This literal coend operator is the total map of the given homogeneous
module transformation conjugated by the two selected flattenings. -/
theorem doubleTransformLinear_eq_total (w : B)
    (b : Obj K (induced J M).toFunctor w) :
    doubleTransformLinear J K hα M w b =
      (((inductionComp J K).hom.app M ≫ transformComponent hα M ≫
        (inductionComp J K).inv.app M).total w) b := by
  rw [Superfunctor.comp_total, SVec.comp_apply, Superfunctor.comp_total,
    SVec.comp_apply, transformComponent_total]
  unfold doubleTransformLinear
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  unfold flattenLinear unflattenLinear
  rfl

omit [Supercategory k B] [K.Additive] [K.Linear k] [IsSuperfunctor k K] in

end OddMath.QuiverHecke.ELVOld.BalancedInduction
