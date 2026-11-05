import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform
import Mathlib.CategoryTheory.EqToHom

/-! # Homogeneous transformations under a commuting induction square

The generator transport in DeformedActionAssembly §§5–6 compares the
literal old/truncated coends before comparing their chosen isomorphisms.
A commuting square gives a canonical map of coends. It intertwines every
homogeneous append transformation whose coefficient arrows map through the
square, retaining the full parity twist of arbitrary coefficient arrows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

section Coends
variable {k : Type u} [CommRing k]
  {C A B D : Type u} [Category.{u} C] [Category.{u} A]
  [Category.{u} B] [Category.{u} D]
  [Preadditive A] [Linear k A] [Preadditive D] [Linear k D]
  (J : C ⥤ A) (U : A ⥤ D) [U.Additive] [U.Linear k]
  (Q : C ⥤ B) (T : B ⥤ D) (h : J ⋙ U = Q ⋙ T)

/-- The coefficient arrow of the canonical coend map through the square. -/
def coendSquareCoefficient (v : C) (w : A) :
    (J.obj v ⟶ w) →ₗ[k] (T.obj (Q.obj v) ⟶ U.obj w) where
  toFun g := eqToHom (congrArg (fun F : C ⥤ D => F.obj v) h).symm ≫ U.map g
  map_add' g g' := by rw [U.map_add, Preadditive.comp_add]
  map_smul' r g := by
    rw [U.map_smul, Linear.comp_smul]
    rfl

theorem coendSquareCoefficient_balance {v v' : C} (f : v ⟶ v')
    (w : A) (g : J.obj v' ⟶ w) :
    coendSquareCoefficient (k := k) J U Q T h v w (J.map f ≫ g) =
      T.map (Q.map f) ≫ coendSquareCoefficient (k := k) J U Q T h v' w g := by
  have hn := (eqToHom h.symm : Q ⋙ T ⟶ J ⋙ U).naturality f
  simp only [eqToHom_app, Functor.comp_map] at hn
  change eqToHom _ ≫ U.map (J.map f ≫ g) =
    T.map (Q.map f) ≫ (eqToHom _ ≫ U.map g)
  rw [U.map_comp, ← Category.assoc, ← hn, Category.assoc]

variable (M : B ⥤ SVec k)

private def coendSquareTensor (w : A) (v : C) :
    (J.obj v ⟶ w) ⊗[k] (Q ⋙ M).obj v →ₗ[k] Obj T M (U.obj w) :=
  inclusion T M (U.obj w) (Q.obj v) ∘ₗ
    TensorProduct.map (coendSquareCoefficient (k := k) J U Q T h v w) LinearMap.id

private theorem coendSquareTensor_tmul (w : A) (v : C)
    (g : J.obj v ⟶ w) (b : M.obj (Q.obj v)) :
    coendSquareTensor J U Q T h M w v (g ⊗ₜ[k] b) =
      tensor T M (Q.obj v) (coendSquareCoefficient (k := k) J U Q T h v w g) b := rfl

/-- The canonical map on literal coends induced by a commuting functor square.
No fullness, flatness or evenness assumption on coefficient arrows is needed. -/
def coendSquareMap (w : A) : Obj J (Q ⋙ M) w →ₗ[k] Obj T M (U.obj w) :=
  lift J (Q ⋙ M) w (coendSquareTensor J U Q T h M w) (by
    intro v v' f g b
    rw [coendSquareTensor_tmul, coendSquareTensor_tmul,
      coendSquareCoefficient_balance (k := k)]
    exact balance T M (Q.map f) (coendSquareCoefficient (k := k) J U Q T h v' w g) b)

end Coends

section Transform
variable {k : Type u} [CommRing k]
  {C A B D : Type u} [Category.{u} C] [Category.{u} A]
  [Category.{u} B] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J K : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (U : A ⥤ D) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T S : B ⥤ D) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  [S.Additive] [S.Linear k] [IsSuperfunctor k S]
  (hJ : J ⋙ U = Q ⋙ T) (hK : K ⋙ U = Q ⋙ S)
  (M : Superfunctor k B (SVec k))
  {p : ZMod 2} {α : ∀ v, J.obj v ⟶ K.obj v} {β : ∀ v, T.obj v ⟶ S.obj v}
  (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β)

omit [J.Linear k] [IsSuperfunctor k J] [T.Linear k] [IsSuperfunctor k T] in

end Transform
end OddMath.QuiverHecke.ELVOld.BalancedInduction
