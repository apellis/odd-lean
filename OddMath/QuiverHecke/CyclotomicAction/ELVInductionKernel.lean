import OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensor

/-! # The Hom kernel of balanced induction
The arbitrary-module tensor step in DeformedMatrixComparison §4 requires
identifying coefficient-kernel tensors with the existing action coends.
This identifies the ordinary-right kernel Hom(J−,w), retaining its literal
balance and the complete input module.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams
namespace OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D]

/-- The ordinary-right Hom kernel of induction at a fixed output. -/
def inductionKernel (J : C ⥤ D) (w : D) : Cᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (J.obj v.unop ⟶ w)
  map a := ModuleCat.ofHom (Linear.leftComp k w (J.map a.unop))
  map_id v := by
    ext g
    change J.map (𝟙 v.unop) ≫ g = g
    rw [J.map_id, Category.id_comp]
  map_comp a b := by
    ext g
    change J.map (b.unop ≫ a.unop) ≫ g = J.map b.unop ≫ (J.map a.unop ≫ g)
    rw [J.map_comp, Category.assoc]

/-- The coefficient-kernel quotient is the existing induction quotient. -/
def inductionKernelEquiv (J : C ⥤ D) (M : C ⥤ SVec k) (w : D) :
    Obj (inductionKernel J w) M ≃ₗ[k] BalancedInduction.Obj J M w :=
  LinearEquiv.refl k _

@[simp] theorem inductionKernelEquiv_tensor (J : C ⥤ D) (M : C ⥤ SVec k)
    (w : D) (v : C) (g : J.obj v ⟶ w) (m : M.obj v) :
    inductionKernelEquiv J M w (tensor (inductionKernel J w) M v g m) =
      BalancedInduction.tensor J M v g m := rfl

end OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
