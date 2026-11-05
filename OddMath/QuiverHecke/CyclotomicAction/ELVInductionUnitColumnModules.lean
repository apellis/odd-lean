import OddMath.QuiverHecke.CyclotomicAction.ELVUnitColumnMatrices
import OddMath.Algebra.FiniteSupermoduleInverseRows
import OddMath.Algebra.HomogeneousSuperfunctorIso

/-! # Module inverses of the finite dotted-unit columns

Brundan–Ellis (1.13) at a vacuum has only the finite shifted identity
columns. Their specified module map and its component isomorphisms
supply an even module inverse, retaining every original source shift.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
local instance unitColumnModulePi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- The exact finite family of shifted values, without a principal slot. -/
def unitColumnModuleFamily (p : ZMod 2) (M : Superfunctor k C (SVec k)) (m : ℕ) :
    Fin m → Superfunctor k C (SVec k) :=
  fun r => (SKM.homParityShift (k := k) (r.val • p)).obj M

variable {A : Type u} [Category.{u} A]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (M : Superfunctor k C (SVec k)) (m : ℕ)

/-- The prescribed finite module map of shifted ordinary unit/dot columns. -/
def unitColumnModuleMap :
    OddMath.FiniteSupermodule.product (unitColumnModuleFamily p M m) ⟶
      (restriction J).obj ((induction J).obj M) :=
  OddMath.FiniteSupermodule.columnsHom
    (fun r : Fin m => shiftedUnitDotColumn J hα M r.val)
    (fun r => shiftedUnitDotColumn_mem J hα M r.val)

/-- The finite module map is even in the canonical source coordinates. -/
theorem unitColumnModuleMap_mem :
    unitColumnModuleMap J hα M m ∈ parity (R := k) _ _ 0 := by
  unfold unitColumnModuleMap OddMath.FiniteSupermodule.columnsHom
  exact Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)

/-- Its component is exactly the prescribed superspace unit matrix. -/
theorem unitColumnModuleMap_total (w : C) :
    (unitColumnModuleMap J hα M m).total w = unitColumnMatrix J hα M m w := by
  apply SVec.hom_ext
  intro x
  exact OddMath.FiniteSupermodule.columnsHom_total_apply
    (fun r : Fin m => shiftedUnitDotColumn J hα M r.val)
    (fun r => shiftedUnitDotColumn_mem J hα M r.val) w x

/-- The prescribed component inverses assemble into an even module inverse.
The component isomorphisms are intermediate inputs, supplied by the given
old missing-colour inverse in the boundary construction. -/
def unitColumnModuleIso
    (e : ∀ w, unitColumnSourceSpace p M m w ≅ ((restriction J).obj ((induction J).obj M)).obj w)
    (he : ∀ w, (e w).hom = unitColumnMatrix J hα M m w) :
    OddMath.FiniteSupermodule.product (unitColumnModuleFamily p M m) ≅
      (restriction J).obj ((induction J).obj M) :=
  OddMath.HomogeneousSuperfunctorIso.ofHom (unitColumnModuleMap J hα M m)
    (unitColumnModuleMap_mem J hα M m) e
    (fun w => (he w).trans (unitColumnModuleMap_total J hα M m w).symm)

/-- The constructed inverse has the original specified forward module map. -/
theorem unitColumnModuleIso_hom
    (e : ∀ w, unitColumnSourceSpace p M m w ≅ ((restriction J).obj ((induction J).obj M)).obj w)
    (he : ∀ w, (e w).hom = unitColumnMatrix J hα M m w) :
    (unitColumnModuleIso J hα M m e he).hom = unitColumnModuleMap J hα M m :=
  OddMath.HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

end OddMath.QuiverHecke.ELVOld.BalancedInduction
