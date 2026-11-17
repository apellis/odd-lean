import OddMath.Algebra.FiniteSupermoduleFamily
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMatrix.GridLocalInverseFamilies
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts.ProbeUpperCharts
import OddMath.SKM.AugmentedInverseProfile
import OddMath.SKM.RouquierBoundary

/-!
# Induction grid rouquier

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The induction-grid fields in the Rouquier target

Brundan–Ellis (1.13)–(1.14): retain the ordinary induction adjunction,
the chosen dot, and the negative equal-colour double crossing when
attaching the prescribed grid inverse entries to the local data.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]

/-- The canonical parity category of modules on a supercategory. -/
def inductionModulePiCategory (C : Type u) [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C] : PiSCat.{u,u,u+1} k where
  toSCat := SCat.of k (Superfunctor k C (SVec k))
  pi := supermodulePiSupercategory

variable {C A B : Type u}
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- Balanced induction as a cell in the chosen parity target. -/
def inductionModuleCell : inductionModulePiCategory (k := k) C ⟶ inductionModulePiCategory (k := k) A :=
  show Superfunctor k (Superfunctor k C (SVec k)) (Superfunctor k A (SVec k)) from
    ⟨induction (k := k) J⟩
/-- Restriction as a cell in the same parity target. -/
def restrictionModuleCell : inductionModulePiCategory (k := k) A ⟶ inductionModulePiCategory (k := k) C :=
  show Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k C (SVec k)) from
    ⟨restriction (k := k) J⟩
/-- The existing even ordinary adjunction on these exact cells. -/
def inductionModuleAdjunction :
    SKM.SuperAdjunction (k := k) (inductionModuleCell (k := k) J) (restrictionModuleCell (k := k) J) :=
  ordinaryEvenSuperAdjunction (inductionModuleCell (k := k) J) (restrictionModuleCell (k := k) J)
    (adjunction J) (adjunctionUnit_mem J) (adjunctionCounit_mem J)

private theorem moduleAdjunction_unit_app (M : Superfunctor k C (SVec k)) :
    (inductionModuleAdjunction (k := k) J).unit.app 0 M = (adjunctionUnit J).app M := rfl

private theorem moduleAdjunction_counit_app (N : Superfunctor k A (SVec k)) :
    (inductionModuleAdjunction (k := k) J).counit.app 0 N = (adjunctionCounit J).app N := rfl

variable {p : ZMod 2}
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)

/-- The specified induced dot, without any new sign convention. -/
def inductionModuleDot : End (inductionModuleCell (k := k) J) :=
  (transformComponent_supernatural hα).toSuperNatTrans
/-- The Rouquier crossing uses the negative of the physical grid crossing. -/
def inductionModuleCross : End (inductionModuleCell (k := k) J ≫ inductionModuleCell (k := k) K) :=
  -(show End (inductionModuleCell (k := k) J ≫ inductionModuleCell (k := k) K) from
    (gridDoubleCrossComponent_supernatural J K hγ).toSuperNatTrans)

theorem inductionModuleDot_mem :
    inductionModuleDot J hα ∈ parity (R := k) _ _ p :=
  Superfunctor.IsSupernatural.toSuperNatTrans_mem (transformComponent_supernatural hα)
theorem inductionModuleCross_mem :
    inductionModuleCross J K hγ ∈ parity (R := k) _ _ p :=
  (parity (R := k) _ _ p).neg_mem
    (Superfunctor.IsSupernatural.toSuperNatTrans_mem (gridDoubleCrossComponent_supernatural J K hγ))

theorem inductionModuleCross_app (q : ZMod 2) (M : Superfunctor k C (SVec k)) :
    (inductionModuleCross J K hγ).app q M =
      if q = p then -gridDoubleCrossComponent J K hγ M else 0 := by
  change -(if q = p then gridDoubleCrossComponent J K hγ M else 0) = _
  split_ifs <;> simp only [neg_zero]

private theorem gridMateComponent_expansion (N : Superfunctor k A (SVec k)) :
    orderedGridMateComponent J K hγ N =
      (adjunctionUnit K).app (induced J ((restriction J).obj N)) ≫
        (restriction K).map (-gridDoubleCrossComponent J K hγ ((restriction J).obj N)) ≫
        (restriction K).map ((induction K).map ((adjunctionCounit J).app N)) := rfl

/-- Its ordered Rouquier mate is the exact prescribed grid principal field. -/
theorem inductionModuleMate_eq_grid :
    SKM.rouquierMate (inductionModuleAdjunction (k := k) J) (inductionModuleAdjunction (k := k) K)
      (inductionModuleCross J K hγ) = gridMateTransformation J K hγ := by
  apply Superfunctor.hom_ext
  intro q N
  rw [SKM.rouquierMate_piscat_app, inductionModuleCross_app]
  change _ = if q = p then orderedGridMateComponent J K hγ N else 0
  by_cases hq : q = p
  · rw [ite_eq_left hq, ite_eq_left hq, gridMateComponent_expansion]
    rw [moduleAdjunction_unit_app, moduleAdjunction_counit_app]
    set_option backward.dsimp.instances true in
      dsimp only [inductionModuleCell, restrictionModuleCell, Superfunctor.obj, Superfunctor.map, induction]
  · rw [ite_eq_right hq, ite_eq_right hq]
    simp only [Functor.map_zero, Limits.comp_zero, Limits.zero_comp]

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Module inverses of the finite dotted-unit columns

Brundan–Ellis (1.13) at a vacuum has only the finite shifted identity
columns. Their specified module map and its component isomorphisms
supply an even module inverse, retaining every original source shift.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
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

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
