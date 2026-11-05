/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularMate
import OddMath.Algebra.HomogeneousSuperfunctorIso

/-! # Homogeneous rectangular mate isomorphisms

Brundan–Ellis (1.12) needs module inverses and input-module naturality for
the prescribed rectangular cup-crossing-cap. Pointwise coend bijectivity
is packaged here before specializing the four categories. The fixed old
content proof supplies that bijectivity from its chosen chart square.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B E : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (M : B ⥤ E) [M.Additive] [M.Linear k] [IsSuperfunctor k M]
  {p : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ M).obj s}
  (hα : IsSupernatural k p α)

/-- The ordered rectangular mate is supernatural in arbitrary input-module maps. -/
theorem orderedRectangularMateComponent_supernatural :
    IsSupernatural k p (F := restriction (k := k) J ⋙ induction (k := k) K) (G := induction (k := k) L ⋙ restriction (k := k) M)
      (orderedRectangularMateComponent J K L M hα) := by
  have hU₀ := isSupernatural_of_natTrans (R := k) (adjunctionUnit (k := k) M)
    (fun P => adjunctionUnit_mem (k := k) M P)
  have hU := hU₀.whiskerLeft (restriction (k := k) J ⋙ induction (k := k) K)
  have hX := ((rectangularCrossComponent_supernatural J K L M hα).whiskerLeft
    (restriction (k := k) J)).whiskerRight (restriction (k := k) M)
  have hC₀ := isSupernatural_of_natTrans (R := k) (adjunctionCounit (k := k) J)
    (fun N => adjunctionCounit_mem (k := k) J N)
  have hC := (hC₀.whiskerRight (induction (k := k) L)).whiskerRight (restriction (k := k) M)
  change IsSupernatural k p (F := restriction (k := k) J ⋙ induction (k := k) K) (G := induction (k := k) L ⋙ restriction (k := k) M)
    (fun N => (adjunctionUnit (k := k) M).app (induced K ((restriction (k := k) J).obj N)) ≫
      (restriction (k := k) M).map (rectangularCrossComponent J K L M hα ((restriction (k := k) J).obj N)) ≫
      (restriction (k := k) M).map ((induction (k := k) L).map ((adjunctionCounit (k := k) J).app N)))
  have h := hU.comp (hX.comp hC)
  set_option backward.dsimp.instances true in
    dsimp only [induction] at h ⊢
  simpa only [Functor.comp_id, Functor.id_comp, Functor.comp_obj, zero_add, add_zero,
    Category.assoc] using h

/-- Pointwise bijectivity of the prescribed coend map supplies its homogeneous module inverse. -/
def rectangularMateModuleIso (N : Superfunctor k A (SVec k))
    (h : ∀ t, Function.Bijective (orderedRectangularMateLinear J K L M hα N t)) :
    induced K ((restriction (k := k) J).obj N) ≅ (restriction (k := k) M).obj (induced L N) :=
  HomogeneousSuperfunctorIso.ofHom (orderedRectangularMateComponent J K L M hα N)
    (orderedRectangularMateComponent_mem J K L M hα N)
    (fun t => SVec.isoOfLinearEquiv (orderedRectangularMateEquiv J K L M hα N t (h t)))
    (fun _ => rfl)

@[simp] theorem rectangularMateModuleIso_hom (N : Superfunctor k A (SVec k))
    (h : ∀ t, Function.Bijective (orderedRectangularMateLinear J K L M hα N t)) :
    (rectangularMateModuleIso J K L M hα N h).hom =
      orderedRectangularMateComponent J K L M hα N :=
  HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

/-- The lower restriction followed by lower induction, as a superfunctor on modules. -/
def rectangularMateSourceFunctor :
    Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k B (SVec k)) :=
  ⟨restriction (k := k) J ⋙ induction (k := k) K⟩

/-- The upper induction followed by upper restriction, as a superfunctor on modules. -/
def rectangularMateTargetFunctor :
    Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k B (SVec k)) :=
  ⟨induction (k := k) L ⋙ restriction (k := k) M⟩

/-- The homogeneous transformation formed by the prescribed ordered components. -/
def rectangularMateHom : rectangularMateSourceFunctor (k := k) J K ⟶ rectangularMateTargetFunctor (k := k) L M :=
  (orderedRectangularMateComponent_supernatural J K L M hα).toSuperNatTrans

theorem rectangularMateHom_mem :
    rectangularMateHom J K L M hα ∈ parity (R := k) _ _ p :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (orderedRectangularMateComponent_supernatural J K L M hα).toSuperNatTrans_isHomogeneous

/-- The total input-module component is exactly the prescribed module mate. -/
@[simp] theorem rectangularMateHom_total (N : Superfunctor k A (SVec k)) :
    (rectangularMateHom J K L M hα).total N = orderedRectangularMateComponent J K L M hα N :=
  HomogeneousSuperfunctorIso.homogeneous_total
    (F := rectangularMateSourceFunctor (k := k) J K)
    (G := rectangularMateTargetFunctor (k := k) L M)
    (orderedRectangularMateComponent_supernatural J K L M hα) N

/-- The inverse is supernatural in arbitrary, including odd, input-module maps. -/
def rectangularMateFunctorIso
    (h : ∀ N t, Function.Bijective (orderedRectangularMateLinear J K L M hα N t)) :
    rectangularMateSourceFunctor (k := k) J K ≅ rectangularMateTargetFunctor (k := k) L M :=
  HomogeneousSuperfunctorIso.ofHom (rectangularMateHom J K L M hα)
    (rectangularMateHom_mem J K L M hα)
    (fun N => rectangularMateModuleIso J K L M hα N (h N))
    (fun N => (rectangularMateModuleIso_hom J K L M hα N (h N)).trans
      (rectangularMateHom_total J K L M hα N).symm)

@[simp] theorem rectangularMateFunctorIso_hom
    (h : ∀ N t, Function.Bijective (orderedRectangularMateLinear J K L M hα N t)) :
    (rectangularMateFunctorIso J K L M hα h).hom = rectangularMateHom J K L M hα :=
  HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

end OddMath.QuiverHecke.ELVOld.BalancedInduction
