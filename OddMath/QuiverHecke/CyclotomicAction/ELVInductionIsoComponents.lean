/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction

/-! # Components of induction comparison isomorphisms

The selected E/F charts in the fixed-content proof of Brundan–Ellis (1.12)
are existing supermodule isomorphisms. Their components are bijective on
the actual balanced coends. The coend endpoints are fixed here before
specializing to the old category, including arbitrary coefficient modules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]

private def evaluationFunctor
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C] (t : C) :
    Superfunctor k C (SVec k) ⥤ SVec k where
  obj P := P.obj t
  map f := f.total t
  map_id P := SuperNatTrans.id_total P.toFunctor t
  map_comp f g := Superfunctor.comp_total f g t

private theorem svecIso_bijective {V W : SVec k} (e : V ≅ W) :
    Function.Bijective (SVec.toLinearMap e.hom) := by
  refine ⟨?_, ?_⟩
  · intro x y h
    have hx := LinearMap.congr_fun e.hom_inv_id x
    have hy := LinearMap.congr_fun e.hom_inv_id y
    exact hx.symm.trans ((congrArg e.inv h).trans hy)
  · intro y
    exact ⟨e.inv y, LinearMap.congr_fun e.inv_hom_id y⟩

variable {C A B O : Type u}
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} O] [Preadditive O] [Linear k O] [Supercategory k O]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (H : A ⥤ O) [H.Additive] [H.Linear k] [IsSuperfunctor k H]
  (Q : B ⥤ O) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (P : Superfunctor k C (SVec k)) (N : Superfunctor k A (SVec k))
  (e : induced K P ≅ (restriction Q).obj (induced H N)) (t : B)

/-- The selected isomorphism component on its two literal coend carriers. -/
def coendIsoLinear : Obj K P.toFunctor t →ₗ[k] Obj H N.toFunctor (Q.obj t) :=
  e.hom.total t

/-- Every component of the selected isomorphism is bijective on the entire coend. -/
theorem coendIsoLinear_bijective : Function.Bijective (coendIsoLinear K H Q P N e t) := by
  have h := svecIso_bijective ((evaluationFunctor t).mapIso e)
  exact h

end OddMath.QuiverHecke.ELVOld.BalancedInduction
