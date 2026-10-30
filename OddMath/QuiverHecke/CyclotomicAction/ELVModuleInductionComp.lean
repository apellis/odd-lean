/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Composition of balanced induction

The constructed induction–restriction adjunctions give a canonical comparison
`induction J ⋙ induction K ≅ induction (J ⋙ K)` on the category of all supernatural
module maps. Both directions are even. On balanced quotient generators the
comparison sends `[g ⊗ [h ⊗ m]]` to `[K.map h ≫ g ⊗ m]`; its inverse sends
`[a ⊗ m]` to `[a ⊗ [id ⊗ m]]`. No homogeneity restriction on `g`, `h`, or `m`
is required. The coefficient ring is an arbitrary commutative ring.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

def compAdjunction : induction (k := k) J ⋙ induction K ⊣ restriction (J ⋙ K) :=
  (adjunction J).comp (adjunction K)

def inductionComp : induction (k := k) J ⋙ induction K ≅ induction (J ⋙ K) :=
  (compAdjunction J K).leftAdjointUniq (adjunction (J ⋙ K))

private theorem uniq_hom {A B : Type*} [Category* A] [Category* B]
    {F F' : A ⥤ B} {G : B ⥤ A} (a : F ⊣ G) (b : F' ⊣ G) (x : A) :
    (a.leftAdjointUniq b).hom.app x = F.map (b.unit.app x) ≫ a.counit.app (F'.obj x) := by
  calc
    _ = (a.homEquiv _ _).symm (b.unit.app x) :=
      (Equiv.eq_symm_apply _).mpr (Adjunction.homEquiv_leftAdjointUniq_hom_app a b x)
    _ = _ := a.homEquiv_counit _ _ _

private theorem uniq_comp_hom {A B T : Type*} [Category* A] [Category* B] [Category* T]
    {F : A ⥤ B} {G : B ⥤ A} {H : B ⥤ T} {I : T ⥤ B} {L : A ⥤ T}
    (a : F ⊣ G) (b : H ⊣ I) (c : L ⊣ I ⋙ G) (x : A) :
    ((a.comp b).leftAdjointUniq c).hom.app x =
      H.map (F.map (c.unit.app x)) ≫ H.map (a.counit.app (I.obj (L.obj x))) ≫
        b.counit.app (L.obj x) := by
  rw [uniq_hom, Adjunction.comp_counit_app]
  rfl

theorem inductionComp_hom_eq (M : Superfunctor k C (SVec k)) :
    (inductionComp J K).hom.app M =
      (induction K).map ((induction J).map ((adjunction (J ⋙ K)).unit.app M)) ≫
      (induction K).map ((adjunction J).counit.app
        ((restriction K).obj ((induction (J ⋙ K)).obj M))) ≫
      (adjunction K).counit.app ((induction (J ⋙ K)).obj M) := by
  exact uniq_comp_hom (adjunction J) (adjunction K) (adjunction (J ⋙ K)) M

theorem inductionComp_inv_eq (M : Superfunctor k C (SVec k)) :
    (inductionComp J K).inv.app M =
      (induction (J ⋙ K)).map
        ((adjunction J).unit.app M ≫
          (restriction J).map ((adjunction K).unit.app ((induction J).obj M))) ≫
      (adjunction (J ⋙ K)).counit.app ((induction K).obj ((induction J).obj M)) := by
  rw [inductionComp, Adjunction.leftAdjointUniq_inv_app, uniq_hom]
  rw [show (compAdjunction J K).unit.app M = _ from
    Adjunction.comp_unit_app (adjunction J) (adjunction K) M]
  rfl

theorem inductionComp_hom_mem (M : Superfunctor k C (SVec k)) :
    (inductionComp J K).hom.app M ∈ parity (R := k) _ _ 0 := by
  rw [inductionComp_hom_eq]
  have hu := adjunctionUnit_mem (J ⋙ K) M
  have hju := map_mem (induction J) hu
  have hkju := map_mem (induction K) hju
  have hcj := adjunctionCounit_mem J ((restriction K).obj ((induction (J ⋙ K)).obj M))
  have hkcj := map_mem (induction K) hcj
  have hck := adjunctionCounit_mem K ((induction (J ⋙ K)).obj M)
  exact comp_mem hkju (comp_mem hkcj hck)

theorem inductionComp_inv_mem (M : Superfunctor k C (SVec k)) :
    (inductionComp J K).inv.app M ∈ parity (R := k) _ _ 0 := by
  rw [inductionComp_inv_eq]
  have huj := adjunctionUnit_mem J M
  have huk := adjunctionUnit_mem K ((induction J).obj M)
  have hru := map_mem (restriction J) huk
  have hu := comp_mem huj hru
  have hiu := map_mem (induction (J ⋙ K)) hu
  have hc := adjunctionCounit_mem (J ⋙ K) ((induction K).obj ((induction J).obj M))
  exact comp_mem hiu hc

private def transposeMap (M : Superfunctor k C (SVec k))
    (N : Superfunctor k D (SVec k)) (f : M ⟶ (restriction J).obj N) :
    (induction J).obj M ⟶ N :=
  (induction J).map f ≫ (adjunction J).counit.app N

private theorem transposeMap_tensor (M : Superfunctor k C (SVec k))
    (N : Superfunctor k D (SVec k)) (f : M ⟶ (restriction J).obj N)
    (v : C) (w : D) (h : J.obj v ⟶ w) (m : M.obj v) :
    (transposeMap J M N f).app 0 w (tensor J M.toFunctor v h m) =
      N.map h (f.app 0 v m) := by
  change counit J N.toFunctor w (mapComponent J f 0 w (tensor J M.toFunctor v h m)) + 0 = _
  rw [add_zero, mapComponent_tensor, twist_zero]
  exact counit_tensor J N.toFunctor w v h (f.app 0 v m)

private theorem transposeMap_comp_tensor (M : Superfunctor k C (SVec k))
    (N : Superfunctor k E (SVec k))
    (f : M ⟶ (restriction J).obj ((restriction K).obj N))
    (v : C) (w : D) (z : E) (g : K.obj w ⟶ z) (h : J.obj v ⟶ w) (m : M.obj v) :
    (transposeMap K (induced J M) N
      (transposeMap J M ((restriction K).obj N) f)).app 0 z
      (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m)) =
        N.map g (N.map (K.map h) (f.app 0 v m)) := by
  erw [transposeMap_tensor, transposeMap_tensor]
  rfl

@[simp] theorem inductionComp_hom_tensor (M : Superfunctor k C (SVec k))
    (v : C) (w : D) (z : E) (g : K.obj w ⟶ z) (h : J.obj v ⟶ w) (m : M.obj v) :
    ((inductionComp J K).hom.app M).app 0 z
      (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m)) =
      tensor (J ⋙ K) M.toFunctor v (K.map h ≫ g) m := by
  let N := (induction (J ⋙ K)).obj M
  let U := (restriction K).obj N
  let f : M ⟶ (restriction J).obj U := (adjunction (J ⋙ K)).unit.app M
  have heq : (inductionComp J K).hom.app M =
      transposeMap K (induced J M) N (transposeMap J M U f) := by
    dsimp only [transposeMap]
    erw [Functor.map_comp, Category.assoc]
    exact inductionComp_hom_eq J K M
  rw [heq]
  erw [transposeMap_comp_tensor J K M N f]
  change postcompose (J ⋙ K) M.toFunctor g
    (postcompose (J ⋙ K) M.toFunctor (K.map h) (unit (J ⋙ K) M.toFunctor v m)) = _
  rw [unit_apply, postcompose_tensor, postcompose_tensor, Category.id_comp]

private theorem compUnit_apply (M : Superfunctor k C (SVec k)) (v : C) (m : M.obj v) :
    (((adjunction J).unit.app M ≫
      (restriction J).map ((adjunction K).unit.app ((induction J).obj M))).app 0 v) m =
      tensor K (induced J M).toFunctor (J.obj v) (𝟙 _) (tensor J M.toFunctor v (𝟙 _) m) := by
  change unit K (induced J M).toFunctor (J.obj v) (unit J M.toFunctor v m) + 0 = _
  rw [add_zero]
  rfl

@[simp] theorem inductionComp_inv_tensor (M : Superfunctor k C (SVec k))
    (v : C) (z : E) (a : K.obj (J.obj v) ⟶ z) (m : M.obj v) :
    ((inductionComp J K).inv.app M).app 0 z (tensor (J ⋙ K) M.toFunctor v a m) =
      tensor K (induced J M).toFunctor (J.obj v) a (tensor J M.toFunctor v (𝟙 _) m) := by
  let N := (induction K).obj ((induction J).obj M)
  let f : M ⟶ (restriction (J ⋙ K)).obj N :=
    (adjunction J).unit.app M ≫
      (restriction J).map ((adjunction K).unit.app ((induction J).obj M))
  have heq : (inductionComp J K).inv.app M = transposeMap (J ⋙ K) M N f :=
    inductionComp_inv_eq J K M
  rw [heq]
  erw [transposeMap_tensor (J ⋙ K) M N f]
  have hf := compUnit_apply J K M v m
  change f.app 0 v m = _ at hf
  rw [hf]
  change postcompose K (induced J M).toFunctor a
    (tensor K (induced J M).toFunctor (J.obj v) (𝟙 _) (tensor J M.toFunctor v (𝟙 _) m)) = _
  erw [postcompose_tensor, Category.id_comp]

@[simp] theorem inductionComp_hom_app_one (M : Superfunctor k C (SVec k)) (z : E) :
    ((inductionComp J K).hom.app M).app 1 z = 0 :=
  Superfunctor.app_eq_zero_of_mem (inductionComp_hom_mem J K M) (by decide) z

@[simp] theorem inductionComp_inv_app_one (M : Superfunctor k C (SVec k)) (z : E) :
    ((inductionComp J K).inv.app M).app 1 z = 0 :=
  Superfunctor.app_eq_zero_of_mem (inductionComp_inv_mem J K M) (by decide) z

/-- Naturality includes arbitrary sums of even and odd module maps. -/
theorem inductionComp_naturality {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) :
    (induction K).map ((induction J).map f) ≫ (inductionComp J K).hom.app N =
      (inductionComp J K).hom.app M ≫ (induction (J ⋙ K)).map f :=
  (inductionComp J K).hom.naturality f

/-- The total map is the sign-free flattening map, since the comparison is even. -/
theorem inductionComp_hom_total_tensor (M : Superfunctor k C (SVec k))
    (v : C) (w : D) (z : E) (g : K.obj w ⟶ z) (h : J.obj v ⟶ w) (m : M.obj v) :
    ((inductionComp J K).hom.app M).total z
      (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m)) =
      tensor (J ⋙ K) M.toFunctor v (K.map h ≫ g) m := by
  rw [SuperNatTrans.total, inductionComp_hom_app_one, add_zero]
  exact inductionComp_hom_tensor J K M v w z g h m

/-- The inverse inserts the identity in the inner tensor factor. -/
theorem inductionComp_inv_total_tensor (M : Superfunctor k C (SVec k))
    (v : C) (z : E) (a : K.obj (J.obj v) ⟶ z) (m : M.obj v) :
    ((inductionComp J K).inv.app M).total z (tensor (J ⋙ K) M.toFunctor v a m) =
      tensor K (induced J M).toFunctor (J.obj v) a (tensor J M.toFunctor v (𝟙 _) m) := by
  rw [SuperNatTrans.total, inductionComp_inv_app_one, add_zero]
  exact inductionComp_inv_tensor J K M v z a m

end OddMath.QuiverHecke.ELVOld.BalancedInduction
