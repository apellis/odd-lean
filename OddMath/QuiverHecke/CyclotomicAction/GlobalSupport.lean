/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ContentSupport
import OddMath.QuiverHecke.CyclotomicAction.SuperDot

/-!
# Supercategories on cyclotomic content blocks

Ports the block-category part of
`Categorification/KLR/CyclotomicAction/Global.lean`. Full content subcategories
retain the entire even/odd decomposition of morphisms. Their induction is the
restriction of the genuine balanced-tensor superfunctor, not its even shadow.
The odd dot restricts as a supernatural transformation with the same parity.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v w

section Full
variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
  [Preadditive C] [Linear k C] [Supercategory k C] (P : ObjectProperty C)

/-- The full-subcategory wrapper does not change the morphism superspace. -/
def fullHomEquiv (M N : P.FullSubcategory) : (M ⟶ N) ≃ₗ[k] (M.obj ⟶ N.obj) where
  toFun f := f.hom
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Full subcategories inherit the supercategory structure. -/
instance fullSupercategory : Supercategory k P.FullSubcategory where
  parity M N p := (parity (R := k) M.obj N.obj p).comap (fullHomEquiv P M N).toLinearMap
  isInternal M N := by
    have hu : (Set.univ : Set (ZMod 2)) = {0, 1} := by ext p; fin_cases p <;> simp
    apply (DirectSum.isInternal_submodule_iff_isCompl _ (by decide : (0 : ZMod 2) ≠ 1) hu).mpr
    have hc := (isInternal (R := k) M.obj N.obj).isCompl
      (by decide : (0 : ZMod 2) ≠ 1) hu
    simpa only [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm] using
      Submodule.isCompl_map (fullHomEquiv P M N).symm hc
  id_mem M := id_mem M.obj
  comp_mem hf hg := comp_mem hf hg

@[simp] theorem full_mem {M N : P.FullSubcategory} (f : M ⟶ N) (p : ZMod 2) :
    f ∈ parity (R := k) M N p ↔ f.hom ∈ parity (R := k) M.obj N.obj p := Iff.rfl

variable {C' : Type*} [Category C'] [Preadditive C'] [Linear k C'] [Supercategory k C']
  (Q : ObjectProperty C')

/-- A superfunctor preserving an object property restricts to full supercategories. -/
def fullLift (F : C ⥤ C') (hF : ∀ M, P M → Q (F.obj M)) :
    P.FullSubcategory ⥤ Q.FullSubcategory where
  obj M := ⟨F.obj M.obj, hF M.obj M.property⟩
  map f := ⟨F.map f.hom⟩
  map_id M := InducedCategory.hom_ext (F.map_id M.obj)
  map_comp f g := InducedCategory.hom_ext (F.map_comp f.hom g.hom)

instance (F : C ⥤ C') (hF : ∀ M, P M → Q (F.obj M)) [F.Additive] :
    (fullLift P Q F hF).Additive where
  map_add := by intros; apply InducedCategory.hom_ext; exact F.map_add

instance (F : C ⥤ C') (hF : ∀ M, P M → Q (F.obj M)) [F.Additive] [F.Linear k] :
    (fullLift P Q F hF).Linear k where
  map_smul f r := InducedCategory.hom_ext (F.map_smul r f.hom)

instance (F : C ⥤ C') (hF : ∀ M, P M → Q (F.obj M))
    [F.Additive] [F.Linear k] [IsSuperfunctor k F] : IsSuperfunctor k (fullLift P Q F hF) where
  map_mem hf := IsSuperfunctor.map_mem (F := F) hf

/-- Restriction preserves both homogeneous components and their Koszul naturality. -/
def fullLiftTrans {F G : C ⥤ C'} (hF : ∀ M, P M → Q (F.obj M))
    (hG : ∀ M, P M → Q (G.obj M)) (η : SuperNatTrans k F G) :
    SuperNatTrans k (fullLift P Q F hF) (fullLift P Q G hG) where
  app p M := ⟨η.app p M.obj⟩
  app_mem p M := η.app_mem p M.obj
  naturality p _ _ _ f hf := InducedCategory.hom_ext (η.naturality p f.hom hf)

theorem fullLiftTrans_homogeneous {F G : C ⥤ C'} (hF : ∀ M, P M → Q (F.obj M))
    (hG : ∀ M, P M → Q (G.obj M)) (η : SuperNatTrans k F G) {p : ZMod 2}
    (hη : η.IsHomogeneous p) : (fullLiftTrans P Q hF hG η).IsHomogeneous p := by
  intro q hq
  funext M
  exact InducedCategory.hom_ext (congrFun (hη q hq) M.obj)

end Full

universe x
variable {I k : Type u} {X : Type x} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
  (i : I) (n : ℕ) (β : Multiset I)

instance contentInduction_additive :
    (cyclotomicContentInduction D Sc a ha i n β).Additive where
  map_add := by
    intros
    apply InducedCategory.hom_ext
    exact (cyclotomicSuperInduction D Sc i a ha n).map_add

instance contentInduction_linear :
    (cyclotomicContentInduction D Sc a ha i n β).Linear k where
  map_smul f r := InducedCategory.hom_ext
    ((cyclotomicSuperInduction D Sc i a ha n).map_smul r f.hom)

instance contentInduction_super :
    IsSuperfunctor k (cyclotomicContentInduction D Sc a ha i n β) where
  map_mem := by
    intro M N p f hf
    change f.hom ∈ parity (R := k) M.obj N.obj p at hf
    change (cyclotomicSuperInduction D Sc i a ha n).map f.hom ∈
      parity (R := k) _ _ p
    exact IsSuperfunctor.map_mem (F := cyclotomicSuperInduction D Sc i a ha n) hf

/-- Balanced-tensor induction restricted to its content superspaces. -/
def globalBlockInduction :
    Superfunctor k (CyclotomicContentModules D Sc a ha n β)
      (CyclotomicContentModules D Sc a ha (n + 1) ({i} + β)) :=
  ⟨cyclotomicContentInduction D Sc a ha i n β⟩

/-- The concrete last dot retains signed naturality on each content block. -/
def globalBlockDot : globalBlockInduction D Sc a ha i n β ⟶
    globalBlockInduction D Sc a ha i n β where
  app p M := ⟨(cyclotomicSuperInductionDot D Sc i a ha n).app p M.obj⟩
  app_mem p M := (cyclotomicSuperInductionDot D Sc i a ha n).app_mem p M.obj
  naturality p _ _ _ f hf := InducedCategory.hom_ext
    ((cyclotomicSuperInductionDot D Sc i a ha n).naturality p f.hom hf)

theorem globalBlockDot_homogeneous :
    (globalBlockDot D Sc a ha i n β).IsHomogeneous (D.parity i) := by
  intro p hp
  funext M
  apply InducedCategory.hom_ext
  exact congrFun (cyclotomicSuperInductionDot_homogeneous D Sc i a ha n p hp) M.obj

end OddMath.QuiverHecke.CyclotomicAction
