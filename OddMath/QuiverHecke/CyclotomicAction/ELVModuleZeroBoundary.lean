import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierFields
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # The zero lower cell inside the module target

The empty boundary of BE (1.14) uses a zero lower E/F cell inside the
same module parity category, rather than a separate zero category.
This supplies that cell and its even right adjunction for the local data.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  (C : Type u) [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

/-- The empty coordinate product is a zero module on the given category. -/
def zeroModule : Superfunctor k C (SVec k) :=
  FiniteSupermodule.product (fun e : Empty => nomatch e)

/-- The zero module has zero identity in the existing module category. -/
theorem zeroModule_id : (𝟙 (zeroModule (k := k) C) : _ ⟶ _) = 0 := by
  apply Superfunctor.hom_ext
  intro p t
  apply SVec.hom_ext
  intro x
  funext e
  exact Empty.elim e

/-- The constant zero functor retains the existing source and target
module categories; it sends both parity components of every map to zero. -/
def zeroModuleFunctor : Superfunctor k C (SVec k) ⥤ Superfunctor k C (SVec k) where
  obj _ := zeroModule C
  map _ := 0
  map_id _ := (zeroModule_id C).symm
  map_comp _ _ := by simp

instance zeroModuleFunctor_additive : (zeroModuleFunctor (k := k) C).Additive where
  map_add := by intros; exact (add_zero _).symm

instance zeroModuleFunctor_linear : (zeroModuleFunctor (k := k) C).Linear k where
  map_smul _ _ := (smul_zero _).symm

instance zeroModuleFunctor_super : IsSuperfunctor k (zeroModuleFunctor (k := k) C) where
  map_mem _ := Submodule.zero_mem _

/-- The zero lower endocell in the canonical module parity target. -/
def zeroModuleCell : inductionModulePiCategory (k := k) C ⟶ inductionModulePiCategory (k := k) C :=
  show Superfunctor k (Superfunctor k C (SVec k)) (Superfunctor k C (SVec k)) from
    ⟨zeroModuleFunctor C⟩

/-- Its identity is literally zero as a supernatural transformation. -/
theorem zeroModuleCell_id : (𝟙 (zeroModuleCell (k := k) C) : _ ⟶ _) = 0 := by
  apply Superfunctor.hom_ext_parity
  · intro M
    exact zeroModule_id C
  · intro M
    rfl

private theorem additive_map_zero_identity
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (a : A) (h : (𝟙 a : a ⟶ a) = 0) :
    (𝟙 (F.obj a) : _ ⟶ _) = 0 := by
  rw [← F.map_id, h, F.map_zero]

/-- Postcomposition by any module-target cell preserves the zero lower
composite. This uses additivity on the original zero module identity. -/
theorem zeroModuleCell_comp_id (B : PiSCat.{u,u,u+1} k)
    (H : inductionModulePiCategory (k := k) C ⟶ B) :
    (𝟙 (zeroModuleCell (k := k) C ≫ H) : _ ⟶ _) = 0 := by
  apply Superfunctor.hom_ext_parity
  · intro M
    exact additive_map_zero_identity H.toFunctor (zeroModule C) (zeroModule_id C)
  · intro M
    rfl

/-- Every transformation whiskered after the zero lower cell vanishes;
this is the zero slide used at the empty boundary. -/
theorem zeroModuleCell_whiskerLeft (B : PiSCat.{u,u,u+1} k)
    {H J : inductionModulePiCategory (k := k) C ⟶ B} (η : H ⟶ J) :
    zeroModuleCell (k := k) C ◁ η = 0 := by
  have h := Category.id_comp (zeroModuleCell (k := k) C ◁ η)
  rw [zeroModuleCell_comp_id C B H, Limits.zero_comp] at h
  exact h.symm

/-- The zero lower cells carry the zero even unit and counit, satisfying
the triangles in the same module parity target. -/
def zeroModuleCellAdjunction :
    SKM.SuperAdjunction (k := k) (zeroModuleCell (k := k) C) (zeroModuleCell (k := k) C) where
  unit := 0
  counit := 0
  unit_mem := Submodule.zero_mem _
  counit_mem := Submodule.zero_mem _
  left_triangle := by
    simp only [TwoSupercategory.zero_whiskerRight (R := k), Limits.comp_zero,
      Limits.zero_comp, zeroModuleCell_id]
  right_triangle := by
    simp only [TwoSupercategory.whiskerLeft_zero (R := k), Limits.comp_zero,
      Limits.zero_comp, zeroModuleCell_id]

end OddMath.QuiverHecke.ELVOld.BalancedInduction
