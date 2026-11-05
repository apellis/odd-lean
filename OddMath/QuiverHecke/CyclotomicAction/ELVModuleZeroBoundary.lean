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

end OddMath.QuiverHecke.ELVOld.BalancedInduction
