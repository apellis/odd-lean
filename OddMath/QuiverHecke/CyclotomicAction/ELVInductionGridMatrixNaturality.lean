import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixFamilies
import OddMath.SKM.RouquierHomPostNaturalInverse

/-! # Input-module naturality of the prescribed changing-content matrix entries

DeformedMatrixComparison (4), (5): the given signed mate, unit/dot columns
and normalized dot/counit rows are supernatural on all input-module maps.
The canonical source or target parity coordinates turn these exact entries
into even natural transformations, including on odd and inhomogeneous maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
section Dots
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)

/-- The given ordered dot powers form a homogeneous input-module family. -/
theorem dotEnd_power_supernatural (n : ℕ) :
    IsSupernatural k (n • p) (F := induction J) (G := induction J)
      (fun M => dotEnd J hα M ^ n) := by
  have hd := transformComponent_supernatural hα
  induction n with
  | zero => simpa only [zero_nsmul, pow_zero, End.one_def] using
      (isSupernatural_id (R := k) (F := induction J))
  | succ n ih =>
    simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm, dotEnd] using hd.comp ih

/-- The ordinary unscaled unit/dot column is supernatural in input maps. -/
theorem unitDotColumn_supernatural (n : ℕ) :
    IsSupernatural k (n • p) (F := 𝟭 (Superfunctor k C (SVec k)))
      (G := induction J ⋙ restriction J) (fun M => unitDotColumn J hα M n) := by
  have hu := isSupernatural_of_natTrans (R := k) (adjunctionUnit J) (adjunctionUnit_mem J)
  simpa only [zero_add, unitDotColumn, adjunction] using hu.comp
    ((dotEnd_power_supernatural J hα n).whiskerRight (restriction J))

/-- The given dot/counit row is supernatural in arbitrary input maps. -/
theorem capDotRow_supernatural (n : ℕ) :
    IsSupernatural k (n • p) (F := restriction J ⋙ induction J)
      (G := 𝟭 (Superfunctor k A (SVec k))) (fun M => capDotRow J hα M n) := by
  have hc := isSupernatural_of_natTrans (R := k) (adjunctionCounit J) (adjunctionCounit_mem J)
  simpa only [add_zero, capDotRow, adjunction] using
    ((dotEnd_power_supernatural J hα n).whiskerLeft (restriction J)).comp hc
end Dots

section Families
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
local instance gridMatrixInputModulePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory

/-- Each literal unit source summand as a functor of the input module. -/
def gridUnitMatrixSummandFunctor (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    Superfunctor k A (SVec k) ⥤ Superfunctor k A (SVec k) :=
  match a with
  | none => (restriction J ⋙ induction J) ⋙ SKM.homParityShift (k := k) p
  | some r => SKM.homParityShift (k := k) (r.val • p)

/-- Each literal cap target summand as a functor of the input module. -/
def gridCapMatrixSummandFunctor (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    Superfunctor k A (SVec k) ⥤ Superfunctor k A (SVec k) :=
  match a with
  | none => (induction K ⋙ restriction K) ⋙ SKM.homParityShift (k := k) p
  | some r => SKM.homParityShift (k := k) (r.val • p)

instance gridUnitMatrixSummandFunctor_additive (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    (gridUnitMatrixSummandFunctor (k := k) J p m a).Additive := by
  cases a <;> dsimp [gridUnitMatrixSummandFunctor] <;> infer_instance
instance gridUnitMatrixSummandFunctor_linear (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    (gridUnitMatrixSummandFunctor (k := k) J p m a).Linear k := by
  cases a <;> dsimp [gridUnitMatrixSummandFunctor] <;> infer_instance
instance gridUnitMatrixSummandFunctor_super (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    IsSuperfunctor k (gridUnitMatrixSummandFunctor (k := k) J p m a) := by
  cases a <;> dsimp [gridUnitMatrixSummandFunctor] <;> infer_instance
instance gridCapMatrixSummandFunctor_additive (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    (gridCapMatrixSummandFunctor (k := k) K p m a).Additive := by
  cases a <;> dsimp [gridCapMatrixSummandFunctor] <;> infer_instance
instance gridCapMatrixSummandFunctor_linear (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    (gridCapMatrixSummandFunctor (k := k) K p m a).Linear k := by
  cases a <;> dsimp [gridCapMatrixSummandFunctor] <;> infer_instance
instance gridCapMatrixSummandFunctor_super (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    IsSuperfunctor k (gridCapMatrixSummandFunctor (k := k) K p m a) := by
  cases a <;> dsimp [gridCapMatrixSummandFunctor] <;> infer_instance

variable {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)

/-- The actual shifted unit fields are natural on ALL input module maps. -/
def gridUnitMatrixEntryNatTrans (m : ℕ) (a : Option (Fin m)) :
    gridUnitMatrixSummandFunctor (k := k) J p m a ⟶ induction (k := k) K ⋙ restriction (k := k) K :=
  match a with
  | none => (SKM.IsSupernatural.shiftSource (orderedGridMateComponent_supernatural J K hγ)).toNatTrans
  | some r => (SKM.IsSupernatural.shiftSource (unitDotColumn_supernatural K hβ r.val)).toNatTrans

/-- The actual shifted cap fields are natural on ALL input module maps. -/
def gridCapMatrixEntryNatTrans (m : ℕ) (a : Option (Fin m)) :
    restriction (k := k) J ⋙ induction (k := k) J ⟶ gridCapMatrixSummandFunctor (k := k) K p m a :=
  match a with
  | none => (SKM.IsSupernatural.shiftTarget (orderedGridMateComponent_supernatural J K hγ)).toNatTrans
  | some r => (SKM.IsSupernatural.shiftTarget (capDotRow_supernatural J hα r.val)).toNatTrans

/-- The input functor has the given literal canonical unit summand. -/
theorem gridUnitMatrixSummandFunctor_obj (q : ZMod 2) (m : ℕ) (a : Option (Fin m))
    (M : Superfunctor k A (SVec k)) :
    (gridUnitMatrixSummandFunctor (k := k) J q m a).obj M = gridUnitMatrixFamily J q M m a := by
  cases a <;> rfl

/-- The input functor has the given literal canonical cap summand. -/
theorem gridCapMatrixSummandFunctor_obj (q : ZMod 2) (m : ℕ) (a : Option (Fin m))
    (M : Superfunctor k A (SVec k)) :
    (gridCapMatrixSummandFunctor (k := k) K q m a).obj M = gridCapMatrixFamily K q M m a := by
  cases a <;> rfl

/-- The natural unit field is exactly the prescribed component, with only
its explicit literal-module endpoint equality. -/
theorem gridUnitMatrixEntryNatTrans_app (m : ℕ) (a : Option (Fin m))
    (M : Superfunctor k A (SVec k)) :
    (gridUnitMatrixEntryNatTrans J K hγ hβ m a).app M =
      eqToHom (gridUnitMatrixSummandFunctor_obj J p m a M) ≫
        gridUnitMatrixEntry J K hγ hβ M m a := by
  cases a <;> exact (Category.id_comp _).symm

/-- The natural cap field is exactly the prescribed component, with only
its explicit literal-module endpoint equality. -/
theorem gridCapMatrixEntryNatTrans_app (m : ℕ) (a : Option (Fin m))
    (M : Superfunctor k A (SVec k)) :
    (gridCapMatrixEntryNatTrans J K hγ hα m a).app M =
      gridCapMatrixEntry J K hγ hα M m a ≫
        eqToHom (gridCapMatrixSummandFunctor_obj K p m a M).symm := by
  cases a <;> exact (Category.comp_id _).symm
end Families
end OddMath.QuiverHecke.ELVOld.BalancedInduction
