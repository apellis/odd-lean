import OddMath.QuiverHecke.CyclotomicAction.ELVInductionMatrixNaturality
import OddMath.Algebra.FiniteSupermoduleFamily

/-! # Weighted matrix families functorial in their input modules

Brundan–Ellis (1.13)–(1.14): canonical parity coordinates turn the
prescribed mate and dotted unit/counit fields into natural transformations
on the entire weighted module category, including odd input maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "T" => truncatedAppend D Sc cutoff N [i]
local instance weightedFunctorPi : PiSupercategory k (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :=
  supermodulePiSupercategory

private theorem mate_family :
    IsSupernatural k (D.parity i) (F := restriction T ⋙ induction T)
      (G := induction T ⋙ restriction T) (weightedMatrixMate D Sc cutoff N i) := by
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp only [h, mul_zero, one_mul]
  exact inductionMatrixMate_supernatural T
    (truncatedEqualCross_supernatural D Sc cutoff N i)
    (truncatedDot_supernatural D Sc cutoff N i) hp

/-- Each prescribed unit source coordinate, functorially in the input. -/
def weightedUnitMatrixSummandFunctor (m : ℕ) (a : Option (Fin m)) :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) ⥤
      Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) :=
  match a with
  | none => (restriction T ⋙ induction T) ⋙ SKM.homParityShift (k := k) (D.parity i)
  | some r => SKM.homParityShift (k := k) (r.val • D.parity i)

/-- Each prescribed cap target coordinate, functorially in the input. -/
def weightedCapMatrixSummandFunctor (m : ℕ) (a : Option (Fin m)) :
    Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) ⥤
      Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k) :=
  match a with
  | none => (induction T ⋙ restriction T) ⋙ SKM.homParityShift (k := k) (D.parity i)
  | some r => SKM.homParityShift (k := k) (r.val • D.parity i)

instance (m : ℕ) (a : Option (Fin m)) :
    (weightedUnitMatrixSummandFunctor D Sc cutoff N i m a).Additive := by
  cases a <;> dsimp [weightedUnitMatrixSummandFunctor] <;> infer_instance
instance (m : ℕ) (a : Option (Fin m)) :
    (weightedCapMatrixSummandFunctor D Sc cutoff N i m a).Additive := by
  cases a <;> dsimp [weightedCapMatrixSummandFunctor] <;> infer_instance
instance (m : ℕ) (a : Option (Fin m)) :
    (weightedUnitMatrixSummandFunctor D Sc cutoff N i m a).Linear k := by
  cases a <;> dsimp [weightedUnitMatrixSummandFunctor] <;> infer_instance
instance (m : ℕ) (a : Option (Fin m)) :
    (weightedCapMatrixSummandFunctor D Sc cutoff N i m a).Linear k := by
  cases a <;> dsimp [weightedCapMatrixSummandFunctor] <;> infer_instance

instance (m : ℕ) (a : Option (Fin m)) :
    IsSuperfunctor k (weightedUnitMatrixSummandFunctor D Sc cutoff N i m a) := by
  cases a <;> dsimp [weightedUnitMatrixSummandFunctor] <;> infer_instance
instance (m : ℕ) (a : Option (Fin m)) :
    IsSuperfunctor k (weightedCapMatrixSummandFunctor D Sc cutoff N i m a) := by
  cases a <;> dsimp [weightedCapMatrixSummandFunctor] <;> infer_instance

/-- The literal parity-shifted unit entries are natural in arbitrary input maps. -/
def weightedUnitMatrixEntryNatTrans (m : ℕ) (a : Option (Fin m)) :
    weightedUnitMatrixSummandFunctor D Sc cutoff N i m a ⟶ induction T ⋙ restriction T :=
  match a with
  | none => (SKM.IsSupernatural.shiftSource (mate_family D Sc cutoff N i)).toNatTrans
  | some r => (SKM.IsSupernatural.shiftSource
      (unitDotColumn_supernatural T (truncatedDot_supernatural D Sc cutoff N i) r.val)).toNatTrans

/-- The literal parity-shifted cap entries are natural in arbitrary input maps. -/
def weightedCapMatrixEntryNatTrans (m : ℕ) (a : Option (Fin m)) :
    restriction T ⋙ induction T ⟶ weightedCapMatrixSummandFunctor D Sc cutoff N i m a :=
  match a with
  | none => (SKM.IsSupernatural.shiftTarget (mate_family D Sc cutoff N i)).toNatTrans
  | some r => (SKM.IsSupernatural.shiftTarget
      (capDotRow_supernatural T (truncatedDot_supernatural D Sc cutoff N i) r.val)).toNatTrans

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))

theorem weightedUnitMatrixSummandFunctor_obj (m : ℕ) (a : Option (Fin m)) :
    (weightedUnitMatrixSummandFunctor D Sc cutoff N i m a).obj M =
      weightedUnitMatrixFamily D Sc cutoff N i M m a := by
  cases a <;> rfl

theorem weightedCapMatrixSummandFunctor_obj (m : ℕ) (a : Option (Fin m)) :
    (weightedCapMatrixSummandFunctor D Sc cutoff N i m a).obj M =
      weightedCapMatrixFamily D Sc cutoff N i M m a := by
  cases a <;> rfl

theorem weightedUnitMatrixEntryNatTrans_app (m : ℕ) (a : Option (Fin m)) :
    (weightedUnitMatrixEntryNatTrans D Sc cutoff N i m a).app M =
      eqToHom (weightedUnitMatrixSummandFunctor_obj D Sc cutoff N i M m a) ≫
        weightedUnitMatrixEntry D Sc cutoff N i M m a := by
  cases a <;> exact (Category.id_comp _).symm

theorem weightedCapMatrixEntryNatTrans_app (m : ℕ) (a : Option (Fin m)) :
    (weightedCapMatrixEntryNatTrans D Sc cutoff N i m a).app M =
      weightedCapMatrixEntry D Sc cutoff N i M m a ≫
        eqToHom (weightedCapMatrixSummandFunctor_obj D Sc cutoff N i M m a).symm := by
  cases a <;> exact (Category.comp_id _).symm

end OddMath.QuiverHecke.ELVOld
