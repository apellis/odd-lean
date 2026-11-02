import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedMatrixFamilies
import OddMath.SKM.RouquierHomPostNaturalInverse

/-! # Input-module naturality of the prescribed matrix entries

DeformedMatrixComparison section 4 requires input-module naturality as
well as output-arrow naturality. The prescribed mate, dotted units and
dotted caps are homogeneous supernatural families. Their literal parity
shifts make even natural transformations on the entire old module category.
No module map is assumed even.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- Literal ordered dot powers are supernatural in arbitrary homogeneous module maps. -/
theorem inductionDotModule_power_supernatural (i : I) (n : ℕ) :
    IsSupernatural k (n • D.parity i)
      (F := BalancedInduction.induction (append D Sc cutoff i))
      (G := BalancedInduction.induction (append D Sc cutoff i))
      (fun M => inductionDotModule D Sc cutoff i M ^ n) := by
  have hd := BalancedInduction.transformComponent_supernatural (oldAppendDot_supernatural D Sc cutoff i)
  induction n with
  | zero => simpa only [zero_nsmul, pow_zero, End.one_def] using
      (isSupernatural_id (R := k) (F := BalancedInduction.induction (append D Sc cutoff i)))
  | succ n ih =>
    simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm, inductionDotModule] using hd.comp ih

/-- The ordinary dotted unit is supernatural in the input module. -/
theorem moduleUnitColumn_supernatural (i : I) (n : ℕ) :
    IsSupernatural k (n • D.parity i)
      (F := 𝟭 (Superfunctor k (OldCategory D Sc cutoff) (SVec k)))
      (G := BalancedInduction.induction (append D Sc cutoff i) ⋙
        BalancedInduction.restriction (append D Sc cutoff i))
      (fun M => moduleUnitColumn D Sc cutoff i M n) := by
  have hu := isSupernatural_of_natTrans (R := k)
    (BalancedInduction.adjunctionUnit (append D Sc cutoff i))
    (BalancedInduction.adjunctionUnit_mem (append D Sc cutoff i))
  simpa only [zero_add, moduleUnitColumn, BalancedInduction.adjunction] using hu.comp
    ((inductionDotModule_power_supernatural D Sc cutoff i n).whiskerRight
      (BalancedInduction.restriction (append D Sc cutoff i)))

/-- The ordinary dotted counit is supernatural in the input module. -/
theorem moduleCapRow_supernatural (i : I) (n : ℕ) :
    IsSupernatural k (n • D.parity i)
      (F := BalancedInduction.restriction (append D Sc cutoff i) ⋙
        BalancedInduction.induction (append D Sc cutoff i))
      (G := 𝟭 (Superfunctor k (OldCategory D Sc cutoff) (SVec k)))
      (fun M => moduleCapRow D Sc cutoff i M n) := by
  have hc := isSupernatural_of_natTrans (R := k)
    (BalancedInduction.adjunctionCounit (append D Sc cutoff i))
    (BalancedInduction.adjunctionCounit_mem (append D Sc cutoff i))
  simpa only [add_zero, moduleCapRow, BalancedInduction.adjunction] using
    ((inductionDotModule_power_supernatural D Sc cutoff i n).whiskerLeft
      (BalancedInduction.restriction (append D Sc cutoff i))).comp hc

/-- The fixed cup-crossing-cap mate retains its prescribed supernatural parity. -/
theorem matrixMateComponent_supernatural (i : I) :
    IsSupernatural k (D.parity i)
      (F := BalancedInduction.restriction (append D Sc cutoff i) ⋙
        BalancedInduction.induction (append D Sc cutoff i))
      (G := BalancedInduction.induction (append D Sc cutoff i) ⋙
        BalancedInduction.restriction (append D Sc cutoff i))
      (matrixMateComponent D Sc cutoff i) :=
  (oldModuleMate D Sc cutoff i).isSupernatural (D.parity i)

/-- Each prescribed shifted unit summand, functorially in the input module. -/
def unitMatrixSummandFunctor (i : I) (m : ℕ) (a : Option (Fin m)) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) ⥤
      Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  match a with
  | none => (BalancedInduction.restriction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff i)) ⋙ SKM.homParityShift (k := k) (D.parity i)
  | some r => SKM.homParityShift (k := k) (r.val • D.parity i)

/-- Each prescribed shifted cap summand, functorially in the input module. -/
def capMatrixSummandFunctor (i : I) (m : ℕ) (a : Option (Fin m)) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) ⥤
      Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  match a with
  | none => (BalancedInduction.induction (append D Sc cutoff i) ⋙
      BalancedInduction.restriction (append D Sc cutoff i)) ⋙ SKM.homParityShift (k := k) (D.parity i)
  | some r => SKM.homParityShift (k := k) (r.val • D.parity i)

instance (i : I) (m : ℕ) (a : Option (Fin m)) :
    (unitMatrixSummandFunctor D Sc cutoff i m a).Additive := by
  cases a <;> dsimp [unitMatrixSummandFunctor] <;> infer_instance

instance (i : I) (m : ℕ) (a : Option (Fin m)) :
    (unitMatrixSummandFunctor D Sc cutoff i m a).Linear k := by
  cases a <;> dsimp [unitMatrixSummandFunctor] <;> infer_instance

instance (i : I) (m : ℕ) (a : Option (Fin m)) :
    IsSuperfunctor k (unitMatrixSummandFunctor D Sc cutoff i m a) := by
  cases a <;> dsimp [unitMatrixSummandFunctor] <;> infer_instance

instance (i : I) (m : ℕ) (a : Option (Fin m)) :
    (capMatrixSummandFunctor D Sc cutoff i m a).Additive := by
  cases a <;> dsimp [capMatrixSummandFunctor] <;> infer_instance

instance (i : I) (m : ℕ) (a : Option (Fin m)) :
    (capMatrixSummandFunctor D Sc cutoff i m a).Linear k := by
  cases a <;> dsimp [capMatrixSummandFunctor] <;> infer_instance

instance (i : I) (m : ℕ) (a : Option (Fin m)) :
    IsSuperfunctor k (capMatrixSummandFunctor D Sc cutoff i m a) := by
  cases a <;> dsimp [capMatrixSummandFunctor] <;> infer_instance

/-- Literal shifted unit entries are natural even along odd input-module maps. -/
def unitMatrixEntryNatTrans (i : I) (m : ℕ) (a : Option (Fin m)) :
    unitMatrixSummandFunctor D Sc cutoff i m a ⟶
      BalancedInduction.induction (append D Sc cutoff i) ⋙
        BalancedInduction.restriction (append D Sc cutoff i) :=
  match a with
  | none => (SKM.IsSupernatural.shiftSource (matrixMateComponent_supernatural D Sc cutoff i)).toNatTrans
  | some r => (SKM.IsSupernatural.shiftSource (moduleUnitColumn_supernatural D Sc cutoff i r.val)).toNatTrans

/-- Literal shifted cap entries are natural even along odd input-module maps. -/
def capMatrixEntryNatTrans (i : I) (m : ℕ) (a : Option (Fin m)) :
    BalancedInduction.restriction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff i) ⟶
        capMatrixSummandFunctor D Sc cutoff i m a :=
  match a with
  | none => (SKM.IsSupernatural.shiftTarget (matrixMateComponent_supernatural D Sc cutoff i)).toNatTrans
  | some r => (SKM.IsSupernatural.shiftTarget (moduleCapRow_supernatural D Sc cutoff i r.val)).toNatTrans

/-- The functorial unit coordinate has exactly the prescribed shifted module. -/
theorem unitMatrixSummandFunctor_obj (i : I) (m : ℕ) (a : Option (Fin m))
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (unitMatrixSummandFunctor D Sc cutoff i m a).obj M = unitMatrixFamily D Sc cutoff i M m a := by
  cases a <;> rfl

/-- The functorial cap coordinate has exactly the prescribed shifted module. -/
theorem capMatrixSummandFunctor_obj (i : I) (m : ℕ) (a : Option (Fin m))
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (capMatrixSummandFunctor D Sc cutoff i m a).obj M = capMatrixFamily D Sc cutoff i M m a := by
  cases a <;> rfl

/-- Naturality uses the inverted unit entries, with only the explicit endpoint equality. -/
theorem unitMatrixEntryNatTrans_app (i : I) (m : ℕ) (a : Option (Fin m))
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (unitMatrixEntryNatTrans D Sc cutoff i m a).app M =
      eqToHom (unitMatrixSummandFunctor_obj D Sc cutoff i m a M) ≫
        unitMatrixEntry D Sc cutoff i M m a := by
  cases a <;> exact (Category.id_comp _).symm

/-- Naturality uses the inverted cap entries, with only the explicit endpoint equality. -/
theorem capMatrixEntryNatTrans_app (i : I) (m : ℕ) (a : Option (Fin m))
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (capMatrixEntryNatTrans D Sc cutoff i m a).app M =
      capMatrixEntry D Sc cutoff i M m a ≫
        eqToHom (capMatrixSummandFunctor_obj D Sc cutoff i m a M).symm := by
  cases a <;> exact (Category.comp_id _).symm

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
