import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotColumns
import OddMath.QuiverHecke.CyclotomicAction.ELVOldModuleAdjunction
import OddMath.SKM.RouquierShiftedAdjunction

/-! # Shifted finite families and even matrix entries

The parity profiles of SuperSumInvFrom and SuperSumInvTo in
RouquierData encode the evenized forms of Brundan--Ellis (1.13)--(1.14).
For the unit-column matrix the source family is Pi^p(Ind Res M) and
Pi^(r p)M, with target Res Ind M. For the cap-row matrix, after removing
the common source shift, the source is Ind Res M and targets are
Pi^p(Res Ind M) and Pi^(r p)M. All entries below are the existing mate,
unit, counit and induction-dot maps composed with the canonical shift
isomorphisms. This specifies the families and their even maps; their
finite inverse identities are a subsequent step.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.MatrixParity
universe u v
variable {k : Type u} [CommRing k] {C : Type v} [Category C]
  [Preadditive C] [Linear k C] [Supercategory k C]

private theorem homogeneous_total {F G : Superfunctor k C (SVec k)} {p : ZMod 2}
    {x : ∀ t, F.obj t ⟶ G.obj t} (h : IsSupernatural k p x) (t : C) :
    (Superfunctor.homMk h.toSuperNatTrans).total t = x t := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

private theorem total_power {F : Superfunctor k C (SVec k)} (f : End F) (t : C) (n : ℕ) :
    SVec.toLinearMap ((f ^ n).total t) = (SVec.toLinearMap (f.total t)) ^ n := by
  induction n with
  | zero =>
    change SVec.toLinearMap (SuperNatTrans.id F.toFunctor |>.total t) = LinearMap.id
    rw [SuperNatTrans.id_total, SVec.toLinearMap_id]
  | succ n ih =>
    rw [pow_succ, End.mul_def, Superfunctor.comp_total, SVec.toLinearMap_comp, ih, pow_succ]
    rfl

section Shift
variable [PiSupercategory k C]
private def sourceEntry {X Y : C} (p : ZMod 2) (f : X ⟶ Y) :
    (SKM.homParityShift (k := k) p).obj X ⟶ Y :=
  ((SKM.homParityShiftDatum (k := k) p).iso X).hom ≫ f

private theorem sourceEntry_mem {X Y : C} {p : ZMod 2} {f : X ⟶ Y}
    (hf : f ∈ parity (R := k) X Y p) :
    sourceEntry (k := k) p f ∈ parity (R := k) _ _ 0 := by
  simpa only [sourceEntry, zmod2_add_self] using comp_mem
    ((SKM.homParityShiftDatum (k := k) p).hom_mem X) hf

private def targetEntry {X Y : C} (p : ZMod 2) (f : X ⟶ Y) :
    X ⟶ (SKM.homParityShift (k := k) p).obj Y :=
  f ≫ ((SKM.homParityShiftDatum (k := k) p).iso Y).inv

private theorem targetEntry_mem {X Y : C} {p : ZMod 2} {f : X ⟶ Y}
    (hf : f ∈ parity (R := k) X Y p) :
    targetEntry (k := k) p f ∈ parity (R := k) _ _ 0 := by
  simpa only [targetEntry, zmod2_add_self] using comp_mem hf
    ((SKM.homParityShiftDatum (k := k) p).inv_mem Y)
end Shift
end OddMath.QuiverHecke.ELVOld.MatrixParity

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- The homogeneous module map underlying the specified induction dot. -/
def inductionDotModule (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    End ((BalancedInduction.induction (append D Sc cutoff i)).obj M) :=
  BalancedInduction.transformComponent (oldAppendDot_supernatural D Sc cutoff i) M

theorem inductionDotModule_mem (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    inductionDotModule D Sc cutoff i M ∈ parity (R := k) _ _ (D.parity i) :=
  BalancedInduction.transformComponent_mem (oldAppendDot_supernatural D Sc cutoff i) M

theorem inductionDotModule_total (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((inductionDotModule D Sc cutoff i M).total t) = inductionDot D Sc cutoff i M t := by
  exact congrArg SVec.toLinearMap (MatrixParity.homogeneous_total
    (BalancedInduction.transformLinear_supernatural (oldAppendDot_supernatural D Sc cutoff i) M) t)

theorem inductionDotModule_power_total (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) (n : ℕ) :
    SVec.toLinearMap (((inductionDotModule D Sc cutoff i M) ^ n).total t) =
      (inductionDot D Sc cutoff i M t) ^ n := by
  exact (MatrixParity.total_power (inductionDotModule D Sc cutoff i M) t n).trans
    (congrArg (fun f : Module.End k (((BalancedInduction.induction (append D Sc cutoff i)).obj M).obj t) => f ^ n)
      (inductionDotModule_total D Sc cutoff i M t))

theorem inductionDotModule_power_mem (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    (inductionDotModule D Sc cutoff i M) ^ n ∈ parity (R := k) _ _ (n • D.parity i) := by
  induction n with
  | zero =>
    simp only [pow_zero, End.one_def, zero_nsmul]
    exact id_mem _
  | succ n ih =>
    rw [pow_succ, End.mul_def]
    simpa only [succ_nsmul, add_comm] using comp_mem (inductionDotModule_mem D Sc cutoff i M) ih

/-- The ordinary unit followed by the actual restricted induction-dot power. -/
def moduleUnitColumn (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    M ⟶ (BalancedInduction.restriction (append D Sc cutoff i)).obj
      ((BalancedInduction.induction (append D Sc cutoff i)).obj M) :=
  (BalancedInduction.adjunction (append D Sc cutoff i)).unit.app M ≫
    (BalancedInduction.restriction (append D Sc cutoff i)).map ((inductionDotModule D Sc cutoff i M) ^ n)

theorem moduleUnitColumn_mem (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    moduleUnitColumn D Sc cutoff i M n ∈ parity (R := k) _ _ (n • D.parity i) := by
  have h := comp_mem (BalancedInduction.adjunctionUnit_mem (append D Sc cutoff i) M)
    (IsSuperfunctor.map_mem (F := BalancedInduction.restriction (append D Sc cutoff i))
      (inductionDotModule_power_mem D Sc cutoff i M n))
  simpa only [moduleUnitColumn, zero_add] using h

/-- The actual dot power followed by the ordinary adjunction counit. -/
def moduleCapRow (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    (BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) ⟶ M :=
  ((inductionDotModule D Sc cutoff i
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)) ^ n) ≫
      (BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M

theorem moduleCapRow_mem (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    moduleCapRow D Sc cutoff i M n ∈ parity (R := k) _ _ (n • D.parity i) := by
  simpa only [moduleCapRow, add_zero] using comp_mem
    (inductionDotModule_power_mem D Sc cutoff i _ n)
    (BalancedInduction.adjunctionCounit_mem (append D Sc cutoff i) M)

/-- The actual mate component, with fixed ordinary module endpoints. -/
def matrixMateComponent (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) ⟶
    (BalancedInduction.restriction (append D Sc cutoff i)).obj
      ((BalancedInduction.induction (append D Sc cutoff i)).obj M) :=
  (oldModuleMate D Sc cutoff i).app (D.parity i) M

theorem matrixMateComponent_mem (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    matrixMateComponent D Sc cutoff i M ∈ parity (R := k) _ _ (D.parity i) :=
  (oldModuleMate D Sc cutoff i).app_mem (D.parity i) M

/-- The literal finite source summands of the even unit-column matrix. -/
def unitMatrixFamily (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    Option (Fin m) → Superfunctor k (OldCategory D Sc cutoff) (SVec k)
  | none => (SKM.homParityShift (k := k) (C := Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (D.parity i)).obj
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M))
  | some r => (SKM.homParityShift (k := k) (C := Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (r.val • D.parity i)).obj M

/-- Ordinary unit/dot entries with canonical source shifts, without column rescaling. -/
def unitMatrixEntry (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (a : Option (Fin m)) :
    unitMatrixFamily D Sc cutoff i M m a ⟶
      (BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M) :=
  match a with
  | none => MatrixParity.sourceEntry (k := k) (D.parity i) (matrixMateComponent D Sc cutoff i M)
  | some r => MatrixParity.sourceEntry (k := k) (r.val • D.parity i) (moduleUnitColumn D Sc cutoff i M r.val)

theorem unitMatrixEntry_mem (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (a : Option (Fin m)) :
    unitMatrixEntry D Sc cutoff i M m a ∈ parity (R := k) _ _ 0 := by
  cases a with
  | none => exact MatrixParity.sourceEntry_mem (matrixMateComponent_mem D Sc cutoff i M)
  | some r => exact MatrixParity.sourceEntry_mem (moduleUnitColumn_mem D Sc cutoff i M r.val)

/-- The literal finite target summands of the even cap-row matrix. -/
def capMatrixFamily (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    Option (Fin m) → Superfunctor k (OldCategory D Sc cutoff) (SVec k)
  | none => (SKM.homParityShift (k := k) (C := Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (D.parity i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M))
  | some r => (SKM.homParityShift (k := k) (C := Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (r.val • D.parity i)).obj M

/-- Prescribed cap-row entries after canonical target parity transport. -/
def capMatrixEntry (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (a : Option (Fin m)) :
    (BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) ⟶
        capMatrixFamily D Sc cutoff i M m a :=
  match a with
  | none => MatrixParity.targetEntry (k := k) (D.parity i) (matrixMateComponent D Sc cutoff i M)
  | some r => MatrixParity.targetEntry (k := k) (r.val • D.parity i) (moduleCapRow D Sc cutoff i M r.val)

theorem capMatrixEntry_mem (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (a : Option (Fin m)) :
    capMatrixEntry D Sc cutoff i M m a ∈ parity (R := k) _ _ 0 := by
  cases a with
  | none => exact MatrixParity.targetEntry_mem (matrixMateComponent_mem D Sc cutoff i M)
  | some r => exact MatrixParity.targetEntry_mem (moduleCapRow_mem D Sc cutoff i M r.val)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
