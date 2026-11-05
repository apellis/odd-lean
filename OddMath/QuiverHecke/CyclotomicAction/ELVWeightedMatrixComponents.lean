import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixRows
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleMatrixInverse

/-! # Finite matrix components on the weighted quotient

DeformedMatrixComparison (2), (4): the quotient matrices retain the given
ordered mate, ordinary unit and counit, dot powers and canonical parity
coordinates. Their pointwise charts use the selected append comparisons.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  {p : ZMod 2} {α : ∀ s, (A ⋙ A).obj s ⟶ (A ⋙ A).obj s}
  (hα : IsSupernatural k p α)

/-- The canonical flattening transports the crossing as a homogeneous family. -/
theorem doubleCrossComponent_supernatural :
    IsSupernatural k p (F := induction A ⋙ induction A) (G := induction A ⋙ induction A)
      (doubleCrossComponent A hα) := by
  have hL := isSupernatural_of_natTrans (inductionComp (k := k) A A).hom
    (fun M => inductionComp_hom_mem A A M)
  have hT := transformComponent_supernatural hα
  have hR := isSupernatural_of_natTrans (inductionComp (k := k) A A).inv
    (fun M => inductionComp_inv_mem A A M)
  change IsSupernatural k p (F := induction A ⋙ induction A) (G := induction A ⋙ induction A)
    (fun M => (inductionComp A A).hom.app M ≫ transformComponent hα M ≫
      (inductionComp A A).inv.app M)
  simpa only [zero_add, add_zero, Category.assoc] using hL.comp (hT.comp hR)

theorem doubleCrossComponent_mem (M : Superfunctor k C (SVec k)) :
    doubleCrossComponent A hα M ∈ parity (R := k) _ _ p :=
  (doubleCrossComponent_supernatural A hα).mem M

private theorem mateComposite_mem
    {U V W Z : Superfunctor k C (SVec k)}
    (a : U ⟶ V) (b : V ⟶ W) (c : W ⟶ Z)
    (ha : a ∈ parity (R := k) _ _ 0) (hb : b ∈ parity (R := k) _ _ p)
    (hc : c ∈ parity (R := k) _ _ 0) :
    a ≫ b ≫ c ∈ parity (R := k) _ _ p := by
  simpa only [zero_add, add_zero] using comp_mem ha (comp_mem hb hc)

/-- The cup-crossing-cap mate has exactly the crossing degree. -/
theorem orderedMateComponent_mem (M : Superfunctor k C (SVec k)) :
    orderedMateComponent A hα M ∈ parity (R := k) _ _ p := by
  exact mateComposite_mem _ _ _
    (adjunctionUnit_mem A ((induction A).obj ((restriction A).obj M)))
    (IsSuperfunctor.map_mem (F := restriction A)
      (neg_mem (doubleCrossComponent_mem A hα ((restriction A).obj M))))
    (IsSuperfunctor.map_mem (F := restriction A)
      (IsSuperfunctor.map_mem (F := induction A) (adjunctionCounit_mem A M)))

private theorem regrade {F G : Superfunctor k C (SVec k)} {q r : ZMod 2}
    {f : F ⟶ G} (h : q = r) (hf : f ∈ parity (R := k) _ _ q) :
    f ∈ parity (R := k) _ _ r := by
  cases h
  exact hf

private def mateWithFunctorEndpoints (M : Superfunctor k C (SVec k)) :
    induced A ((restriction A).obj M) ⟶ (restriction A).obj (induced A M) :=
  orderedMateComponent A hα M

private theorem mateWithFunctorEndpoints_mem (M : Superfunctor k C (SVec k)) :
    mateWithFunctorEndpoints A hα M ∈ parity (R := k) _ _ p :=
  orderedMateComponent_mem A hα M

private theorem mateWithFunctorEndpoints_regrade (M : Superfunctor k C (SVec k))
    (q : ZMod 2) (hp : p = q) :
    mateWithFunctorEndpoints A hα M ∈ parity (R := k) _ _ q :=
  regrade hp (mateWithFunctorEndpoints_mem A hα M)

private def homogeneousMate (M : Superfunctor k C (SVec k)) (q : ZMod 2) (hp : p = q) :
    parity (R := k) (induced A ((restriction A).obj M))
      ((restriction A).obj (induced A M)) q :=
  ⟨mateWithFunctorEndpoints A hα M, mateWithFunctorEndpoints_regrade A hα M q hp⟩

private def unitColumnNative {q : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s}
    (hδ : IsSupernatural k q δ) (M : Superfunctor k C (SVec k)) (n : ℕ) :
    M ⟶ (restriction A).obj (induced A M) := unitDotColumn A hδ M n
private theorem unitColumn_mem {q : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s}
    (hδ : IsSupernatural k q δ) (M : Superfunctor k C (SVec k)) (n : ℕ) :
    unitColumnNative A hδ M n ∈ parity (R := k) _ _ (n • q) :=
  unitDotColumn_mem A hδ M n
private def capRowNative {q : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s}
    (hδ : IsSupernatural k q δ) (M : Superfunctor k C (SVec k)) (n : ℕ) :
    induced A ((restriction A).obj M) ⟶ M := capDotRow A hδ M n
private theorem capRow_mem {q : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s}
    (hδ : IsSupernatural k q δ) (M : Superfunctor k C (SVec k)) (n : ℕ) :
    capRowNative A hδ M n ∈ parity (R := k) _ _ (n • q) :=
  capDotRow_mem A hδ M n

/-- Endpoint objects are fixed before assembling their canonical parity coordinates. -/
private structure MatrixDatum (q : ZMod 2) where
  value : Superfunctor k C (SVec k)
  source : Superfunctor k C (SVec k)
  target : Superfunctor k C (SVec k)
  mate : parity (R := k) source target q
  columns : ∀ n : ℕ, parity (R := k) value target (n • q)
  rows : ∀ n : ℕ, parity (R := k) source value (n • q)

private def inductionMatrixDatum {q : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s}
    (hδ : IsSupernatural k q δ) (hq : p = q) (M : Superfunctor k C (SVec k)) : MatrixDatum (k := k) (C := C) q where
  value := M
  source := induced A ((restriction A).obj M)
  target := (restriction A).obj (induced A M)
  mate := homogeneousMate A hα M q hq
  columns n := ⟨unitColumnNative A hδ M n, unitColumn_mem A hδ M n⟩
  rows n := ⟨capRowNative A hδ M n, capRow_mem A hδ M n⟩

/-- The given matrix datum retains the entire ordered mate before the
functor and module parameters are specialized. -/
theorem inductionMatrixMate_eq {q : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s}
    (hδ : IsSupernatural k q δ) (hq : p = q) (M : Superfunctor k C (SVec k)) :
    (inductionMatrixDatum A hα hδ hq M).mate.val = orderedMateComponent A hα M := rfl

local instance matrixDatumPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

private def datumUnitFamily {q : ZMod 2} (B : MatrixDatum (k := k) (C := C) q) (m : ℕ) :
    Option (Fin m) → Superfunctor k C (SVec k)
  | none => (SKM.homParityShift (k := k) q).obj B.source
  | some r => (SKM.homParityShift (k := k) (r.val • q)).obj B.value
private def datumCapFamily {q : ZMod 2} (B : MatrixDatum (k := k) (C := C) q) (m : ℕ) :
    Option (Fin m) → Superfunctor k C (SVec k)
  | none => (SKM.homParityShift (k := k) q).obj B.target
  | some r => (SKM.homParityShift (k := k) (r.val • q)).obj B.value
private def datumUnitEntry {q : ZMod 2} (B : MatrixDatum (k := k) (C := C) q) (m : ℕ) (a : Option (Fin m)) :
    datumUnitFamily B m a ⟶ B.target :=
  match a with
  | none => ((SKM.homParityShiftDatum (k := k) q).iso B.source).hom ≫ B.mate.val
  | some r => ((SKM.homParityShiftDatum (k := k) (r.val • q)).iso B.value).hom ≫ (B.columns r.val).val
private def datumCapEntry {q : ZMod 2} (B : MatrixDatum (k := k) (C := C) q) (m : ℕ) (a : Option (Fin m)) :
    B.source ⟶ datumCapFamily B m a :=
  match a with
  | none => B.mate.val ≫ ((SKM.homParityShiftDatum (k := k) q).iso B.target).inv
  | some r => (B.rows r.val).val ≫ ((SKM.homParityShiftDatum (k := k) (r.val • q)).iso B.value).inv
private theorem datumUnitEntry_mem {q : ZMod 2} (B : MatrixDatum (k := k) (C := C) q) (m : ℕ) (a : Option (Fin m)) :
    datumUnitEntry B m a ∈ parity (R := k) _ _ 0 := by
  cases a with
  | none =>
    dsimp only [datumUnitEntry, datumUnitFamily]
    simpa only [zmod2_add_self] using comp_mem
      ((SKM.homParityShiftDatum (k := k) q).hom_mem B.source) B.mate.property
  | some r =>
    dsimp only [datumUnitEntry, datumUnitFamily]
    simpa only [zmod2_add_self] using comp_mem
      ((SKM.homParityShiftDatum (k := k) (r.val • q)).hom_mem B.value) (B.columns r.val).property
private theorem datumCapEntry_mem {q : ZMod 2} (B : MatrixDatum (k := k) (C := C) q) (m : ℕ) (a : Option (Fin m)) :
    datumCapEntry B m a ∈ parity (R := k) _ _ 0 := by
  cases a with
  | none =>
    dsimp only [datumCapEntry, datumCapFamily]
    simpa only [zmod2_add_self] using comp_mem B.mate.property
      ((SKM.homParityShiftDatum (k := k) q).inv_mem B.target)
  | some r =>
    dsimp only [datumCapEntry, datumCapFamily]
    simpa only [zmod2_add_self] using comp_mem (B.rows r.val).property
      ((SKM.homParityShiftDatum (k := k) (r.val • q)).inv_mem B.value)

/-- The actual first source-shifted field evaluates to the prescribed raw mate. -/
theorem inductionUnitMatrixEntry_none_total {q : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s}
    (hδ : IsSupernatural k q δ) (hq : p = q) (M : Superfunctor k C (SVec k)) (m : ℕ) (w : C) :
    SVec.toLinearMap ((datumUnitEntry (inductionMatrixDatum A hα hδ hq M) m none).total w) =
      orderedMateLinear A hα M w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso
          (induced A ((restriction A).obj M))).hom.total w) := by
  dsimp only [datumUnitEntry]
  rw [Superfunctor.comp_total]
  rfl

/-- Every actual source-shifted unit field evaluates to its unscaled raw unit/dot column. -/
theorem inductionUnitMatrixEntry_some_total {q : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s}
    (hδ : IsSupernatural k q δ) (hq : p = q) (M : Superfunctor k C (SVec k))
    (m : ℕ) (r : Fin m) (w : C) :
    SVec.toLinearMap ((datumUnitEntry (inductionMatrixDatum A hα hδ hq M) m (some r)).total w) =
      unitDotLinear A hδ M r.val w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • q)).iso M).hom.total w) := by
  dsimp only [datumUnitEntry, inductionMatrixDatum, unitColumnNative]
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp, unitDotColumn_total]

/-- The actual first target-shifted field evaluates to the prescribed raw mate. -/
theorem inductionCapMatrixEntry_none_total {q : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s}
    (hδ : IsSupernatural k q δ) (hq : p = q) (M : Superfunctor k C (SVec k)) (m : ℕ) (w : C) :
    SVec.toLinearMap ((datumCapEntry (inductionMatrixDatum A hα hδ hq M) m none).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso
        ((restriction A).obj (induced A M))).inv.total w) ∘ₗ orderedMateLinear A hα M w := by
  dsimp only [datumCapEntry]
  rw [Superfunctor.comp_total]
  rfl

/-- Every actual target-shifted cap field evaluates to its unscaled raw dot/counit row. -/
theorem inductionCapMatrixEntry_some_total {q : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s}
    (hδ : IsSupernatural k q δ) (hq : p = q) (M : Superfunctor k C (SVec k))
    (m : ℕ) (r : Fin m) (w : C) :
    SVec.toLinearMap ((datumCapEntry (inductionMatrixDatum A hα hδ hq M) m (some r)).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • q)).iso M).inv.total w) ∘ₗ
        capDotLinear A hδ M r.val w := by
  dsimp only [datumCapEntry, inductionMatrixDatum, capRowNative]
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp, capDotRow_total]

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "T" => truncatedAppend D Sc cutoff N [i]
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
private theorem parity_square (p : ZMod 2) : p * p = p := by
  rcases parity_eq_zero_or_one p with h | h <;> simp only [h, mul_zero, one_mul]
private def weightedMatrixDatum :=
  BalancedInduction.inductionMatrixDatum T
    (truncatedEqualCross_supernatural D Sc cutoff N i)
    (truncatedDot_supernatural D Sc cutoff N i) (parity_square (D.parity i)) M
local notation "B" => weightedMatrixDatum D Sc cutoff N i M

/-- The prescribed cup-crossing-cap mate with its original crossing parameter. -/
def weightedMatrixMate := (B).mate.val

theorem weightedMatrixMate_mem : weightedMatrixMate D Sc cutoff N i M ∈ parity (R := k) _ _ (D.parity i) :=
  (B).mate.property

/-- The weighted matrix uses the literal prescribed ordered mate as a
whole module map, with no change of sign or parity convention. -/
theorem weightedMatrixMate_eq_ordered :
    weightedMatrixMate D Sc cutoff N i M =
      BalancedInduction.orderedMateComponent T
        (truncatedEqualCross_supernatural D Sc cutoff N i) M :=
  BalancedInduction.inductionMatrixMate_eq T
    (truncatedEqualCross_supernatural D Sc cutoff N i)
    (truncatedDot_supernatural D Sc cutoff N i) (parity_square (D.parity i)) M

/-- Canonical source parity coordinates, including every unscaled unit column. -/
def weightedUnitMatrixFamily (m : ℕ) := BalancedInduction.datumUnitFamily (B) m
/-- Canonical target parity coordinates, including every unscaled cap row. -/
def weightedCapMatrixFamily (m : ℕ) := BalancedInduction.datumCapFamily (B) m
/-- The prescribed mate and ordinary unit/dot columns in those source coordinates. -/
def weightedUnitMatrixEntry (m : ℕ) (a : Option (Fin m)) := BalancedInduction.datumUnitEntry (B) m a
/-- The prescribed mate and ordinary dot/counit rows in those target coordinates. -/
def weightedCapMatrixEntry (m : ℕ) (a : Option (Fin m)) := BalancedInduction.datumCapEntry (B) m a

theorem weightedUnitMatrixEntry_mem (m : ℕ) (a : Option (Fin m)) :
    weightedUnitMatrixEntry D Sc cutoff N i M m a ∈ parity (R := k) _ _ 0 :=
  BalancedInduction.datumUnitEntry_mem (B) m a

theorem weightedCapMatrixEntry_mem (m : ℕ) (a : Option (Fin m)) :
    weightedCapMatrixEntry D Sc cutoff N i M m a ∈ parity (R := k) _ _ 0 :=
  BalancedInduction.datumCapEntry_mem (B) m a

local instance weightedMatrixComponentPi : PiSupercategory k (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :=
  supermodulePiSupercategory

/-- The first unit entry is exactly the given mate in its canonical source coordinate. -/
theorem weightedUnitMatrixEntry_none (m : ℕ) :
    weightedUnitMatrixEntry D Sc cutoff N i M m none =
      ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
        (BalancedInduction.induced T ((BalancedInduction.restriction T).obj M))).hom ≫
          weightedMatrixMate D Sc cutoff N i M := rfl
/-- Every remaining unit entry is the given ordinary unit/dot column, unscaled. -/
theorem weightedUnitMatrixEntry_some (m : ℕ) (r : Fin m) :
    weightedUnitMatrixEntry D Sc cutoff N i M m (some r) =
      ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom ≫
        BalancedInduction.unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) M r.val := rfl
/-- The first cap entry is exactly the given mate in its canonical target coordinate. -/
theorem weightedCapMatrixEntry_none (m : ℕ) :
    weightedCapMatrixEntry D Sc cutoff N i M m none =
      weightedMatrixMate D Sc cutoff N i M ≫
        ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
          ((BalancedInduction.restriction T).obj (BalancedInduction.induced T M))).inv := rfl
/-- Every remaining cap entry is the given ordinary dot/counit row, unscaled. -/
theorem weightedCapMatrixEntry_some (m : ℕ) (r : Fin m) :
    weightedCapMatrixEntry D Sc cutoff N i M m (some r) =
      BalancedInduction.capDotRow T (truncatedDot_supernatural D Sc cutoff N i) M r.val ≫
        ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).inv := rfl

/-- Finite source with the prescribed pointwise parity grading. -/
def weightedUnitMatrixSourceSpace (m : ℕ) (w : TruncatedCategory D Sc cutoff N) : SVec k :=
  OddMath.FiniteSuperspace.product fun a => (weightedUnitMatrixFamily D Sc cutoff N i M m a).obj w

/-- Finite target with the prescribed pointwise parity grading. -/
def weightedCapMatrixTargetSpace (m : ℕ) (w : TruncatedCategory D Sc cutoff N) : SVec k :=
  OddMath.FiniteSuperspace.product fun a => (weightedCapMatrixFamily D Sc cutoff N i M m a).obj w

/-- The finite prescribed unit matrix on the quotient module. -/
def weightedUnitMatrixComponent (m : ℕ) (w : TruncatedCategory D Sc cutoff N) :
    weightedUnitMatrixSourceSpace D Sc cutoff N i M m w ⟶ ((B).target).obj w :=
  OddMath.FiniteSuperspace.assembleColumns _ _ fun a =>
    (weightedUnitMatrixEntry D Sc cutoff N i M m a).total w

/-- The finite prescribed cap matrix on the quotient module. -/
def weightedCapMatrixComponent (m : ℕ) (w : TruncatedCategory D Sc cutoff N) :
    ((B).source).obj w ⟶ weightedCapMatrixTargetSpace D Sc cutoff N i M m w :=
  OddMath.FiniteSuperspace.assembleRows _ _ fun a =>
    (weightedCapMatrixEntry D Sc cutoff N i M m a).total w

private theorem total_even {C : Type u} [Category.{u} C] [Preadditive C]
    [Linear k C] [Supercategory k C] {F G : Superfunctor k C (SVec k)}
    (f : F ⟶ G) (h : f ∈ parity (R := k) _ _ 0) (w : C) :
    f.total w ∈ parity (R := k) _ _ 0 := by
  have hz := Superfunctor.app_eq_zero_of_mem h (by decide : (1 : ZMod 2) ≠ 0) w
  simpa only [SuperNatTrans.total, hz, add_zero] using f.app_mem 0 w

end OddMath.QuiverHecke.ELVOld
