import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend
import OddMath.QuiverHecke.CyclotomicAction.KernelMatrixEvaluation
import Mathlib.LinearAlgebra.Pi
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import Mathlib.CategoryTheory.Comma.Arrow
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockExtension
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.Algebra.SupermoduleIsoOfBijectiveTotals

/-!
# Weighted matrix

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Finite matrix components on the weighted quotient

DeformedMatrixComparison (2), (4): the quotient matrices retain the given
ordered mate, ordinary unit and counit, dot powers and canonical parity
coordinates. Their pointwise charts use the selected append comparisons.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
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

end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Charts and row comparison for weighted matrices

DeformedMatrixComparison (2), (4) compares the given arbitrary-module old
matrix inverses through the selected append and canonical parity charts.
The conjugate isomorphisms are constructed here; their forward identification
with the finite prescribed weighted matrices is a separate obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
section DotComponents
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)

private theorem endpointUnitDotLinear_refl (R : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    BalancedInduction.endpointUnitDotLinear J hα R n w (J.obj w) rfl =
      SVec.toLinearMap ((BalancedInduction.unitDotColumn J hα R n).total w) := by
  rw [← BalancedInduction.endpointUnitDotLinear_total J hα R n w (J.obj w) rfl,
    eqToHom_refl, BalancedInduction.postcompose_id, LinearMap.id_comp]

private theorem endpointUnitDot_apply (R : Superfunctor k C (SVec k)) (n : ℕ) (w : C) (b : R.obj w) :
    BalancedInduction.endpointUnitDotLinear J hα R n w (J.obj w) rfl b =
      (BalancedInduction.unitDotColumn J hα R n).total w b :=
  LinearMap.congr_fun (endpointUnitDotLinear_refl J hα R n w) b

private theorem mapComponent_identity (R : Superfunctor k C (SVec k)) (w : A) :
    BalancedInduction.mapComponent J (𝟙 R) 0 w = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s a b
  rw [BalancedInduction.mapComponent_tensor, twist_zero]
  rfl
end DotComponents

private theorem equiv_hom_apply {k V W : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (e : V ≃ₗ[k] W) (f : V →ₗ[k] W) (h : e.toLinearMap = f) (x : V) :
    e x = f x := LinearMap.congr_fun h x

private def superspaceIsoLinearEquiv {k : Type u} [CommRing k] {V W : SVec k}
    (e : V ≅ W) : V ≃ₗ[k] W where
  toLinearMap := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : W ⟶ W => f x) e.inv_hom_id

section FiniteCharts
variable {k : Type u} [CommRing k] {ι : Type} [Fintype ι]
  (V V' : ι → SVec k) (W W' : SVec k)
  (eV : ∀ a, V a ≃ₗ[k] V' a) (eW : W ≃ₗ[k] W')

end FiniteCharts

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "Q" => oldTruncateFunctor D Sc cutoff N
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

private theorem oldUnitColumn_linear
    (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((CyclotomicCrossingTensor.moduleUnitColumn D Sc cutoff i P n).total w) =
      BalancedInduction.unitDotLinear J
        (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) P n w := by
  rw [oldUnitColumn_eq, BalancedInduction.unitDotColumn_total]

private theorem oldUnitColumn_apply
    (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) (w : OldCategory D Sc cutoff) (b : P.obj w) :
    (moduleUnitColumn D Sc cutoff i P n).total w b =
      BalancedInduction.unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) P n w b :=
  LinearMap.congr_fun (oldUnitColumn_linear D Sc cutoff i P n w) b

private theorem oldCapRow_linear
    (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((CyclotomicCrossingTensor.moduleCapRow D Sc cutoff i P n).total w) =
      BalancedInduction.capDotLinear J
        (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) P n w := by
  rw [oldCapRow_eq, BalancedInduction.capDotRow_total]

private theorem parity_square_2 (p : ZMod 2) : p * p = p := by
  rcases parity_eq_zero_or_one p with h | h <;> simp only [h, mul_zero, one_mul]

private def oldMateRaw (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J ((BalancedInduction.restriction J).obj P).toFunctor w →ₗ[k]
      BalancedInduction.Obj J P.toFunctor ((J).obj w) :=
  ((oldModuleMate D Sc cutoff i).app (D.parity i * D.parity i) P).total w

private theorem oldMatePrecompose_identity (w : OldCategory D Sc cutoff) :
    weightedOldMatePrecomposeLinear D Sc cutoff N i M ((BalancedInduction.restriction J).obj RM) (𝟙 _) w =
      weightedOldMateLinear D Sc cutoff N i M w := by
  unfold weightedOldMatePrecomposeLinear
  rw [mapComponent_identity, LinearMap.comp_id]

/-- Every prescribed ordinary unit/dot column commutes with the selected value chart. -/
theorem weightedUnitColumnValue_compare (w : OldCategory D Sc cutoff) (n : ℕ) (b : (RM).obj w) :
    weightedMateTargetLinearEquiv D Sc cutoff N i M w
        ((moduleUnitColumn D Sc cutoff i RM n).total w b) =
      (BalancedInduction.unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) M n).total ((Q).obj w) b := by
  have h1 := congrArg (weightedMateTargetLinearEquiv D Sc cutoff N i M w)
    (oldUnitColumn_apply D Sc cutoff i RM n w b)
  have hc := equiv_hom_apply (weightedMateTargetLinearEquiv D Sc cutoff N i M w)
    (weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w))
    (weightedMateTargetLinearEquiv_hom D Sc cutoff N i M w)
    (BalancedInduction.unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) RM n w b)
  have h2 := LinearMap.congr_fun (weightedMateTargetLinear_unitDot D Sc cutoff N i M w n) b
  have h3 := endpointUnitDot_apply T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w) b
  have h12 := h1.trans hc
  have h23 := h2.trans h3
  have hresult := h12.trans h23
  exact hresult

/-- Every prescribed ordinary dot/counit row commutes with the selected value chart. -/
theorem weightedCapRowValue_compare (w : OldCategory D Sc cutoff) (n : ℕ)
    (x : ((BalancedInduction.induction J).obj ((BalancedInduction.restriction J).obj RM)).obj w) :
    (moduleCapRow D Sc cutoff i RM n).total w x =
      (BalancedInduction.capDotRow T (truncatedDot_supernatural D Sc cutoff N i) M n).total ((Q).obj w)
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w x) := by
  have h1 := LinearMap.congr_fun (oldCapRow_linear D Sc cutoff i RM n w) x
  have h2 := LinearMap.congr_fun (weightedMateSourceLinear_capDot D Sc cutoff N i M w n) x
  have hc := LinearMap.congr_fun (weightedMateSourceLinearEquiv_hom D Sc cutoff N i M w) x
  have h3 := congrArg
    (BalancedInduction.capDotLinear T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w)) hc.symm
  have h4 := LinearMap.congr_fun
    (BalancedInduction.capDotRow_total T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w))
    (weightedMateSourceLinearEquiv D Sc cutoff N i M w x)
  have h23 := h2.symm.trans h3
  have h123 := h1.trans h23
  have hresult := h123.trans h4.symm
  exact hresult

local instance weightedMatrixOldPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory
local instance weightedMatrixQuotientPi : PiSupercategory k (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :=
  supermodulePiSupercategory

/-- Coordinatewise selected source charts with the prescribed module parity actions. -/
def weightedUnitFamilyValueEquiv (m : ℕ) (w : OldCategory D Sc cutoff)
    (a : Option (Fin m)) :
    (CyclotomicCrossingTensor.unitMatrixFamily D Sc cutoff i RM m a).obj w ≃ₗ[k]
      (weightedUnitMatrixFamily D Sc cutoff N i M m a).obj ((Q).obj w) :=
  match a with
  | none => BalancedInduction.shiftedModuleValueLinearEquiv
      ((BalancedInduction.induction J).obj ((BalancedInduction.restriction J).obj RM))
      ((BalancedInduction.induction T).obj ((BalancedInduction.restriction T).obj M))
      w ((Q).obj w) (weightedMateSourceLinearEquiv D Sc cutoff N i M w) (D.parity i)
  | some r => BalancedInduction.shiftedModuleValueLinearEquiv RM M w ((Q).obj w)
      (LinearEquiv.refl k _) (r.val • D.parity i)

/-- Coordinatewise selected target charts with the prescribed module parity actions. -/
def weightedCapFamilyValueEquiv (m : ℕ) (w : OldCategory D Sc cutoff)
    (a : Option (Fin m)) :
    (CyclotomicCrossingTensor.capMatrixFamily D Sc cutoff i RM m a).obj w ≃ₗ[k]
      (weightedCapMatrixFamily D Sc cutoff N i M m a).obj ((Q).obj w) :=
  match a with
  | none => BalancedInduction.shiftedModuleValueLinearEquiv
      ((BalancedInduction.restriction J).obj ((BalancedInduction.induction J).obj RM))
      ((BalancedInduction.restriction T).obj ((BalancedInduction.induction T).obj M))
      w ((Q).obj w) (weightedMateTargetLinearEquiv D Sc cutoff N i M w) (D.parity i)
  | some r => BalancedInduction.shiftedModuleValueLinearEquiv RM M w ((Q).obj w)
      (LinearEquiv.refl k _) (r.val • D.parity i)

/-- The finite source chart is the product of those exact canonical coordinates. -/
def weightedUnitMatrixValueEquiv (m : ℕ) (w : OldCategory D Sc cutoff) :
    CyclotomicCrossingTensor.unitMatrixSourceSpace D Sc cutoff i RM m w ≃ₗ[k]
      weightedUnitMatrixSourceSpace D Sc cutoff N i M m ((Q).obj w) :=
  LinearEquiv.piCongrRight (weightedUnitFamilyValueEquiv D Sc cutoff N i M m w)

/-- The finite target chart is the product of those exact canonical coordinates. -/
def weightedCapMatrixValueEquiv (m : ℕ) (w : OldCategory D Sc cutoff) :
    CyclotomicCrossingTensor.capMatrixTargetSpace D Sc cutoff i RM m w ≃ₗ[k]
      weightedCapMatrixTargetSpace D Sc cutoff N i M m ((Q).obj w) :=
  LinearEquiv.piCongrRight (weightedCapFamilyValueEquiv D Sc cutoff N i M m w)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Prescribed weighted matrix fields in canonical coordinates

DeformedMatrixComparison (2), (4): each prescribed shifted field commutes
with the selected append chart. Raw field formulas are established before
specializing the input module to the weighted restriction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor BalancedInduction
universe u

section LinearKernels
variable {k V W X Y : Type u} [CommRing k]
  [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
private theorem unitPlain_reencode (c c₀ : W →ₗ[k] Y) (f : V →ₗ[k] W)
    (g g₀ : V →ₗ[k] Y) (hc : c = c₀) (hg : g₀ = g) (h : c₀ ∘ₗ f = g₀) :
    c ∘ₗ f = g ∘ₗ LinearMap.id := by
  rw [hc, LinearMap.comp_id]
  exact h.trans hg
private theorem capPlain_reencode (d d₀ : V →ₗ[k] X) (f : V →ₗ[k] W) (g : X →ₗ[k] W)
    (hd : d = d₀) (h : g ∘ₗ d₀ = f) : LinearMap.id ∘ₗ f = g ∘ₗ d := by
  rw [hd, LinearMap.id_comp]
  exact h.symm
end LinearKernels

section Endpoints
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  {p : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s} (hδ : IsSupernatural k p δ)
private theorem unitEndpoint_refl (P : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    endpointUnitDotLinear A hδ P n w (A.obj w) rfl = unitDotLinear A hδ P n w := by
  unfold endpointUnitDotLinear unitDotLinear
  rw [eqToHom_refl, postcompose_id, LinearMap.id_comp]
private theorem mapComponent_identity_2 (P : Superfunctor k C (SVec k)) (w : C) :
    mapComponent A (𝟙 P) 0 w = LinearMap.id := by
  apply hom_ext
  intro s a b
  rw [mapComponent_tensor, twist_zero]
  rfl
end Endpoints

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "J" => append D Sc cutoff i
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local instance weightedEntryOldPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory
local instance weightedEntryNewPi : PiSupercategory k (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :=
  supermodulePiSupercategory

private theorem parity_square_3 (p : ZMod 2) : p * p = p := by
  rcases parity_eq_zero_or_one p with h | h <;> simp only [h, mul_zero, one_mul]

private def oldMateRaw_2 (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (w : OldCategory D Sc cutoff) :
    Obj J ((restriction J).obj P).toFunctor w →ₗ[k] Obj J P.toFunctor ((J).obj w) :=
  ((oldModuleMate D Sc cutoff i).app (D.parity i * D.parity i) P).total w

private theorem oldMate_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((matrixMateComponent D Sc cutoff i P).total w) = oldMateRaw_2 D Sc cutoff i P w := by
  exact congrArg (fun q => ((oldModuleMate D Sc cutoff i).app q P).total w)
    (parity_square_3 (D.parity i)).symm
private theorem oldUnit_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((moduleUnitColumn D Sc cutoff i P n).total w) =
      unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) P n w := by
  rw [oldUnitColumn_eq, unitDotColumn_total]
private theorem oldCap_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((moduleCapRow D Sc cutoff i P n).total w) =
      capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) P n w := by
  rw [oldCapRow_eq, capDotRow_total]

private theorem oldUnitEntry_none_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i P m none).total w) =
      oldMateRaw_2 D Sc cutoff i P w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
          ((induction J).obj ((restriction J).obj P))).hom.total w) := by
  rw [unitMatrixEntry_none, Superfunctor.comp_total, SVec.toLinearMap_comp, oldMate_total]
private theorem oldUnitEntry_some_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i P m (some r)).total w) =
      unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) P r.val w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso P).hom.total w) := by
  change SVec.toLinearMap ((((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso P).hom ≫
    moduleUnitColumn D Sc cutoff i P r.val).total w) = _
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp, oldUnit_total]
private theorem oldCapEntry_none_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i P m none).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
        ((restriction J).obj ((induction J).obj P))).inv.total w) ∘ₗ oldMateRaw_2 D Sc cutoff i P w := by
  change SVec.toLinearMap ((matrixMateComponent D Sc cutoff i P ≫
    ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso ((restriction J).obj ((induction J).obj P))).inv).total w) = _
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp, oldMate_total]
private theorem oldCapEntry_some_total (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i P m (some r)).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso P).inv.total w) ∘ₗ
        capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) P r.val w := by
  change SVec.toLinearMap ((moduleCapRow D Sc cutoff i P r.val ≫
    ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso P).inv).total w) = _
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp, oldCap_total]

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

private theorem selectedOldMate_eq (w : OldCategory D Sc cutoff) :
    weightedOldMateLinear D Sc cutoff N i M w = oldMateRaw_2 D Sc cutoff i RM w := rfl
private theorem oldMatePrecompose_identity_2 (w : OldCategory D Sc cutoff) :
    weightedOldMatePrecomposeLinear D Sc cutoff N i M ((restriction J).obj RM) (𝟙 _) w =
      weightedOldMateLinear D Sc cutoff N i M w := by
  unfold weightedOldMatePrecomposeLinear
  rw [mapComponent_identity_2, LinearMap.comp_id]

/-- The selected genuine charts intertwine the prescribed raw mate, without an entry compatibility hypothesis. -/
theorem weightedMatrixCharts_mate (w : OldCategory D Sc cutoff) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap ∘ₗ oldMateRaw_2 D Sc cutoff i RM w =
      orderedMateLinear T (truncatedEqualCross_supernatural D Sc cutoff N i) M ((Q).obj w) ∘ₗ
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  have h := appendWeightedModuleIso_hom_mate D Sc cutoff N i M w
  rw [oldMatePrecompose_identity_2, Category.id_comp] at h
  exact linearSquare_reencode _ _ _ _ _ _ _ _
    (weightedMateTargetLinearEquiv_hom D Sc cutoff N i M w)
    (selectedOldMate_eq D Sc cutoff N i M w).symm
    (endpointMateLinear_refl T (truncatedEqualCross_supernatural D Sc cutoff N i) M ((Q).obj w)).symm
    (weightedMateSourceLinearEquiv_hom D Sc cutoff N i M w) h

/-- Every given raw unit/dot column commutes with the same chosen chart. -/
theorem weightedMatrixCharts_unit (w : OldCategory D Sc cutoff) (n : ℕ) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap ∘ₗ
        unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) RM n w =
      unitDotLinear T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w) ∘ₗ LinearMap.id := by
  exact unitPlain_reencode _ _ _ _ _
    (weightedMateTargetLinearEquiv_hom D Sc cutoff N i M w)
    (unitEndpoint_refl T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w))
    (weightedMateTargetLinear_unitDot D Sc cutoff N i M w n)

/-- Every given raw dot/counit row commutes with the same chosen chart. -/
theorem weightedMatrixCharts_cap (w : OldCategory D Sc cutoff) (n : ℕ) :
    LinearMap.id ∘ₗ capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) RM n w =
      capDotLinear T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w) ∘ₗ
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  exact capPlain_reencode _ _ _ _ (weightedMateSourceLinearEquiv_hom D Sc cutoff N i M w)
    (weightedMateSourceLinear_capDot D Sc cutoff N i M w n)

/-- The given first source-shifted field commutes with the canonical EF chart. -/
theorem weightedMatrixCharts_unitEntry_none (m : ℕ) (w : OldCategory D Sc cutoff) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap ∘ₗ
        SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i RM m none).total w) =
      SVec.toLinearMap ((weightedUnitMatrixEntry D Sc cutoff N i M m none).total ((Q).obj w)) ∘ₗ
        (weightedUnitFamilyValueEquiv D Sc cutoff N i M m w none).toLinearMap := by
  have h := weightedMatrixCharts_mate D Sc cutoff N i M w
  have hz := shiftedModuleValueLinearEquiv_source_square
    ((induction J).obj ((restriction J).obj RM)) (induced T ((restriction T).obj M))
    w ((Q).obj w) (weightedMateSourceLinearEquiv D Sc cutoff N i M w) (D.parity i)
  have ho := oldUnitEntry_none_total D Sc cutoff i RM m w
  have hn := inductionUnitMatrixEntry_none_total T
    (truncatedEqualCross_supernatural D Sc cutoff N i) (truncatedDot_supernatural D Sc cutoff N i)
    (parity_square_3 (D.parity i)) M m ((Q).obj w)
  exact linearColumn_parity_square _ _ _ _ _ _ _ _ _ h hz ho hn

/-- The given first target-shifted field commutes with the canonical FE chart. -/
theorem weightedMatrixCharts_capEntry_none (m : ℕ) (w : OldCategory D Sc cutoff) :
    (weightedCapFamilyValueEquiv D Sc cutoff N i M m w none).toLinearMap ∘ₗ
        SVec.toLinearMap ((capMatrixEntry D Sc cutoff i RM m none).total w) =
      SVec.toLinearMap ((weightedCapMatrixEntry D Sc cutoff N i M m none).total ((Q).obj w)) ∘ₗ
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  have h := weightedMatrixCharts_mate D Sc cutoff N i M w
  have hz := shiftedModuleValueLinearEquiv_target_square
    ((restriction J).obj ((induction J).obj RM)) ((restriction T).obj (induced T M))
    w ((Q).obj w) (weightedMateTargetLinearEquiv D Sc cutoff N i M w) (D.parity i)
  have ho := oldCapEntry_none_total D Sc cutoff i RM m w
  have hn := inductionCapMatrixEntry_none_total T
    (truncatedEqualCross_supernatural D Sc cutoff N i) (truncatedDot_supernatural D Sc cutoff N i)
    (parity_square_3 (D.parity i)) M m ((Q).obj w)
  exact linearRow_parity_square _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every given unit/dot field commutes with the canonical value-coordinate chart. -/
theorem weightedMatrixCharts_unitEntry_some (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap ∘ₗ
        SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i RM m (some r)).total w) =
      SVec.toLinearMap ((weightedUnitMatrixEntry D Sc cutoff N i M m (some r)).total ((Q).obj w)) ∘ₗ
        (weightedUnitFamilyValueEquiv D Sc cutoff N i M m w (some r)).toLinearMap := by
  have h := weightedMatrixCharts_unit D Sc cutoff N i M w r.val
  have hz := shiftedModuleValueLinearEquiv_source_square RM M w ((Q).obj w)
    (LinearEquiv.refl k _) (r.val • D.parity i)
  have ho := oldUnitEntry_some_total D Sc cutoff i RM m r w
  have hn := inductionUnitMatrixEntry_some_total T
    (truncatedEqualCross_supernatural D Sc cutoff N i) (truncatedDot_supernatural D Sc cutoff N i)
    (parity_square_3 (D.parity i)) M m r ((Q).obj w)
  exact linearColumn_parity_square _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every given dot/counit field commutes with the canonical value-coordinate chart. -/
theorem weightedMatrixCharts_capEntry_some (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    (weightedCapFamilyValueEquiv D Sc cutoff N i M m w (some r)).toLinearMap ∘ₗ
        SVec.toLinearMap ((capMatrixEntry D Sc cutoff i RM m (some r)).total w) =
      SVec.toLinearMap ((weightedCapMatrixEntry D Sc cutoff N i M m (some r)).total ((Q).obj w)) ∘ₗ
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  have h := weightedMatrixCharts_cap D Sc cutoff N i M w r.val
  have hz := shiftedModuleValueLinearEquiv_target_square RM M w ((Q).obj w)
    (LinearEquiv.refl k _) (r.val • D.parity i)
  have ho := oldCapEntry_some_total D Sc cutoff i RM m r w
  have hn := inductionCapMatrixEntry_some_total T
    (truncatedEqualCross_supernatural D Sc cutoff N i) (truncatedDot_supernatural D Sc cutoff N i)
    (parity_square_3 (D.parity i)) M m r ((Q).obj w)
  exact linearRow_parity_square _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every prescribed unit field, including the crossing-derived slot, commutes with its given chart. -/
theorem weightedMatrixCharts_unitEntry (m : ℕ) (a : Option (Fin m)) (w : OldCategory D Sc cutoff) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap ∘ₗ
        SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i RM m a).total w) =
      SVec.toLinearMap ((weightedUnitMatrixEntry D Sc cutoff N i M m a).total ((Q).obj w)) ∘ₗ
        (weightedUnitFamilyValueEquiv D Sc cutoff N i M m w a).toLinearMap := by
  cases a with
  | none => exact weightedMatrixCharts_unitEntry_none D Sc cutoff N i M m w
  | some r => exact weightedMatrixCharts_unitEntry_some D Sc cutoff N i M m r w

/-- Every prescribed cap field, including the crossing-derived slot, commutes with its given chart. -/
theorem weightedMatrixCharts_capEntry (m : ℕ) (a : Option (Fin m)) (w : OldCategory D Sc cutoff) :
    (weightedCapFamilyValueEquiv D Sc cutoff N i M m w a).toLinearMap ∘ₗ
        SVec.toLinearMap ((capMatrixEntry D Sc cutoff i RM m a).total w) =
      SVec.toLinearMap ((weightedCapMatrixEntry D Sc cutoff N i M m a).total ((Q).obj w)) ∘ₗ
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  cases a with
  | none => exact weightedMatrixCharts_capEntry_none D Sc cutoff N i M m w
  | some r => exact weightedMatrixCharts_capEntry_some D Sc cutoff N i M m r w

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Finite assembly of the prescribed weighted matrix comparisons

The finite sums and products in DeformedMatrixComparison (2), (4) retain
all given first/dotted entries. The selected coordinate products intertwine
the whole prescribed matrices before any inverse is attached.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor BalancedInduction
universe u
section FiniteKernels
variable {k : Type u} [CommRing k] {ι : Type} [Fintype ι]
  {V W : ι → Type u} {U Z : Type u}
  [∀ a, AddCommMonoid (V a)] [∀ a, Module k (V a)]
  [∀ a, AddCommMonoid (W a)] [∀ a, Module k (W a)]
  [AddCommMonoid U] [Module k U] [AddCommMonoid Z] [Module k Z]

private theorem columns_square
    (c : U →ₗ[k] Z) (f : ∀ a, V a →ₗ[k] U) (g : ∀ a, W a →ₗ[k] Z)
    (d : ∀ a, V a →ₗ[k] W a)
    (o : ((a : ι) → V a) →ₗ[k] U) (n : ((a : ι) → W a) →ₗ[k] Z)
    (s : ((a : ι) → V a) →ₗ[k] ((a : ι) → W a))
    (h : ∀ a, c ∘ₗ f a = g a ∘ₗ d a)
    (ho : o = ∑ a, f a ∘ₗ LinearMap.proj a)
    (hn : n = ∑ a, g a ∘ₗ LinearMap.proj a)
    (hs : ∀ a, LinearMap.proj a ∘ₗ s = d a ∘ₗ LinearMap.proj a) :
    c ∘ₗ o = n ∘ₗ s := by
  classical
  rw [ho, hn]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  change c (∑ a, f a (x a)) = ∑ a, g a ((s x) a)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact (LinearMap.congr_fun (h a) (x a)).trans (congrArg (g a) (LinearMap.congr_fun (hs a) x).symm)

omit [Fintype ι] in
private theorem rows_square
    (c : U →ₗ[k] Z) (f : ∀ a, U →ₗ[k] V a) (g : ∀ a, Z →ₗ[k] W a)
    (d : ∀ a, V a →ₗ[k] W a)
    (o : U →ₗ[k] ((a : ι) → V a)) (n : Z →ₗ[k] ((a : ι) → W a))
    (s : ((a : ι) → V a) →ₗ[k] ((a : ι) → W a))
    (h : ∀ a, d a ∘ₗ f a = g a ∘ₗ c)
    (ho : ∀ a, LinearMap.proj a ∘ₗ o = f a)
    (hn : ∀ a, LinearMap.proj a ∘ₗ n = g a)
    (hs : ∀ a, LinearMap.proj a ∘ₗ s = d a ∘ₗ LinearMap.proj a) :
    s ∘ₗ o = n ∘ₗ c := by
  apply LinearMap.ext
  intro x
  funext a
  have h1 := LinearMap.congr_fun (hs a) (o x)
  have h2 := congrArg (d a) (LinearMap.congr_fun (ho a) x)
  have h3 := LinearMap.congr_fun (h a) x
  have h4 := LinearMap.congr_fun (hn a) (c x)
  exact h1.trans (h2.trans (h3.trans h4.symm))

omit [Fintype ι] in
private theorem piChart_proj (e : ∀ a, V a ≃ₗ[k] W a) (a : ι) :
    LinearMap.proj a ∘ₗ (LinearEquiv.piCongrRight e).toLinearMap =
      (e a).toLinearMap ∘ₗ LinearMap.proj a := by
  apply LinearMap.ext
  intro x
  rfl
end FiniteKernels

section SuperspaceColumns
variable {k : Type u} [CommRing k] {ι : Type} [Fintype ι]
private theorem columns_sum (V : ι → SVec k) (W : SVec k) (f : ∀ a, V a ⟶ W) :
    SVec.toLinearMap (OddMath.FiniteSuperspace.assembleColumns V W f) =
      ∑ a, SVec.toLinearMap (f a) ∘ₗ LinearMap.proj (R := k) (φ := fun a => V a) a := by
  classical
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rfl
end SuperspaceColumns

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "J" => append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N

private theorem oldCapMatrix_proj (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (m : ℕ) (w : OldCategory D Sc cutoff) (a : Option (Fin m)) :
    LinearMap.proj a ∘ₗ SVec.toLinearMap (capMatrixComponent D Sc cutoff i P m w) =
      SVec.toLinearMap ((capMatrixEntry D Sc cutoff i P m a).total w) := rfl

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

private theorem newCapMatrix_proj (m : ℕ) (w : TruncatedCategory D Sc cutoff N) (a : Option (Fin m)) :
    LinearMap.proj a ∘ₗ SVec.toLinearMap (weightedCapMatrixComponent D Sc cutoff N i M m w) =
      SVec.toLinearMap ((weightedCapMatrixEntry D Sc cutoff N i M m a).total w) := rfl

/-- Every prescribed column, including the original mate slot, forms the whole finite unit square. -/
theorem weightedMatrixCharts_unitMatrix (m : ℕ) (w : OldCategory D Sc cutoff) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap ∘ₗ
        SVec.toLinearMap (unitMatrixComponent D Sc cutoff i RM m w) =
      SVec.toLinearMap (weightedUnitMatrixComponent D Sc cutoff N i M m ((Q).obj w)) ∘ₗ
        (weightedUnitMatrixValueEquiv D Sc cutoff N i M m w).toLinearMap := by
  exact columns_square _ _ _ _ _ _ _
    (fun a => weightedMatrixCharts_unitEntry D Sc cutoff N i M m a w)
    (columns_sum (fun a : Option (Fin m) => (unitMatrixFamily D Sc cutoff i RM m a).obj w) _
      (fun a => (unitMatrixEntry D Sc cutoff i RM m a).total w))
    (columns_sum (fun a : Option (Fin m) => (weightedUnitMatrixFamily D Sc cutoff N i M m a).obj ((Q).obj w)) _
      (fun a => (weightedUnitMatrixEntry D Sc cutoff N i M m a).total ((Q).obj w)))
    (fun a => piChart_proj (weightedUnitFamilyValueEquiv D Sc cutoff N i M m w) a)

/-- Every prescribed row, including the original mate slot, forms the whole finite cap square. -/
theorem weightedMatrixCharts_capMatrix (m : ℕ) (w : OldCategory D Sc cutoff) :
    (weightedCapMatrixValueEquiv D Sc cutoff N i M m w).toLinearMap ∘ₗ
        SVec.toLinearMap (capMatrixComponent D Sc cutoff i RM m w) =
      SVec.toLinearMap (weightedCapMatrixComponent D Sc cutoff N i M m ((Q).obj w)) ∘ₗ
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  exact rows_square _ _ _ _ _ _ _
    (fun a => weightedMatrixCharts_capEntry D Sc cutoff N i M m a w)
    (oldCapMatrix_proj D Sc cutoff i RM m w)
    (newCapMatrix_proj D Sc cutoff N i M m ((Q).obj w))
    (fun a => piChart_proj (weightedCapFamilyValueEquiv D Sc cutoff N i M m w) a)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Inverses of the prescribed weighted matrix components

DeformedMatrixComparison (2), (4): the given old matrix inverse and the
selected genuine chart squares make the prescribed weighted forward maps
bijective. The resulting isomorphisms use those exact forward maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor BalancedInduction
universe u

private def svecIsoEquiv {k : Type u} [CommRing k] {V W : SVec k} (e : V ≅ W) : V ≃ₗ[k] W where
  toLinearMap := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : W ⟶ W => f x) e.inv_hom_id
private theorem iso_hom_bijective {k : Type u} [CommRing k] {V W : SVec k} (e : V ≅ W) :
    Function.Bijective e.hom := (svecIsoEquiv e).bijective
private theorem equiv_hom_bijective {k V W : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W] (e : V ≃ₗ[k] W) :
    Function.Bijective e.toLinearMap := e.bijective

private theorem bijective_square {k V W X Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    (c : W →ₗ[k] Y) (f : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (hc : Function.Bijective c) (hf : Function.Bijective f) (hd : Function.Bijective d)
    (h : c ∘ₗ f = g ∘ₗ d) : Function.Bijective g := by
  constructor
  · intro x y hxy
    obtain ⟨v, hv⟩ := hd.surjective x
    obtain ⟨w, hw⟩ := hd.surjective y
    have hmid : g (d v) = g (d w) := by
      simpa only [hv, hw] using hxy
    have hh : c (f v) = c (f w) :=
      (LinearMap.congr_fun h v).trans (hmid.trans (LinearMap.congr_fun h w).symm)
    exact hv.symm.trans ((congrArg d (hf.injective (hc.injective hh))).trans hw)
  · intro y
    obtain ⟨w, hw⟩ := hc.surjective y
    obtain ⟨v, hv⟩ := hf.surjective w
    exact ⟨d v, (LinearMap.congr_fun h v).symm.trans ((congrArg c hv).trans hw)⟩

private def isoOfBijectiveMap {k : Type u} [CommRing k] {V W : SVec k} (f : V ⟶ W)
    (hf : Function.Bijective f) : V ≅ W := SVec.isoOfLinearEquiv (LinearEquiv.ofBijective f hf)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

private theorem oldUnit_bijective (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (w : OldCategory D Sc cutoff) (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I)) :
    Function.Bijective (unitMatrixComponent D Sc cutoff i P
      (contentUnitCount D cutoff i (w.word : Multiset I)) w) := by
  rw [← TensorMatrixCoordinates.moduleUnitMatrixIso_hom D Sc cutoff P i w hh]
  exact iso_hom_bijective (TensorMatrixCoordinates.moduleUnitMatrixIso D Sc cutoff P i w hh)
private theorem oldCap_bijective (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (w : OldCategory D Sc cutoff) (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0) :
    Function.Bijective (capMatrixComponent D Sc cutoff i P
      (contentCapCount D cutoff i (w.word : Multiset I)) w) := by
  rw [← TensorMatrixCoordinates.moduleCapMatrixIso_hom D Sc cutoff P i w hh]
  exact iso_hom_bijective (TensorMatrixCoordinates.moduleCapMatrixIso D Sc cutoff P i w hh)

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The actual weighted unit matrix is bijective at its prescribed nonnegative-height size. -/
theorem weightedUnitMatrixComponent_bijective (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I)) :
    Function.Bijective (weightedUnitMatrixComponent D Sc cutoff N i M
      (contentUnitCount D cutoff i (w.word : Multiset I)) ((Q).obj w)) := by
  exact bijective_square _ _ _ _
    (equiv_hom_bijective (weightedMateTargetLinearEquiv D Sc cutoff N i M w))
    (oldUnit_bijective D Sc cutoff i RM w hh)
    (equiv_hom_bijective (weightedUnitMatrixValueEquiv D Sc cutoff N i M _ w))
    (weightedMatrixCharts_unitMatrix D Sc cutoff N i M _ w)

/-- The actual weighted cap matrix is bijective at its prescribed nonpositive-height size. -/
theorem weightedCapMatrixComponent_bijective (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0) :
    Function.Bijective (weightedCapMatrixComponent D Sc cutoff N i M
      (contentCapCount D cutoff i (w.word : Multiset I)) ((Q).obj w)) := by
  exact bijective_square _ _ _ _
    (equiv_hom_bijective (weightedCapMatrixValueEquiv D Sc cutoff N i M _ w))
    (oldCap_bijective D Sc cutoff i RM w hh)
    (equiv_hom_bijective (weightedMateSourceLinearEquiv D Sc cutoff N i M w))
    (weightedMatrixCharts_capMatrix D Sc cutoff N i M _ w)

/-- The given unit forward map, with its actual domain and codomain retained. -/
def weightedUnitMatrixArrow (m : ℕ) (w : TruncatedCategory D Sc cutoff N) : Arrow (SVec k) :=
  Arrow.mk (weightedUnitMatrixComponent D Sc cutoff N i M m w)
/-- The given cap forward map, with its actual domain and codomain retained. -/
def weightedCapMatrixArrow (m : ℕ) (w : TruncatedCategory D Sc cutoff N) : Arrow (SVec k) :=
  Arrow.mk (weightedCapMatrixComponent D Sc cutoff N i M m w)

/-- An inverse for the exact prescribed weighted unit forward matrix. -/
def weightedUnitMatrixComponentIso (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I)) :
    (weightedUnitMatrixArrow D Sc cutoff N i M (contentUnitCount D cutoff i (w.word : Multiset I)) ((Q).obj w)).left ≅
      (weightedUnitMatrixArrow D Sc cutoff N i M (contentUnitCount D cutoff i (w.word : Multiset I)) ((Q).obj w)).right :=
  isoOfBijectiveMap (weightedUnitMatrixComponent D Sc cutoff N i M
    (contentUnitCount D cutoff i (w.word : Multiset I)) ((Q).obj w))
      (weightedUnitMatrixComponent_bijective D Sc cutoff N i M w hh)

/-- An inverse for the exact prescribed weighted cap forward matrix. -/
def weightedCapMatrixComponentIso (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0) :
    (weightedCapMatrixArrow D Sc cutoff N i M (contentCapCount D cutoff i (w.word : Multiset I)) ((Q).obj w)).left ≅
      (weightedCapMatrixArrow D Sc cutoff N i M (contentCapCount D cutoff i (w.word : Multiset I)) ((Q).obj w)).right :=
  isoOfBijectiveMap (weightedCapMatrixComponent D Sc cutoff N i M
    (contentCapCount D cutoff i (w.word : Multiset I)) ((Q).obj w))
      (weightedCapMatrixComponent_bijective D Sc cutoff N i M w hh)

theorem weightedUnitMatrixComponentIso_hom (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I)) :
    (weightedUnitMatrixComponentIso D Sc cutoff N i M w hh).hom =
      weightedUnitMatrixComponent D Sc cutoff N i M
        (contentUnitCount D cutoff i (w.word : Multiset I)) ((Q).obj w) := rfl

theorem weightedCapMatrixComponentIso_hom (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0) :
    (weightedCapMatrixComponentIso D Sc cutoff N i M w hh).hom =
      weightedCapMatrixComponent D Sc cutoff N i M
        (contentCapCount D cutoff i (w.word : Multiset I)) ((Q).obj w) := rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Weighted matrix isomorphisms on canonical content modules

Brundan–Ellis (1.13)–(1.14): the specified finite weighted module matrices
are invertible after restriction to their canonical output content block.
The proof uses the established inverses of those exact forward components.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor BalancedInduction
universe u

private theorem columnsHom_even {k : Type u} [CommRing k]
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} [Fintype ι] {V : ι → Superfunctor k C (SVec k)}
    {T : Superfunctor k C (SVec k)} (f : ∀ a, V a ⟶ T)
    (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) :
    OddMath.FiniteSupermodule.columnsHom f hf ∈ parity (R := k) _ _ 0 :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr (SuperNatTrans.ofNatTrans_isHomogeneous _ _)

private theorem rowsHom_even {k : Type u} [CommRing k]
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {ι : Type} {V : ι → Superfunctor k C (SVec k)}
    {T : Superfunctor k C (SVec k)} (f : ∀ a, T ⟶ V a)
    (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) :
    OddMath.FiniteSupermodule.rowsHom f hf ∈ parity (R := k) _ _ 0 :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr (SuperNatTrans.ofNatTrans_isHomogeneous _ _)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))

/-- The prescribed finite unit columns, as one module morphism. -/
def weightedUnitMatrixModuleMap (m : ℕ) :=
  OddMath.FiniteSupermodule.columnsHom (weightedUnitMatrixEntry D Sc cutoff N i M m)
    (weightedUnitMatrixEntry_mem D Sc cutoff N i M m)
/-- The prescribed finite cap rows, as one module morphism. -/
def weightedCapMatrixModuleMap (m : ℕ) :=
  OddMath.FiniteSupermodule.rowsHom (weightedCapMatrixEntry D Sc cutoff N i M m)
    (weightedCapMatrixEntry_mem D Sc cutoff N i M m)

theorem weightedUnitMatrixModuleMap_mem (m : ℕ) :
    weightedUnitMatrixModuleMap D Sc cutoff N i M m ∈ parity (R := k) _ _ 0 :=
  columnsHom_even _ _
theorem weightedCapMatrixModuleMap_mem (m : ℕ) :
    weightedCapMatrixModuleMap D Sc cutoff N i M m ∈ parity (R := k) _ _ 0 :=
  rowsHom_even _ _

/-- Evaluation is exactly the specified unit forward matrix. -/
theorem weightedUnitMatrixModuleMap_total (m : ℕ) (w : TruncatedCategory D Sc cutoff N) :
    (weightedUnitMatrixModuleMap D Sc cutoff N i M m).total w =
      weightedUnitMatrixComponent D Sc cutoff N i M m w := by
  ext x
  exact OddMath.FiniteSupermodule.columnsHom_total_apply _ _ w x

/-- Evaluation is exactly the specified cap forward matrix. -/
theorem weightedCapMatrixModuleMap_total (m : ℕ) (w : TruncatedCategory D Sc cutoff N) :
    (weightedCapMatrixModuleMap D Sc cutoff N i M m).total w =
      weightedCapMatrixComponent D Sc cutoff N i M m w := by
  apply LinearMap.ext
  intro x
  funext a
  exact OddMath.FiniteSupermodule.rowsHom_total_apply _ _ w x a

private theorem weightedUnitMatrix_bijectiveAtCount (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (m : ℕ) (hm : contentUnitCount D cutoff i (w.word : Multiset I) = m) :
    Function.Bijective ((weightedUnitMatrixModuleMap D Sc cutoff N i M m).total
      ((oldTruncateFunctor D Sc cutoff N).obj w)) := by
  subst m
  rw [weightedUnitMatrixModuleMap_total]
  exact weightedUnitMatrixComponent_bijective D Sc cutoff N i M w hh

private theorem weightedCapMatrix_bijectiveAtCount (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0)
    (m : ℕ) (hm : contentCapCount D cutoff i (w.word : Multiset I) = m) :
    Function.Bijective ((weightedCapMatrixModuleMap D Sc cutoff N i M m).total
      ((oldTruncateFunctor D Sc cutoff N).obj w)) := by
  subst m
  rw [weightedCapMatrixModuleMap_total]
  exact weightedCapMatrixComponent_bijective D Sc cutoff N i M w hh

/-- Restrict the specified unit map to its canonical output content. -/
def weightedContentUnitMatrixMap (β : Multiset I) :=
  (restriction (contentInclusion D Sc cutoff N β)).map
    (weightedUnitMatrixModuleMap D Sc cutoff N i M (contentUnitCount D cutoff i β))
/-- Restrict the specified cap map to its canonical output content. -/
def weightedContentCapMatrixMap (β : Multiset I) :=
  (restriction (contentInclusion D Sc cutoff N β)).map
    (weightedCapMatrixModuleMap D Sc cutoff N i M (contentCapCount D cutoff i β))

theorem weightedContentUnitMatrixMap_mem (β : Multiset I) :
    weightedContentUnitMatrixMap D Sc cutoff N i M β ∈ parity (R := k) _ _ 0 :=
  map_mem (restriction (contentInclusion D Sc cutoff N β))
    (weightedUnitMatrixModuleMap_mem D Sc cutoff N i M _)
theorem weightedContentCapMatrixMap_mem (β : Multiset I) :
    weightedContentCapMatrixMap D Sc cutoff N i M β ∈ parity (R := k) _ _ 0 :=
  map_mem (restriction (contentInclusion D Sc cutoff N β))
    (weightedCapMatrixModuleMap_mem D Sc cutoff N i M _)

theorem weightedContentUnitMatrixMap_bijective (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β) :
    Function.Bijective ((weightedContentUnitMatrixMap D Sc cutoff N i M β).total w) := by
  exact weightedUnitMatrix_bijectiveAtCount D Sc cutoff N i M ⟨w.obj.word⟩
    (by simpa only [w.content] using hh) _
    (congrArg (contentUnitCount D cutoff i) w.content)

theorem weightedContentCapMatrixMap_bijective (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β) :
    Function.Bijective ((weightedContentCapMatrixMap D Sc cutoff N i M β).total w) := by
  exact weightedCapMatrix_bijectiveAtCount D Sc cutoff N i M ⟨w.obj.word⟩
    (by simpa only [w.content] using hh) _
    (congrArg (contentCapCount D cutoff i) w.content)

/-- The prescribed unit matrix is an isomorphism on its canonical content block. -/
def weightedContentUnitMatrixIso (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals
    (weightedContentUnitMatrixMap D Sc cutoff N i M β)
    (weightedContentUnitMatrixMap_mem D Sc cutoff N i M β)
    (weightedContentUnitMatrixMap_bijective D Sc cutoff N i M β hh)

/-- The prescribed cap matrix is an isomorphism on its canonical content block. -/
def weightedContentCapMatrixIso (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals
    (weightedContentCapMatrixMap D Sc cutoff N i M β)
    (weightedContentCapMatrixMap_mem D Sc cutoff N i M β)
    (weightedContentCapMatrixMap_bijective D Sc cutoff N i M β hh)

theorem weightedContentUnitMatrixIso_hom (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) :
    (weightedContentUnitMatrixIso D Sc cutoff N i M β hh).hom =
      weightedContentUnitMatrixMap D Sc cutoff N i M β :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals_hom _ _ _
theorem weightedContentCapMatrixIso_hom (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) :
    (weightedContentCapMatrixIso D Sc cutoff N i M β hh).hom =
      weightedContentCapMatrixMap D Sc cutoff N i M β :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals_hom _ _ _

theorem weightedContentUnitMatrixIso_hom_total (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β) :
    (weightedContentUnitMatrixIso D Sc cutoff N i M β hh).hom.total w =
      weightedUnitMatrixComponent D Sc cutoff N i M (contentUnitCount D cutoff i β) w.obj := by
  rw [weightedContentUnitMatrixIso_hom]
  exact weightedUnitMatrixModuleMap_total D Sc cutoff N i M _ w.obj

theorem weightedContentCapMatrixIso_hom_total (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β) :
    (weightedContentCapMatrixIso D Sc cutoff N i M β hh).hom.total w =
      weightedCapMatrixComponent D Sc cutoff N i M (contentCapCount D cutoff i β) w.obj := by
  rw [weightedContentCapMatrixIso_hom]
  exact weightedCapMatrixModuleMap_total D Sc cutoff N i M _ w.obj

end OddMath.QuiverHecke.ELV
end

end
