import StringDiagrams.Super.SVec
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Module.LinearMap.End
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.QuiverHecke.CyclotomicAction.BoundaryNumerator.BoundaryPolynomial
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier.GlobalWeightCross
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate.ShiftedCoefficientModule
import OddMath.SKM.RouquierHomPostNaturalInverse

/-!
# Cap input matrices

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
namespace OddMath.QuiverHecke.ELV.MatrixParity
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

end Shift
end OddMath.QuiverHecke.ELV.MatrixParity

namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Input contraction pivots on the actual boundary lifts

The input shift has zero constant coefficient. Hence the actual contraction
of a decoded lift is the constant coefficient of the next boundary value.
This gives anti-diagonal vanishing and the prescribed leading equivalence.
These statements concern the concrete input operators; categorical cap
comparison and the full factor action remain separate.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem appendInputShift_zero (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) : appendInputShift D Sc cutoff i v t f 0 = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, add_zero]
  | single m b => simp [appendInputShift, appendOutputShift]

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Parity and dot transport for the actual shifted source

The source comparison is the induced map of the actual restriction parity
isomorphism followed by the prescribed even coefficient comparison.
Its odd parity and the odd shifted counit are established on these fixed
module maps. The actual induction dot anticommutes with this canonical
source comparison; no chosen-J or matrix premise is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

abbrev unshiftedSourceModule (i : I) (v : List I) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  (BalancedInduction.induction (append D Sc cutoff i)).obj
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))

theorem coefficientModuleBackward_mem (i : I) (v : List I) :
    coefficientModuleBackward D Sc cutoff i v ∈ parity (R := k) _ _ 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext s
  rw [coefficientModuleBackward_app, ite_eq_right hq]
  rfl

def parityCoefficientMap (i : I) (v : List I) :
    (BalancedInduction.restriction (append D Sc cutoff i)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) ⟶
      coefficientOneModule D Sc cutoff i v :=
  (BalancedInduction.restriction (append D Sc cutoff i)).map
      (supermoduleParityIso
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).inv ≫
    coefficientModuleBackward D Sc cutoff i v

theorem parityCoefficientMap_mem (i : I) (v : List I) :
    parityCoefficientMap D Sc cutoff i v ∈ parity (R := k) _ _ 1 := by
  have h := map_mem (BalancedInduction.restriction (append D Sc cutoff i))
    (inv_mem _
      (supermoduleParityIso_hom_mem
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))))
  simpa only [parityCoefficientMap, add_zero] using
    comp_mem h (coefficientModuleBackward_mem D Sc cutoff i v)

theorem shiftedSourceParityIso_hom_eq_induction_map (i : I) (v : List I) :
    (shiftedSourceParityIso D Sc cutoff i v).hom =
      (BalancedInduction.induction (append D Sc cutoff i)).map
        (parityCoefficientMap D Sc cutoff i v) := by
  change (BalancedInduction.induction (append D Sc cutoff i)).map
      ((BalancedInduction.restriction (append D Sc cutoff i)).map
        (supermoduleParityIso
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).inv) ≫
    (BalancedInduction.induction (append D Sc cutoff i)).map
      (coefficientModuleBackward D Sc cutoff i v) = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

theorem shiftedSourceParityIso_hom_mem (i : I) (v : List I) :
    (shiftedSourceParityIso D Sc cutoff i v).hom ∈ parity (R := k) _ _ 1 := by
  rw [shiftedSourceParityIso_hom_eq_induction_map]
  exact map_mem (BalancedInduction.induction (append D Sc cutoff i))
    (parityCoefficientMap_mem D Sc cutoff i v)

theorem odd_total_eq_app_one
    {M N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)} {f : M ⟶ N}
    (hf : f ∈ parity (R := k) M N 1) (t : OldCategory D Sc cutoff) :
    f.total t = f.app 1 t := by
  change f.app 0 t + f.app 1 t = f.app 1 t
  rw [Superfunctor.app_eq_zero_of_mem hf (by decide) t, zero_add]

theorem odd_total_mem
    {M N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)} {f : M ⟶ N}
    (hf : f ∈ parity (R := k) M N 1) (t : OldCategory D Sc cutoff) :
    f.total t ∈ parity (R := k) (M.obj t) (N.obj t) 1 := by
  rw [odd_total_eq_app_one D Sc cutoff hf t]
  exact f.app_mem 1 t

theorem inductionDot_mem (j : {j : I // D.parity j = 1})
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    inductionDot D Sc cutoff j.1 M t ∈ parity (R := k)
      (((BalancedInduction.induction (append D Sc cutoff j.1)).obj M).obj t)
      (((BalancedInduction.induction (append D Sc cutoff j.1)).obj M).obj t) 1 := by
  change BalancedInduction.transformLinear (oldAppendDot_supernatural D Sc cutoff j.1) M t ∈
    parity (R := k) (BalancedInduction.superspace (append D Sc cutoff j.1) M.toFunctor t)
      (BalancedInduction.superspace (append D Sc cutoff j.1) M.toFunctor t) 1
  have hp := congrArg (fun q : ZMod 2 =>
    parity (R := k) (BalancedInduction.superspace (append D Sc cutoff j.1) M.toFunctor t)
      (BalancedInduction.superspace (append D Sc cutoff j.1) M.toFunctor t) q) j.property
  exact hp ▸ BalancedInduction.transformLinear_mem
    (oldAppendDot_supernatural D Sc cutoff j.1) M t

/-- The outer Koszul sign for the actual odd dot and the canonical odd J. -/
theorem inductionDot_sourceParity (j : {j : I // D.parity j = 1})
    (v t : List I)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    inductionDot D Sc cutoff j.1 (coefficientOneModule D Sc cutoff j.1 v)
      (⟨t⟩ : OldCategory D Sc cutoff)
      ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
        (⟨t⟩ : OldCategory D Sc cutoff) z) =
      -(shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
        (⟨t⟩ : OldCategory D Sc cutoff)
        (inductionDot D Sc cutoff j.1
          ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
          (⟨t⟩ : OldCategory D Sc cutoff) z) := by
  let f := parityCoefficientMap D Sc cutoff j.1 v
  have hf := map_mem (BalancedInduction.induction (append D Sc cutoff j.1))
    (parityCoefficientMap_mem D Sc cutoff j.1 v)
  have hj : (shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
      (⟨t⟩ : OldCategory D Sc cutoff) =
      BalancedInduction.mapComponent (append D Sc cutoff j.1) f 1
        (⟨t⟩ : OldCategory D Sc cutoff) := by
    rw [shiftedSourceParityIso_hom_eq_induction_map,
      odd_total_eq_app_one D Sc cutoff hf]
    rfl
  simp only [hj]
  have h := congrArg (fun g => g z)
    (BalancedInduction.transform_mapComponent
      (oldAppendDot_supernatural D Sc cutoff j.1)
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
      f 1 (⟨t⟩ : OldCategory D Sc cutoff))
  have hs : sign k (D.parity j.1 * 1) = -1 := by
    rw [mul_one, j.property, sign_one]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, hs, neg_one_smul] at h
  change BalancedInduction.transformLinear (oldAppendDot_supernatural D Sc cutoff j.1)
      (coefficientOneModule D Sc cutoff j.1 v) (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.mapComponent (append D Sc cutoff j.1) f 1
        (⟨t⟩ : OldCategory D Sc cutoff) z) =
    -BalancedInduction.mapComponent (append D Sc cutoff j.1) f 1
      (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.transformLinear (oldAppendDot_supernatural D Sc cutoff j.1)
        ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
        (⟨t⟩ : OldCategory D Sc cutoff) z)
  exact h

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The sign in the prescribed dotted cap row

The scalar in DeformedMatrixComparison (5) is
(-1)^(n(n+1)/2). For an odd operator T on a superspace, composing T with
source parity changes its iterates by exactly this scalar and output parity.
This linear-algebra identity is the sign step used by the concrete shifted
counit comparison; it does not assert an action or a matrix inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {k : Type u} [CommRing k]

def capRowSign (n : ℕ) : k := (-1 : k) ^ (n + 1).choose 2

private theorem sign_natCast (n : ℕ) :
    sign k (n : ZMod 2) = (-1 : k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, sign_add, ih, sign_one, pow_succ]

theorem capRowSign_succ (n : ℕ) :
    capRowSign (k := k) (n + 1) =
      sign k ((n + 1 : ℕ) : ZMod 2) * capRowSign (k := k) n := by
  have h : (n + 1 + 1).choose 2 = (n + 1) + (n + 1).choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ (n + 1) 1
  unfold capRowSign
  rw [h, pow_add, sign_natCast]

/-- The prescribed cap scalar cancels the sign introduced by composing an
odd dot with source parity. The odd-operator premise is discharged by the
concrete module dot in the shifted-counit comparison. -/
theorem capRowSign_sgn_iterate (V : SVec k) (T : V →ₗ[k] V)
    (hT : T ∈ SVec.parityHom V V 1) (n : ℕ) (z : V) :
    capRowSign (k := k) n • V.sgn (n : ZMod 2)
      ((T.comp (V.sgn 1))^[n] z) = T^[n] z := by
  induction n with
  | zero => simp [capRowSign]
  | succ n ih =>
    let w := (T.comp (V.sgn 1))^[n] z
    have hp : ((n + 1 : ℕ) : ZMod 2) + 1 = (n : ZMod 2) := by
      rw [Nat.cast_add, Nat.cast_one, add_assoc, SVec.zmod2_one_add_one, add_zero]
    have hphi : V.sgn ((n + 1 : ℕ) : ZMod 2) (V.sgn 1 w) =
        V.sgn (n : ZMod 2) w := by
      have h := congrArg (fun f : V →ₗ[k] V => f w)
        (SVec.sgn_comp_sgn V ((n + 1 : ℕ) : ZMod 2) 1)
      simpa only [LinearMap.comp_apply, hp] using h
    have hc := congrArg (fun f : V →ₗ[k] V => f (V.sgn 1 w))
      (SVec.sgn_comp_of_mem hT ((n + 1 : ℕ) : ZMod 2))
    simp only [LinearMap.comp_apply, SVec.coe_toLinearMap, LinearMap.smul_apply,
      one_mul, hphi] at hc
    have hs : V.sgn ((n + 1 : ℕ) : ZMod 2)
        ((T.comp (V.sgn 1))^[n + 1] z) =
        sign k ((n + 1 : ℕ) : ZMod 2) • T (V.sgn (n : ZMod 2) w) := by
      rw [Function.iterate_succ_apply']
      exact hc
    have he : capRowSign (k := k) (n + 1) *
        sign k ((n + 1 : ℕ) : ZMod 2) = capRowSign (k := k) n := by
      rw [capRowSign_succ, mul_right_comm, Supercategory.sign_mul_self, one_mul]
    calc
      capRowSign (k := k) (n + 1) • V.sgn ((n + 1 : ℕ) : ZMod 2)
          ((T.comp (V.sgn 1))^[n + 1] z) =
          capRowSign (k := k) n • T (V.sgn (n : ZMod 2) w) := by
        rw [hs, smul_smul, he]
      _ = T (capRowSign (k := k) n • V.sgn (n : ZMod 2) w) := (map_smul T _ _).symm
      _ = T (T^[n] z) := congrArg T ih
      _ = T^[n + 1] z := (Function.iterate_succ_apply' _ _ _).symm

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Component formulas for the actual shifted matrix entries
The finite families of Brundan--Ellis (1.13)--(1.14) use the prescribed
module unit/cap maps and the canonical parity isomorphisms. These formulas
identify their total component maps without assuming any matrix inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.MatrixEntryTotals
universe u
variable {k : Type u} [CommRing k]
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
private theorem restriction_total (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k B (SVec k)} (f : M ⟶ N) (t : C) :
    ((BalancedInduction.restriction J).map f).total t = f.total (J.obj t) := rfl
end OddMath.QuiverHecke.ELV.MatrixEntryTotals

namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance matrixEntryTotalsPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- The actual unit column on components is the ordinary unit followed by the dot power. -/
theorem moduleUnitColumn_total (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (n : ℕ) :
    SVec.toLinearMap ((moduleUnitColumn D Sc cutoff i M n).total t) =
      ((inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t)) ^ n).comp
        (SVec.toLinearMap (((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app M).total t)) := by
  rw [moduleUnitColumn, Superfunctor.comp_total, SVec.toLinearMap_comp,
    MatrixEntryTotals.restriction_total, inductionDotModule_power_total]

/-- The actual cap row on components is the ordinary dot power followed by the counit. -/
theorem moduleCapRow_total (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (n : ℕ) :
    SVec.toLinearMap ((moduleCapRow D Sc cutoff i M n).total t) =
      (SVec.toLinearMap (((BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M).total t)).comp
        ((inductionDot D Sc cutoff i
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t) ^ n) := by
  rw [moduleCapRow, Superfunctor.comp_total, SVec.toLinearMap_comp,
    inductionDotModule_power_total]

/-- The unit entry uses precisely the canonical source parity coordinate. -/
theorem unitMatrixEntry_some_total (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (m : ℕ) (r : Fin m)
    (b : (unitMatrixFamily D Sc cutoff i M m (some r)).obj t) :
    (unitMatrixEntry D Sc cutoff i M m (some r)).total t b =
      (moduleUnitColumn D Sc cutoff i M r.val).total t
        (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t b) := by
  change ((((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom ≫
    moduleUnitColumn D Sc cutoff i M r.val).total t) b = _
  rw [Superfunctor.comp_total]
  rfl

/-- Removing the canonical target parity coordinate gives the ordinary cap row. -/
theorem capMatrixEntry_some_total (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (m : ℕ) (r : Fin m)
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t) :
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t
      ((capMatrixEntry D Sc cutoff i M m (some r)).total t z) =
      (moduleCapRow D Sc cutoff i M r.val).total t z := by
  change (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom.total t)
    (((moduleCapRow D Sc cutoff i M r.val ≫
      ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).inv).total t) z) = _
  rw [Superfunctor.comp_total]
  exact (moduleIsoLinearEquiv
    ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t).apply_symm_apply _

/-- The first source-shifted module entry before evaluating components. -/
theorem unitMatrixEntry_none (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) :
    unitMatrixEntry D Sc cutoff i M m none =
      ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
        ((BalancedInduction.induction (append D Sc cutoff i)).obj
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj M))).hom ≫
            matrixMateComponent D Sc cutoff i M := rfl

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Dot powers and output parity under comparison maps

The dotted unit and cap rows of DeformedMatrixComparison (1), (2), (5)
require powers of the same signed dot, followed by the prescribed output
parity correction. The rectangular comparison lemmas below apply to the
selected scalar and weighted append maps before coend carriers are specialized.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u

section LinearPowers
variable {k V W : Type u} [CommRing k]
  [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  (C : V →ₗ[k] W) (f : Module.End k V) (g : Module.End k W)

/-- A rectangular intertwiner carries every ordinary power of the given
signed operators to the same power of the target operator. -/
theorem intertwine_pow_apply (h : ∀ x, C (f x) = g (C x)) (n : ℕ) (x : V) :
    C ((f ^ n) x) = (g ^ n) (C x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

/-- The same rectangular power comparison as an equality of linear maps;
only additive commutative monoids are required for the two carriers. -/
theorem intertwine_pow (h : C ∘ₗ f = g ∘ₗ C) (n : ℕ) :
    C ∘ₗ (f ^ n) = (g ^ n) ∘ₗ C := by
  apply LinearMap.ext
  intro x
  exact intertwine_pow_apply C f g (fun x => LinearMap.congr_fun h x) n x

end LinearPowers

section Parity
variable {k : Type u} [CommRing k] (V W : SVec k)
  (C : V →ₗ[k] W) (hC : C ∈ SVec.parityHom V W 0)
include hC

end Parity
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Input-module naturality of the prescribed matrix entries

DeformedMatrixComparison section 4 requires input-module naturality as
well as output-arrow naturality. The prescribed mate, dotted units and
dotted caps are homogeneous supernatural families. Their literal parity
shifts make even natural transformations on the entire old module category.
No module map is assumed even.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Whole prescribed matrices natural in input modules

DeformedMatrixComparison section 4, finite-family assembly of the unit/cap
entries. This assembly includes odd and inhomogeneous input maps.
The fixed-content inverse construction is in ELVContentMatrixFunctorInverse;
identification with the chosen content E/F composites remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The prescribed shifted unit coordinate map, with explicit endpoint transport. -/
def unitMatrixCoordinateMap (i : I) (m : ℕ)
    {M N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)} (f : M ⟶ N)
    (a : Option (Fin m)) :
    unitMatrixFamily D Sc cutoff i M m a ⟶ unitMatrixFamily D Sc cutoff i N m a :=
  eqToHom (unitMatrixSummandFunctor_obj D Sc cutoff i m a M).symm ≫
    (unitMatrixSummandFunctor D Sc cutoff i m a).map f ≫
      eqToHom (unitMatrixSummandFunctor_obj D Sc cutoff i m a N)

/-- The prescribed shifted cap coordinate map, with explicit endpoint transport. -/
def capMatrixCoordinateMap (i : I) (m : ℕ)
    {M N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)} (f : M ⟶ N)
    (a : Option (Fin m)) :
    capMatrixFamily D Sc cutoff i M m a ⟶ capMatrixFamily D Sc cutoff i N m a :=
  eqToHom (capMatrixSummandFunctor_obj D Sc cutoff i m a M).symm ≫
    (capMatrixSummandFunctor D Sc cutoff i m a).map f ≫
      eqToHom (capMatrixSummandFunctor_obj D Sc cutoff i m a N)

/-- The full finite unit source is functorial on every supernatural module map. -/
def unitMatrixSourceFunctor (i : I) (m : ℕ) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) ⥤
      Superfunctor k (OldCategory D Sc cutoff) (SVec k) where
  obj M := FiniteSupermodule.product (unitMatrixFamily D Sc cutoff i M m)
  map f := FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m f)
  map_id M := by
    rw [show unitMatrixCoordinateMap D Sc cutoff i m (𝟙 M) =
      (fun a => 𝟙 (unitMatrixFamily D Sc cutoff i M m a)) by
        funext a
        cases a <;> simp [unitMatrixCoordinateMap]]
    exact FiniteSupermodule.productMap_id _
  map_comp f g := by
    rw [← FiniteSupermodule.productMap_comp]
    congr 1
    funext a
    cases a <;> simp [unitMatrixCoordinateMap]

/-- The full finite cap target is functorial on every supernatural module map. -/
def capMatrixTargetFunctor (i : I) (m : ℕ) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) ⥤
      Superfunctor k (OldCategory D Sc cutoff) (SVec k) where
  obj M := FiniteSupermodule.product (capMatrixFamily D Sc cutoff i M m)
  map f := FiniteSupermodule.productMap (capMatrixCoordinateMap D Sc cutoff i m f)
  map_id M := by
    rw [show capMatrixCoordinateMap D Sc cutoff i m (𝟙 M) =
      (fun a => 𝟙 (capMatrixFamily D Sc cutoff i M m a)) by
        funext a
        cases a <;> simp [capMatrixCoordinateMap]]
    exact FiniteSupermodule.productMap_id _
  map_comp f g := by
    rw [← FiniteSupermodule.productMap_comp]
    congr 1
    funext a
    cases a <;> simp [capMatrixCoordinateMap]

instance (i : I) (m : ℕ) : (unitMatrixSourceFunctor D Sc cutoff i m).Additive where
  map_add {M N f g} := by
    change FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m (f + g)) =
      FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m f) +
        FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m g)
    rw [← FiniteSupermodule.productMap_add]
    congr 1
    funext a
    cases a <;> simp [unitMatrixCoordinateMap]

instance (i : I) (m : ℕ) : (capMatrixTargetFunctor D Sc cutoff i m).Additive where
  map_add {M N f g} := by
    change FiniteSupermodule.productMap (capMatrixCoordinateMap D Sc cutoff i m (f + g)) =
      FiniteSupermodule.productMap (capMatrixCoordinateMap D Sc cutoff i m f) +
        FiniteSupermodule.productMap (capMatrixCoordinateMap D Sc cutoff i m g)
    rw [← FiniteSupermodule.productMap_add]
    congr 1
    funext a
    cases a <;> simp [capMatrixCoordinateMap]

instance (i : I) (m : ℕ) : (unitMatrixSourceFunctor D Sc cutoff i m).Linear k where
  map_smul f r := by
    change FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m (r • f)) =
      r • FiniteSupermodule.productMap (unitMatrixCoordinateMap D Sc cutoff i m f)
    rw [← FiniteSupermodule.productMap_smul]
    congr 1
    funext a
    cases a <;> simp [unitMatrixCoordinateMap]

instance (i : I) (m : ℕ) : (capMatrixTargetFunctor D Sc cutoff i m).Linear k where
  map_smul f r := by
    change FiniteSupermodule.productMap (capMatrixCoordinateMap D Sc cutoff i m (r • f)) =
      r • FiniteSupermodule.productMap (capMatrixCoordinateMap D Sc cutoff i m f)
    rw [← FiniteSupermodule.productMap_smul]
    congr 1
    funext a
    cases a <;> simp [capMatrixCoordinateMap]

instance (i : I) (m : ℕ) : IsSuperfunctor k (unitMatrixSourceFunctor D Sc cutoff i m) where
  map_mem {M N p f} hf := by
    apply FiniteSupermodule.productMap_mem
    intro a
    exact (show unitMatrixCoordinateMap D Sc cutoff i m f a ∈ parity (R := k) _ _ p from by
      simpa only [unitMatrixCoordinateMap, zero_add, add_zero] using
        comp_mem (eqToHom_mem (R := k)
          (unitMatrixSummandFunctor_obj D Sc cutoff i m a M).symm)
          (comp_mem (IsSuperfunctor.map_mem
            (F := unitMatrixSummandFunctor D Sc cutoff i m a) hf)
            (eqToHom_mem (R := k) (unitMatrixSummandFunctor_obj D Sc cutoff i m a N))))

instance (i : I) (m : ℕ) : IsSuperfunctor k (capMatrixTargetFunctor D Sc cutoff i m) where
  map_mem {M N p f} hf := by
    apply FiniteSupermodule.productMap_mem
    intro a
    exact (show capMatrixCoordinateMap D Sc cutoff i m f a ∈ parity (R := k) _ _ p from by
      simpa only [capMatrixCoordinateMap, zero_add, add_zero] using
        comp_mem (eqToHom_mem (R := k)
          (capMatrixSummandFunctor_obj D Sc cutoff i m a M).symm)
          (comp_mem (IsSuperfunctor.map_mem
            (F := capMatrixSummandFunctor D Sc cutoff i m a) hf)
            (eqToHom_mem (R := k) (capMatrixSummandFunctor_obj D Sc cutoff i m a N))))

/-- The literal finite unit matrix as an even module map. -/
def unitMatrixModuleMap (i : I) (m : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (unitMatrixSourceFunctor D Sc cutoff i m).obj M ⟶
      (BalancedInduction.induction (append D Sc cutoff i) ⋙
        BalancedInduction.restriction (append D Sc cutoff i)).obj M :=
  FiniteSupermodule.columnsHom (unitMatrixEntry D Sc cutoff i M m)
    (unitMatrixEntry_mem D Sc cutoff i M m)

/-- The whole finite unit matrix is natural in arbitrary input-module maps. -/
def unitMatrixModuleNatTrans (i : I) (m : ℕ) :
    unitMatrixSourceFunctor D Sc cutoff i m ⟶
      BalancedInduction.induction (append D Sc cutoff i) ⋙
        BalancedInduction.restriction (append D Sc cutoff i) where
  app := unitMatrixModuleMap D Sc cutoff i m
  naturality M N f := by
    apply FiniteSupermodule.productMap_columnsHom
    intro a
    cases a with
    | none => simpa [unitMatrixCoordinateMap, unitMatrixEntryNatTrans_app] using
        (unitMatrixEntryNatTrans D Sc cutoff i m none).naturality f
    | some r => simpa [unitMatrixCoordinateMap, unitMatrixEntryNatTrans_app] using
        (unitMatrixEntryNatTrans D Sc cutoff i m (some r)).naturality f

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end
