import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import OddMath.QuiverHecke.CyclotomicAction.AppendContent
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.SKM.RouquierShiftedAdjunction
import OddMath.QuiverHecke.CyclotomicAction.BoundaryNumerator
import OddMath.QuiverHecke.CyclotomicAction.AppendSourceRows
import OddMath.QuiverHecke.CyclotomicAction.ChronologicalTails
import StringDiagrams.Super.SVec
import Mathlib.Data.Nat.Choose.Basic
import OddMath.QuiverHecke.CyclotomicAction.ContentModule
import Mathlib.Algebra.Module.LinearMap.End
import OddMath.SKM.RouquierHomPostNaturalInverse
import OddMath.Algebra.FiniteSupermoduleFunctor

/-!
# Cap input matrices

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Ordinary unit and dot columns of the positive matrix

The positive columns in DeformedMatrixComparison (4) are the ordinary
adjunction unit followed by induction-dot powers. Under the canonical
upper-Hom equivalence they are the literal output-polynomial columns,
with the prescribed odd dot-power scalar retained. Both moving parities
and complete old Hom coefficients are included.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The scalar introduced by iterating the ordinary induction dot. -/
def inductionUnitDotSign (p : ZMod 2) (n : ℕ) : k := sign k (n.choose 2 • p)

theorem inductionUnitDotSign_succ (p : ZMod 2) (n : ℕ) :
    inductionUnitDotSign (k := k) p (n + 1) =
      sign k (n • p) * inductionUnitDotSign (k := k) p n := by
  have he : (n + 1).choose 2 = n + n.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ n 1
  simp only [inductionUnitDotSign, he, add_nsmul, sign_add]

private def oldAppendPower (i : I) (t : OldCategory D Sc cutoff) (n : ℕ) :
    (append D Sc cutoff i).obj t ⟶ (append D Sc cutoff i).obj t :=
  (ideal D Sc cutoff _ _).mkQ (appendMovingPower D Sc cutoff i t.word n)

private theorem oldAppendPower_mem (i : I) (t : OldCategory D Sc cutoff) (n : ℕ) :
    oldAppendPower D Sc cutoff i t n ∈ parity (R := k) _ _ (n • D.parity i) := by
  apply Submodule.mem_map_of_mem
  rw [appendMovingPower_whisker]
  exact appendComponent_mem D Sc cutoff (firstDot_pow_parity D Sc i [] n) t.word

private theorem oldAppendPower_zero (i : I) (t : OldCategory D Sc cutoff) :
    oldAppendPower D Sc cutoff i t 0 = 𝟙 _ := by
  simp only [oldAppendPower, appendMovingPower, pow_zero, End.one_def, affineUnit_id]
  rfl

private theorem oldAppendPower_succ (i : I) (t : OldCategory D Sc cutoff) (n : ℕ) :
    oldAppendDotComponent D Sc cutoff i t ≫ oldAppendPower D Sc cutoff i t n =
      oldAppendPower D Sc cutoff i t (n + 1) := by
  rw [oldAppendDotComponent_eq]
  change (ideal D Sc cutoff _ _).mkQ
    (appendMovingPower D Sc cutoff i t.word 1 ≫ appendMovingPower D Sc cutoff i t.word n) = _
  congr 1
  unfold appendMovingPower
  rw [← affineUnit_comp]
  change affineUnit D Sc cutoff _ _
    ((dotE D Sc (t.word ++ [i]) t.word.length) ^ n *
      (dotE D Sc (t.word ++ [i]) t.word.length) ^ 1) = _
  rw [pow_one, ← pow_succ]

private theorem tensor_smul_first (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s t : OldCategory D Sc cutoff) (c : k)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : M.obj s) :
    BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s (c • g) b =
      c • BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s g b := by
  simp only [BalancedInduction.tensor, ← TensorProduct.smul_tmul', map_smul]

/-- Powers on the actual unit tensor, including the odd power scalar. -/
theorem inductionDot_iterate_unit (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (n : ℕ) (b : M.obj t) :
    (inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t))^[n]
      (BalancedInduction.unit (append D Sc cutoff i) M.toFunctor t b) =
      inductionUnitDotSign (k := k) (D.parity i) n •
        BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor t
          (oldAppendPower D Sc cutoff i t n) b := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, inductionUnitDotSign, Nat.choose_zero_succ,
      zero_nsmul, sign_zero, one_smul, oldAppendPower_zero, BalancedInduction.unit_apply]
  | succ n ih =>
    have hp : D.parity i * (n • D.parity i) = n • D.parity i := by
      rcases parity_eq_zero_or_one (D.parity i) with h | h <;> rw [h] <;> simp
    rw [Function.iterate_succ_apply', ih, map_smul, inductionDot_tensor,
      twist_of_mem (D.parity i) (oldAppendPower_mem D Sc cutoff i t n), hp,
      Linear.comp_smul, tensor_smul_first, smul_smul,
      oldAppendPower_succ, inductionUnitDotSign_succ, mul_comm]

/-- The packaged adjunction unit is the existing raw unit on every coefficient. -/
theorem adjunctionUnit_total_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (b : M.obj t) :
    ((BalancedInduction.adjunctionUnit (append D Sc cutoff i)).app M).total t b =
      BalancedInduction.unit (append D Sc cutoff i) M.toFunctor t b := by
  simp only [BalancedInduction.adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    BalancedInduction.unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

/-- The ordinary categorical unit/dot column, in its canonical upper-Hom coordinates. -/
def inductionUnitDotColumn (i : I) (v t : List I) (n : ℕ) :
    Old D Sc cutoff v t →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  (OldInductionRepresentable.upperHomEquiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).toLinearMap.comp
      (((inductionDot D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))
        ((append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff))) ^ n).comp
        (BalancedInduction.unit (append D Sc cutoff i)
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).toFunctor
          (⟨t⟩ : OldCategory D Sc cutoff)))

/-- No coefficient projection occurs: the actual categorical column equals
its prescribed scalar times the literal polynomial column on full Old(v,t). -/
theorem inductionUnitDotColumn_apply (i : I) (v t : List I) (n : ℕ)
    (b : Old D Sc cutoff v t) :
    inductionUnitDotColumn D Sc cutoff i v t n b =
      inductionUnitDotSign (k := k) (D.parity i) n •
        canonicalAppendTarget D Sc cutoff i v (t ++ [i])
          (appendOutputEmbedding D Sc cutoff i v t (Finsupp.single n b)) := by
  change OldInductionRepresentable.upperHomEquiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
    (((inductionDot D Sc cutoff i
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))
      ((append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff))) ^ n)
      (BalancedInduction.unit (append D Sc cutoff i)
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).toFunctor
        (⟨t⟩ : OldCategory D Sc cutoff) b)) = _
  rw [Module.End.pow_apply, inductionDot_iterate_unit, map_smul]
  congr 1
  have hforward := OldInductionRepresentable.upperHomEquiv_tensor D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
    (⟨t⟩ : OldCategory D Sc cutoff) (oldAppendPower D Sc cutoff i ⟨t⟩ n)
    (show (⟨v⟩ : OldCategory D Sc cutoff) ⟶ (⟨t⟩ : OldCategory D Sc cutoff) from b)
  refine hforward.trans ?_
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  rw [appendOutputEmbedding_single, canonicalAppendTarget_projection]
  rfl

/-- Finite polynomial assembly of the prescribed scalar-normalized ordinary columns. -/
def unitDotPolynomialMap (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  Finsupp.lsum k fun n => inductionUnitDotSign (k := k) (D.parity i) n •
    inductionUnitDotColumn D Sc cutoff i v t n

@[simp] theorem unitDotPolynomialMap_single (i : I) (v t : List I) (n : ℕ)
    (b : Old D Sc cutoff v t) :
    unitDotPolynomialMap D Sc cutoff i v t (Finsupp.single n b) =
      canonicalAppendTarget D Sc cutoff i v (t ++ [i])
        (appendOutputEmbedding D Sc cutoff i v t (Finsupp.single n b)) := by
  rw [unitDotPolynomialMap, Finsupp.lsum_single, LinearMap.smul_apply,
    inductionUnitDotColumn_apply, smul_smul]
  simp only [inductionUnitDotSign, Supercategory.sign_mul_self, one_smul]

/-- The whole polynomial column map equals the actual ordinary unit/dot assembly. -/
theorem unitDotPolynomialMap_eq (i : I) (v t : List I) :
    unitDotPolynomialMap D Sc cutoff i v t =
      (canonicalAppendTarget D Sc cutoff i v (t ++ [i])).comp
        (appendOutputEmbedding D Sc cutoff i v t) := by
  apply LinearMap.ext
  intro f
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single n b => exact unitDotPolynomialMap_single D Sc cutoff i v t n b

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # The linear equivalence of the canonical actual source isomorphism

The component totals of the fixed shiftedSourceParityIso are inverse linear
maps. Composing with the literal coefficient(1) comparison identifies the
actual induction-restriction carrier with the prescribed balanced Source.
The actual counit square is retained. Higher dot/cap normalization is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The underlying component equivalence of the fixed actual source isomorphism. -/
def shiftedSourceCanonicalEquiv (j : {j : I // D.parity j = 1}) (v t : List I) :
    ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
      Source D Sc cutoff j.1 v t :=
  (moduleIsoLinearEquiv (shiftedSourceParityIso D Sc cutoff j.1 v)
    (⟨t⟩ : OldCategory D Sc cutoff)).trans
      (coefficientOneSourceEquiv D Sc cutoff j v t)

@[simp] theorem shiftedSourceCanonicalEquiv_apply (j : {j : I // D.parity j = 1})
    (v t : List I)
    (x : ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    shiftedSourceCanonicalEquiv D Sc cutoff j v t x =
      coefficientOneSourceEquiv D Sc cutoff j v t
        ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
          (⟨t⟩ : OldCategory D Sc cutoff) x) := rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Actual cap and input-dot maps on arbitrary old Hom endpoints

The cap is the actual shifted adjunction counit followed by total output
parity. The input dot is the actual induction dot composed with actual
source grading. Since coefficient(1) is parity shifted, this source grading
contains an extra minus on tensors. No quotient annihilation or chosen
replacement map is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The fixed balanced quotient, named before constructing its grading. -/
abbrev shiftedCarrier (i : I) (v t : List I) :=
  BalancedInduction.Obj (append D Sc cutoff i) (coefficient D Sc cutoff 1 i v)
    (⟨t⟩ : OldCategory D Sc cutoff)

def shiftedSourceSpace (i : I) (v t : List I) : SVec k :=
  BalancedInduction.superspace (append D Sc cutoff i) (coefficient D Sc cutoff 1 i v)
    (⟨t⟩ : OldCategory D Sc cutoff)

/-- An actual counit component, followed by the prescribed full output twist. -/
def shiftedInputContraction (i : I) (v t : List I) :
    shiftedCarrier D Sc cutoff i v t →ₗ[k] Old D Sc cutoff v t :=
  (oldTwist D Sc cutoff 1 v t).comp
    ((shiftedSourceCounit D Sc cutoff i v).total (⟨t⟩ : OldCategory D Sc cutoff))

/-- Actual grading on the shifted source, then the actual induction dot.
The coefficient shift is part of this grading and must not be discarded. -/
def shiftedInputDot (j : {j : I // D.parity j = 1}) (v t : List I) :
    shiftedCarrier D Sc cutoff j.1 v t →ₗ[k]
      shiftedCarrier D Sc cutoff j.1 v t :=
  (inductionDot D Sc cutoff j.1 (coefficientOneModule D Sc cutoff j.1 v)
    (⟨t⟩ : OldCategory D Sc cutoff)).comp
      ((shiftedSourceSpace D Sc cutoff j.1 v t).sgn 1)

/-- The actual cap on the literal independently defined source. -/
def sourceInputContraction (j : {j : I // D.parity j = 1}) (v t : List I) :
    Source D Sc cutoff j.1 v t →ₗ[k] Old D Sc cutoff v t :=
  (shiftedInputContraction D Sc cutoff j.1 v t).comp
    (coefficientOneSourceEquiv D Sc cutoff j v t).symm.toLinearMap

/-- The actual input dot on the literal independently defined source. -/
def sourceInputDot (j : {j : I // D.parity j = 1}) (v t : List I) :
    Source D Sc cutoff j.1 v t →ₗ[k] Source D Sc cutoff j.1 v t :=
  (coefficientOneSourceEquiv D Sc cutoff j v t).toLinearMap.comp
    ((shiftedInputDot D Sc cutoff j v t).comp
      (coefficientOneSourceEquiv D Sc cutoff j v t).symm.toLinearMap)

theorem sourceInputContraction_carrier (j : {j : I // D.parity j = 1})
    (v t : List I) (z : shiftedCarrier D Sc cutoff j.1 v t) :
    sourceInputContraction D Sc cutoff j v t
      (coefficientOneSourceEquiv D Sc cutoff j v t z) =
      shiftedInputContraction D Sc cutoff j.1 v t z := by
  simp only [sourceInputContraction, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem sourceInputDot_carrier (j : {j : I // D.parity j = 1})
    (v t : List I) (z : shiftedCarrier D Sc cutoff j.1 v t) :
    sourceInputDot D Sc cutoff j v t
      (coefficientOneSourceEquiv D Sc cutoff j v t z) =
      coefficientOneSourceEquiv D Sc cutoff j v t
        (shiftedInputDot D Sc cutoff j v t z) := by
  simp only [sourceInputDot, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- The coefficient module comparison is identity on every underlying vector. -/
theorem inducedCoefficientForward_total_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    ((BalancedInduction.induction (append D Sc cutoff i)).map
      (coefficientModuleForward D Sc cutoff i v)).total (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      BalancedInduction.tensor (append D Sc cutoff i)
        (parityRestrictedRepresentable D Sc cutoff i v).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b := by
  change (BalancedInduction.moduleMap (append D Sc cutoff i)
    (coefficientModuleForward D Sc cutoff i v)).total _
      (BalancedInduction.tensor _ _ _ g b) = _
  rw [BalancedInduction.moduleMap_total_tensor]
  simp only [coefficientModuleForward_app, ↓reduceIte, one_ne_zero]
  change BalancedInduction.tensor (append D Sc cutoff i)
      (parityRestrictedRepresentable D Sc cutoff i v).toFunctor
      (⟨s⟩ : OldCategory D Sc cutoff) g b +
    BalancedInduction.tensor (append D Sc cutoff i)
      (parityRestrictedRepresentable D Sc cutoff i v).toFunctor
      (⟨s⟩ : OldCategory D Sc cutoff)
      (twist k 1 (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g) 0 =
    BalancedInduction.tensor (append D Sc cutoff i)
      (parityRestrictedRepresentable D Sc cutoff i v).toFunctor
      (⟨s⟩ : OldCategory D Sc cutoff) g b
  rw [BalancedInduction.tensor_zero_right, add_zero]

/-- The actual shifted counit acts by composition with the full kernel twist. -/
theorem shiftedSourceCounit_total_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    (shiftedSourceCounit D Sc cutoff i v).total (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      oldComp D Sc cutoff v (s ++ [i]) t b (oldTwist D Sc cutoff 1 (s ++ [i]) t g) := by
  have hmap : ((BalancedInduction.induction (append D Sc cutoff i)).mapIso
      (coefficientParityModuleIso D Sc cutoff i v)).hom =
      (BalancedInduction.induction (append D Sc cutoff i)).map
        (coefficientModuleForward D Sc cutoff i v) := rfl
  rw [shiftedSourceCounit, hmap, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [SVec.comp_apply]
  rw [inducedCoefficientForward_total_tensor]
  change (0 : Old D Sc cutoff v t) +
    ((show Old D Sc cutoff v t from BalancedInduction.counit (append D Sc cutoff i)
      (supermoduleParityObj (oldRepresentable D Sc cutoff
        (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙
          (supermoduleParityObj (oldRepresentable D Sc cutoff
            (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor)
        (⟨s⟩ : OldCategory D Sc cutoff) g b)) + (0 : Old D Sc cutoff v t)) = _
  rw [add_zero, zero_add, BalancedInduction.counit_tensor]
  change (twist k 1
    (X := (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).obj
      (⟨s ++ [i]⟩ : OldCategory D Sc cutoff))
    (Y := (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).obj
      (⟨t⟩ : OldCategory D Sc cutoff))
    ((oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).map
      (X := (⟨s ++ [i]⟩ : OldCategory D Sc cutoff))
      (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g)) b = _
  rw [← Supercategory.map_twist, oldCategory_twist]
  rfl

/-- The actual cap retains parity on the entire coefficient, with arbitrary endpoints. -/
theorem shiftedInputContraction_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    shiftedInputContraction D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      oldComp D Sc cutoff v (s ++ [i]) t
        (oldTwist D Sc cutoff 1 v (s ++ [i]) b) g := by
  have h := congrArg (oldTwist D Sc cutoff 1 v t)
    (shiftedSourceCounit_total_tensor D Sc cutoff i v s t g b)
  change oldTwist D Sc cutoff 1 v t
    ((shiftedSourceCounit D Sc cutoff i v).total (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor ⟨s⟩ g b)) = _
  refine h.trans ?_
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff (s ++ [i]) t).mkQ_surjective g
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  change (ideal D Sc cutoff v t).mkQ (twist k 1 (b ≫ twist k 1 g)) =
    (ideal D Sc cutoff v t).mkQ (twist k 1 b ≫ g)
  rw [twist_comp, twist_twist]

private theorem induced_sgn_tensor
    {C T : Type u} [Category.{u} C] [Category.{u} T]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive T] [Linear k T] [Supercategory k T]
    (J : C ⥤ T) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (M : Superfunctor k C (SVec k)) (v : C) (w : T)
    (h : J.obj v ⟶ w) (m : M.obj v) :
    (BalancedInduction.superspace J M.toFunctor w).sgn 1
        (BalancedInduction.tensor J M.toFunctor v h m) =
      BalancedInduction.tensor J M.toFunctor v
        (twist k 1 (X := J.obj v) (Y := w) h) ((M.obj v).sgn 1 m) := by
  rw [SVec.sgn_apply (BalancedInduction.superspace J M.toFunctor w) 1
    (BalancedInduction.tensor J M.toFunctor v h m), SVec.sgn_apply]
  simp only [sign_one, neg_one_smul, ← sub_eq_add_neg]
  rw [BalancedInduction.proj_tensor, BalancedInduction.proj_tensor]
  simp only [zero_add, SVec.zmod2_one_add_one]
  rw [twist_apply, sign_one, neg_one_smul, ← sub_eq_add_neg]
  simp only [BalancedInduction.tensor, TensorProduct.sub_tmul, TensorProduct.tmul_sub, map_sub]
  abel

/-- Actual grading on coefficient(1) contributes the shift minus, including
the entire old coefficient and the kernel-arrow parity. -/
theorem shiftedSource_sgn_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    (shiftedSourceSpace D Sc cutoff i v t).sgn 1
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      -BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff)
        (twist k 1 g) (oldTwist D Sc cutoff 1 v (s ++ [i]) b) := by
  have hbt : oldTwist D Sc cutoff 1 v (s ++ [i]) b =
      oldProj D Sc cutoff v (s ++ [i]) 0 b - oldProj D Sc cutoff v (s ++ [i]) 1 b := by
    obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    rw [oldProj_mk, oldProj_mk]
    change (ideal D Sc cutoff v (s ++ [i])).mkQ (twist k 1 a) = _
    rw [twist_apply, sign_one, neg_one_smul, ← sub_eq_add_neg, map_sub]
  have hsum : oldProj D Sc cutoff v (s ++ [i]) 0 b +
      oldProj D Sc cutoff v (s ++ [i]) 1 b = b := by
    obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    rw [oldProj_mk, oldProj_mk, ← map_add, proj_add_proj]
  have hb : ((coefficientOneModule D Sc cutoff i v).obj
      (⟨s⟩ : OldCategory D Sc cutoff)).sgn 1 b =
      -oldTwist D Sc cutoff 1 v (s ++ [i]) b := by
    rw [SVec.sgn_apply ((coefficientOneModule D Sc cutoff i v).obj
      (⟨s⟩ : OldCategory D Sc cutoff)) 1 b, sign_one, neg_one_smul, ← sub_eq_add_neg]
    change (b - oldProj D Sc cutoff v (s ++ [i]) (1 + 1) b) -
      oldProj D Sc cutoff v (s ++ [i]) (1 + 1) b = _
    rw [SVec.zmod2_one_add_one, hbt]
    have hbsub : b - oldProj D Sc cutoff v (s ++ [i]) 0 b =
        oldProj D Sc cutoff v (s ++ [i]) 1 b :=
      sub_eq_iff_eq_add.mpr (hsum.symm.trans (add_comm _ _))
    rw [hbsub]
    abel
  have h := induced_sgn_tensor (append D Sc cutoff i)
    (coefficientOneModule D Sc cutoff i v) (⟨s⟩ : OldCategory D Sc cutoff)
    (⟨t⟩ : OldCategory D Sc cutoff) g b
  refine h.trans ?_
  rw [hb]
  simp only [BalancedInduction.tensor, TensorProduct.tmul_neg, map_neg]

/-- The specified input-dot representative formula follows from the actual
dot and actual shifted grading, rather than from an assumed kernel map. -/
theorem shiftedInputDot_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    shiftedInputDot D Sc cutoff j v t
      (BalancedInduction.tensor (append D Sc cutoff j.1)
        (coefficientOneModule D Sc cutoff j.1 v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      -BalancedInduction.tensor (append D Sc cutoff j.1)
        (coefficientOneModule D Sc cutoff j.1 v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff)
        (oldAppendDotComponent D Sc cutoff j.1 (⟨s⟩ : OldCategory D Sc cutoff) ≫ g)
        (oldTwist D Sc cutoff 1 v (s ++ [j.1]) b) := by
  change inductionDot D Sc cutoff j.1 (coefficientOneModule D Sc cutoff j.1 v)
    (⟨t⟩ : OldCategory D Sc cutoff)
      ((shiftedSourceSpace D Sc cutoff j.1 v t).sgn 1
        (BalancedInduction.tensor (append D Sc cutoff j.1)
          (coefficientOneModule D Sc cutoff j.1 v).toFunctor ⟨s⟩ g b)) = _
  rw [shiftedSource_sgn_tensor,
    map_neg, inductionDot_tensor, j.property, twist_twist]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # The input moving dot on the prescribed crossing source

The existing append moving operator is transported through the concrete
crossing decoder. Corrected rho and the actual short-column square prove
preservation of the Pprime relations, so the operator descends to the
independently prescribed cyclotomic source. This is input-oriented and
is not yet identified with the categorical signed-dot normalization.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def crossingInputDotAffine (j : {j : I // D.parity j = 1}) (v : List I) :
    ShortTarget D Sc cutoff j.1 v v →ₗ[k] ShortTarget D Sc cutoff j.1 v v :=
  ShortCrossCoordinates.decode D Sc cutoff j.1 v v ∘ₗ
    appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1 ∘ₗ
      shortCross D Sc cutoff j.1 v v

/-- The concrete decoder retains the crossing residual and removes exactly
the existing output-polynomial coordinate. -/
theorem shortCross_decode_residual (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    shortCross D Sc cutoff i v t (ShortCrossCoordinates.decode D Sc cutoff i v t z) =
      z - appendOutputEmbedding D Sc cutoff i v t (appendC0 D Sc cutoff i v t z) := by
  have hz := appendC0_residual_mem D Sc cutoff i v t z
  rw [← ShortCrossCoordinates.range_shortCross] at hz
  obtain ⟨y, hy⟩ := hz
  have hd := congrArg (ShortCrossCoordinates.decode D Sc cutoff i v t) hy
  simp only [ShortCrossCoordinates.decode_shortCross, map_sub,
    ShortCrossCoordinates.decode_embedding, sub_zero] at hd
  rw [hd] at hy
  exact hy

/-- The moving input dot sends every Pprime relation to another Pprime relation. -/
theorem crossingInputDotAffine_pprime (j : {j : I // D.parity j = 1}) (v : List I)
    (a : PprimeDomain D Sc cutoff j.1 v v) :
    crossingInputDotAffine D Sc cutoff j v (pprime D Sc cutoff j.1 v v a) ∈
      LinearMap.range (pprime D Sc cutoff j.1 v v) := by
  have hz : boundaryRho D Sc cutoff j v (v ++ [j.1]) (alpha D Sc cutoff j.1 v v a) ∈
      LinearMap.range (alpha D Sc cutoff j.1 v v) := by
    rw [← ker_outputLongExtraction_eq_range_alpha D Sc cutoff 0 j.1 v,
      LinearMap.mem_ker, outputLongExtraction_boundaryRho,
      outputLongExtraction_alpha, map_zero]
  obtain ⟨a', ha'⟩ := hz
  refine ⟨a', ?_⟩
  change pprime D Sc cutoff j.1 v v a' =
    ShortCrossCoordinates.decode D Sc cutoff j.1 v v
      (appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
        (shortCross D Sc cutoff j.1 v v (pprime D Sc cutoff j.1 v v a)))
  have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v v) a
  have hs' := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v v) a'
  simp only [LinearMap.comp_apply] at hs hs'
  rw [← hs, ← pMap_boundaryRho, ← ha', hs', ShortCrossCoordinates.decode_shortCross]

theorem crossingInputDotAffine_ker_q (j : {j : I // D.parity j = 1}) (v : List I) :
    LinearMap.ker (q D Sc cutoff j.1 v v) ≤
      (LinearMap.ker (q D Sc cutoff j.1 v v)).comap
        (crossingInputDotAffine D Sc cutoff j v) := by
  intro z hz
  rw [← range_pprime_eq_ker_q] at hz
  obtain ⟨a, rfl⟩ := hz
  change crossingInputDotAffine D Sc cutoff j v (pprime D Sc cutoff j.1 v v a) ∈
    LinearMap.ker (q D Sc cutoff j.1 v v)
  rw [← range_pprime_eq_ker_q]
  exact crossingInputDotAffine_pprime D Sc cutoff j v a

/-- Concrete transport of the moving input dot to the original cyclotomic source. -/
def crossingInputDot (j : {j : I // D.parity j = 1}) (v : List I) :
    Source D Sc cutoff j.1 v v →ₗ[k] Source D Sc cutoff j.1 v v :=
  let e := (q D Sc cutoff j.1 v v).quotKerEquivOfSurjective (q_surjective D Sc cutoff j.1 v v)
  e.toLinearMap ∘ₗ
    (LinearMap.ker (q D Sc cutoff j.1 v v)).mapQ
      (LinearMap.ker (q D Sc cutoff j.1 v v)) (crossingInputDotAffine D Sc cutoff j v)
      (crossingInputDotAffine_ker_q D Sc cutoff j v) ∘ₗ e.symm.toLinearMap

@[simp] theorem crossingInputDot_q (j : {j : I // D.parity j = 1}) (v : List I)
    (z : ShortTarget D Sc cutoff j.1 v v) :
    crossingInputDot D Sc cutoff j v (q D Sc cutoff j.1 v v z) =
      q D Sc cutoff j.1 v v (crossingInputDotAffine D Sc cutoff j v z) := by
  simp only [crossingInputDot, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.mapQ_apply,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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
namespace OddMath.QuiverHecke.ELVOld
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

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The prescribed dotted row of the shifted counit
DeformedMatrixComparison (5) is proved for the canonical source comparison
and the existing induction dot and counit. Every map below is constructed
from those module functors. The whole output parity and the cap scalar are
retained; no arbitrary source isomorphism or presumed row equality occurs.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem representable_sgn (v t : List I) (p : ZMod 2)
    (b : Old D Sc cutoff v t) :
    ((oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).obj
      (⟨t⟩ : OldCategory D Sc cutoff)).sgn p b = oldTwist D Sc cutoff p v t b := by
  change (Supercategory.homSVec k (OldCategory D Sc cutoff)
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).sgn p b = _
  rw [SVec.sgn_apply, Supercategory.homSVec_proj, Supercategory.homSVec_proj,
    ← oldCategory_twist D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)
      (⟨t⟩ : OldCategory D Sc cutoff) p b, twist_apply]

private theorem even_total_mem
    {M N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)} {f : M ⟶ N}
    (hf : f ∈ parity (R := k) M N 0) (t : OldCategory D Sc cutoff) :
    f.total t ∈ parity (R := k) (M.obj t) (N.obj t) 0 := by
  change f.app 0 t + f.app 1 t ∈ _
  rw [Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide) t, add_zero]
  exact f.app_mem 0 t

/-- The exact cap-row normalization for the actual induction dot, canonical
whole source comparison and actual adjunction counit, at arbitrary old endpoints.
The scalar is exactly (-1)^(n(n+1)/2) by capRowSign_eq. -/
theorem shiftedCapRow_normalization (j : {j : I // D.parity j = 1})
    (v t : List I) (n : ℕ)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    capRowSign (k := k) n • oldTwist D Sc cutoff ((n + 1 : ℕ) : ZMod 2) v t
      (shiftedInputContraction D Sc cutoff j.1 v t
        ((shiftedInputDot D Sc cutoff j v t)^[n]
          ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
            (⟨t⟩ : OldCategory D Sc cutoff) z))) =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
          (⟨t⟩ : OldCategory D Sc cutoff)
          ((inductionDot D Sc cutoff j.1
            ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
            (⟨t⟩ : OldCategory D Sc cutoff))^[n] z) := by
  let U := (unshiftedSourceModule D Sc cutoff j.1 v).obj
    (⟨t⟩ : OldCategory D Sc cutoff)
  let S := shiftedSourceSpace D Sc cutoff j.1 v t
  let O := (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).obj
    (⟨t⟩ : OldCategory D Sc cutoff)
  let J : U →ₗ[k] S := (shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
    (⟨t⟩ : OldCategory D Sc cutoff)
  let A : S →ₗ[k] O := (shiftedSourceCounit D Sc cutoff j.1 v).total
    (⟨t⟩ : OldCategory D Sc cutoff)
  let C : U →ₗ[k] O := ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
      (⟨t⟩ : OldCategory D Sc cutoff)
  let T : U →ₗ[k] U := inductionDot D Sc cutoff j.1
    ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
    (⟨t⟩ : OldCategory D Sc cutoff)
  let Xs : S →ₗ[k] S := shiftedInputDot D Sc cutoff j v t
  have hJ : J ∈ SVec.parityHom U S 1 :=
    odd_total_mem D Sc cutoff (shiftedSourceParityIso_hom_mem D Sc cutoff j.1 v) _
  have hC : C ∈ SVec.parityHom U O 0 :=
    even_total_mem D Sc cutoff
      (BalancedInduction.adjunctionCounit_mem (append D Sc cutoff j.1)
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) _
  have hT : T ∈ SVec.parityHom U U 1 := inductionDot_mem D Sc cutoff j _ _
  have hJsign (w : U) : S.sgn 1 (J w) = -J (U.sgn 1 w) := by
    have h := congrArg (fun f : U →ₗ[k] S => f w) (SVec.sgn_comp_of_mem hJ 1)
    simpa using h
  have hXJ (w : U) : Xs (J w) = J ((T.comp (U.sgn 1)) w) := by
    change inductionDot D Sc cutoff j.1 (coefficientOneModule D Sc cutoff j.1 v)
      (⟨t⟩ : OldCategory D Sc cutoff) (S.sgn 1 (J w)) = J (T (U.sgn 1 w))
    rw [hJsign, map_neg]
    change -inductionDot D Sc cutoff j.1 (coefficientOneModule D Sc cutoff j.1 v)
        (⟨t⟩ : OldCategory D Sc cutoff)
        ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
          (⟨t⟩ : OldCategory D Sc cutoff) (U.sgn 1 w)) =
      (shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
        (⟨t⟩ : OldCategory D Sc cutoff)
        (inductionDot D Sc cutoff j.1
          ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
          (⟨t⟩ : OldCategory D Sc cutoff) (U.sgn 1 w))
    exact neg_eq_iff_eq_neg.mpr
      (inductionDot_sourceParity D Sc cutoff j v t (U.sgn 1 w))
  have hiter (m : ℕ) (w : U) :
      Xs^[m] (J w) = J ((T.comp (U.sgn 1))^[m] w) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, hXJ, Function.iterate_succ_apply']
  have hAJ (w : U) : A (J w) = C w := by
    have h := congrArg (fun f => f.total (⟨t⟩ : OldCategory D Sc cutoff) w)
      (shiftedSourceParityIso_counit D Sc cutoff j.1 v)
    rw [Superfunctor.comp_total] at h
    change (shiftedSourceCounit D Sc cutoff j.1 v).total
        (⟨t⟩ : OldCategory D Sc cutoff)
        ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
          (⟨t⟩ : OldCategory D Sc cutoff) w) =
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff j.1)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff) w
    exact h
  have hCsign (q : ZMod 2) (w : U) : O.sgn q (C w) = C (U.sgn q w) := by
    have h := congrArg (fun f : U →ₗ[k] O => f w) (SVec.sgn_comp_of_mem hC q)
    simpa using h
  have hp : ((n + 1 : ℕ) : ZMod 2) + 1 = (n : ZMod 2) := by
    rw [Nat.cast_add, Nat.cast_one, add_assoc, SVec.zmod2_one_add_one, add_zero]
  have hsgn (w : O) :
      O.sgn ((n + 1 : ℕ) : ZMod 2) (O.sgn 1 w) = O.sgn (n : ZMod 2) w := by
    have h := congrArg (fun f : O →ₗ[k] O => f w)
      (SVec.sgn_comp_sgn O ((n + 1 : ℕ) : ZMod 2) 1)
    simpa only [LinearMap.comp_apply, hp] using h
  rw [shiftedInputContraction, LinearMap.comp_apply,
    ← representable_sgn D Sc cutoff v t ((n + 1 : ℕ) : ZMod 2),
    ← representable_sgn D Sc cutoff v t 1]
  change capRowSign (k := k) n •
      O.sgn ((n + 1 : ℕ) : ZMod 2) (O.sgn 1 (A (Xs^[n] (J z)))) = C (T^[n] z)
  rw [hsgn, hiter, hAJ, hCsign, ← map_smul]
  rw [capRowSign_sgn_iterate U T hT n z]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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
namespace OddMath.QuiverHecke.ELVOld.MatrixEntryTotals
universe u
variable {k : Type u} [CommRing k]
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
private theorem restriction_total (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k B (SVec k)} (f : M ⟶ N) (t : C) :
    ((BalancedInduction.restriction J).map f).total t = f.total (J.obj t) := rfl
end OddMath.QuiverHecke.ELVOld.MatrixEntryTotals

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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
namespace OddMath.QuiverHecke.ELVOld
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
end OddMath.QuiverHecke.ELVOld
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end
