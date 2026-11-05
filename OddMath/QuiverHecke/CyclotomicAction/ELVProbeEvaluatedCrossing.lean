import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridCrossSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentAffineRelations

/-! # The chosen equal crossing on scalar-evaluated OLD probes

Brundan–Ellis Definition 1.5, (1.7): restrict the prescribed negative
double-induction crossing to the full scalar-evaluated module category.
The actual balanced flattening, every input module map, and odd crossing
parity are retained. No inverse or complete-factor hypothesis is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppend D Sc cut ν i
local notation "K" => oldContentAppend D Sc cut (i :: ν) i
private theorem equalCross_degree :
    IsSupernatural k (D.parity i) (oldContentEqualCross D Sc cut ν i) := by
  simpa only [SKM.zmod2_mul_self] using oldContentEqualCross_supernatural D Sc cut ν i
local notation "hCross" => equalCross_degree D Sc m ν i
local notation "E" => probeEvaluatedInduction D Sc m ν i
local notation "E'" => probeEvaluatedInduction D Sc m (i :: ν) i
local notation "P" => ProbeEvaluatesCoefficients D m Sc ν
local notation "Q" => ProbeEvaluatesCoefficients D m Sc (i :: i :: ν)

private theorem doubleInduction_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k)) (hN : P N) :
    Q (((inductionModuleCell (k := k) J) ≫ inductionModuleCell (k := k) K).obj N) :=
  ((E ⋙ E').obj ⟨N, hN⟩).property

/-- The homogeneous crossing on the actual evaluated double induction. -/
def probeEvaluatedEqualCross :
    End (⟨E ⋙ E'⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m (i :: i :: ν))) :=
  fullLiftTrans P Q (doubleInduction_closed D Sc m ν i)
    (doubleInduction_closed D Sc m ν i) (inductionModuleCross J K hCross)

theorem probeEvaluatedEqualCross_mem :
    probeEvaluatedEqualCross D Sc m ν i ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (fullLiftTrans_homogeneous P Q (doubleInduction_closed D Sc m ν i)
      (doubleInduction_closed D Sc m ν i) (inductionModuleCross J K hCross)
      (Superfunctor.mem_parity_iff_isHomogeneous.mp (inductionModuleCross_mem J K hCross)))

/-- Each parity component is the identical chosen OLD component. -/
theorem probeEvaluatedEqualCross_native_app (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeEvaluatedEqualCross D Sc m ν i).app q N).hom =
      (inductionModuleCross J K hCross).app q N.obj := rfl

end OddMath.QuiverHecke
