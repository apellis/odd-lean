import OddMath.QuiverHecke.CyclotomicAction.ELVProbeShiftedUnitComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVParityMatrixCoordinates

/-! # Selected scalar charts for the prescribed finite matrices

DeformedMatrixComparison (4), (5) requires genuine invertible charts on the
source and target of each matrix. These are the selected scalar append
isomorphisms, including the induced restriction equality in the E/F source.
The charts are independent of the matrix's invertibility.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u

private theorem matrixChart_total_mem
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C]
    [Supercategory k C] {F G : Superfunctor k C (SVec k)} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ 0) (w : C) :
    f.total w ∈ parity (R := k) (F.obj w) (G.obj w) 0 := by
  have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) w
  rw [SuperNatTrans.total, hz, add_zero]
  exact f.app_mem 0 w

section AppendCharts
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
  (R : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hR : ProbeEvaluatesCoefficients D m Sc ν R)
  (M : Superfunctor k (OrdinaryContentCategory D Sc
    (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))
  (c : probeOrdinaryModuleSuperfunctor D Sc m ν R hR ≅ M) (i : I)
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m ν R hR

/-- The original chosen append isomorphism on its literal old/ordinary coends. -/
def probeAppendLinearEquiv (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    Obj J R.toFunctor w ≃ₗ[k] Obj T (O).toFunctor ((U).obj w) :=
  moduleIsoLinearEquiv (probeAppendOrdinaryModuleIso D Sc m ν R hR i) ((U).obj w)

/-- This invertible chart has exactly the previously computed selected map. -/
theorem probeAppendLinearEquiv_hom
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    (probeAppendLinearEquiv D Sc m ν R hR i w).toLinearMap =
      probeAppendComparisonLinear D Sc m ν R hR i w := rfl

/-- The given input isomorphism is induced after the chosen scalar comparison. -/
def probeMappedAppendLinearEquiv
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    Obj J R.toFunctor w ≃ₗ[k] Obj T M.toFunctor ((U).obj w) :=
  moduleIsoLinearEquiv (probeMappedAppendIso D Sc m ν R hR M c i) ((U).obj w)

theorem probeMappedAppendLinearEquiv_hom
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    (probeMappedAppendLinearEquiv D Sc m ν R hR M c i w).toLinearMap =
      probeMappedAppendLinear D Sc m ν R hR M c i w := by
  apply LinearMap.ext
  intro b
  exact (probeMappedAppendLinear_eq D Sc m ν R hR M c i w b).symm

/-- The original selected append chart is even on the actual module values. -/
theorem probeAppendLinearEquiv_mem
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    SVec.ofHom (probeAppendLinearEquiv D Sc m ν R hR i w).toLinearMap ∈
      parity (R := k) ((induction J).obj R |>.obj w) ((induction T).obj O |>.obj ((U).obj w)) 0 :=
  matrixChart_total_mem (probeAppendOrdinaryModuleIso_hom_mem D Sc m ν R hR i) ((U).obj w)

/-- The mapped chart retains the original selected isomorphism and the induced
specified input comparison. -/
theorem probeMappedAppendIso_eq :
    probeMappedAppendIso D Sc m ν R hR M c i =
      probeAppendOrdinaryModuleIso D Sc m ν R hR i ≪≫ (induction T).mapIso c := rfl

/-- An even given input isomorphism yields an even mapped append isomorphism. -/
theorem probeMappedAppendIso_hom_mem
    (hc : c.hom ∈ parity (R := k) _ _ 0) :
    (probeMappedAppendIso D Sc m ν R hR M c i).hom ∈ parity (R := k) _ _ 0 := by
  rw [probeMappedAppendIso_eq, Iso.trans_hom, Functor.mapIso_hom]
  simpa only [zero_add] using comp_mem
    (probeAppendOrdinaryModuleIso_hom_mem D Sc m ν R hR i)
    (IsSuperfunctor.map_mem (F := induction T) hc)

/-- The mapped chart is even on the literal old/ordinary module values. -/
theorem probeMappedAppendLinearEquiv_mem
    (hc : c.hom ∈ parity (R := k) _ _ 0)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    SVec.ofHom (probeMappedAppendLinearEquiv D Sc m ν R hR M c i w).toLinearMap ∈
      parity (R := k) ((induction J).obj R |>.obj w) ((induction T).obj M |>.obj ((U).obj w)) 0 :=
  matrixChart_total_mem (probeMappedAppendIso_hom_mem D Sc m ν R hR M c i hc) ((U).obj w)

end AppendCharts

section MatrixCharts
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "K" => ELVOld.oldContentAppend D Sc (probeCutoff D m) (i :: ν) i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN
local notation "R" => Functor.obj (restriction J) N
local notation "hR" => probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
local notation "c" => eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)

/-- The actual E/F source chart, with the same chosen restriction equality
and selected append isomorphism as in the mate and cap calculations. -/
abbrev probeMatrixSourceLinearEquiv
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :=
  probeMappedAppendLinearEquiv D Sc m ν R hR ((restriction T).obj O) c i w

/-- The E/F chart's map is the original computed selected source comparison. -/
theorem probeMatrixSourceLinearEquiv_hom
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    (probeMatrixSourceLinearEquiv D Sc m ν i N hN w).toLinearMap =
      probeMappedAppendLinear D Sc m ν R hR ((restriction T).obj O) c i w :=
  probeMappedAppendLinearEquiv_hom D Sc m ν R hR ((restriction T).obj O) c i w

/-- The actual F/E target chart is the original selected next append map. -/
abbrev probeMatrixTargetLinearEquiv
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :=
  probeAppendLinearEquiv D Sc m (i :: ν) N hN i ((K).obj w)

theorem probeMatrixTargetLinearEquiv_hom
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    (probeMatrixTargetLinearEquiv D Sc m ν i N hN w).toLinearMap =
      probeAppendComparisonLinear D Sc m (i :: ν) N hN i ((K).obj w) := rfl

end MatrixCharts
end OddMath.QuiverHecke
