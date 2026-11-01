import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryParity
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeScalarInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientComparison

/-! # Scalar quotient and ordinary probe append induction
The proved scalar-kernel closure, the full quotient counit and composition
of balanced induction identify old scalar append induction with literal
ordinary quotient append induction. No height-algebra identification or
weighted coefficient-truncation specialization is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "cut" => probeCutoff D m
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν
local notation "C" => ELVOld.OldContentCategory D Sc cut ν
local notation "O" => OrdinaryContentCategory D Sc a ν

/-- Restriction uses the existing full scalar Superfunctor. -/
def probeOrdinaryRestriction (M : Superfunctor k O (SVec k)) : Superfunctor k C (SVec k) :=
  (probeOldOrdinarySuperfunctor D Sc m ν).comp M

variable (M : Superfunctor k (OrdinaryContentCategory D Sc
  (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))

private def probeQuotientCounitInverse (w : O) :
    M.obj w →ₗ[k] ELVOld.BalancedInduction.Obj Q (Q ⋙ M.toFunctor) w :=
  ELVOld.BalancedInduction.unit Q (Q ⋙ M.toFunctor) (probeOrdinaryOldObject D Sc m ν w)

private theorem probeQuotientCounit_right_inv (w : O) :
    (ELVOld.BalancedInduction.counit Q M.toFunctor w).comp
      (probeQuotientCounitInverse D Sc m ν M w) = LinearMap.id :=
  ELVOld.BalancedInduction.counit_unit Q M.toFunctor (probeOrdinaryOldObject D Sc m ν w)

private theorem probeQuotientCounit_left_inv (w : O) :
    (probeQuotientCounitInverse D Sc m ν M w).comp
      (ELVOld.BalancedInduction.counit Q M.toFunctor w) = LinearMap.id :=
  ELVOld.BalancedInduction.unit_counit_of_full Q M.toFunctor (probeOrdinaryOldObject D Sc m ν w)

/-- The full scalar quotient counit is an even isomorphism on modules. -/
def probeQuotientCounitIso :
    ELVOld.BalancedInduction.induced Q (probeOrdinaryRestriction D Sc m ν M) ≅ M :=
  ELVOld.moduleIsoOfEvenNatIso _ _
    (NatIso.ofComponents (fun w =>
      { hom := ELVOld.BalancedInduction.counit Q M.toFunctor w
        inv := probeQuotientCounitInverse D Sc m ν M w
        hom_inv_id := probeQuotientCounit_left_inv D Sc m ν M w
        inv_hom_id := probeQuotientCounit_right_inv D Sc m ν M w })
      (fun f => ELVOld.BalancedInduction.counit_naturality Q M.toFunctor f))
    (fun w => ELVOld.BalancedInduction.counit_mem Q M w)
    (fun w => ELVOld.BalancedInduction.unit_mem Q (probeOrdinaryRestriction D Sc m ν M)
      (probeOrdinaryOldObject D Sc m ν w))

variable
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)

/-- The scalar-evaluated old module has precisely its descended ordinary induction. -/
def probeQuotientInducedModuleIso :
    ELVOld.BalancedInduction.induced Q N ≅ probeOrdinaryModuleSuperfunctor D Sc m ν N hN :=
  ((ELVOld.BalancedInduction.induction Q).mapIso
    (eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN))).symm ≪≫
      probeQuotientCounitIso D Sc m ν (probeOrdinaryModuleSuperfunctor D Sc m ν N hN)

/-- Actual old append induction, descended by proved scalar-kernel closure,
agrees with literal ordinary append induction of the descended module. -/
def probeAppendOrdinaryModuleIso (i : I) :
    probeOrdinaryModuleSuperfunctor D Sc m (i :: ν)
      (ELVOld.BalancedInduction.induced (ELVOld.oldContentAppend D Sc cut ν i) N)
      (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN) ≅
    ELVOld.BalancedInduction.induced (probeOrdinaryAppend D Sc m ν i)
      (probeOrdinaryModuleSuperfunctor D Sc m ν N hN) :=
  let J := ELVOld.oldContentAppend D Sc cut ν i
  let T := probeOrdinaryAppend D Sc m ν i
  let U := probeOldOrdinaryFunctor D Sc m (i :: ν)
  let L := ELVOld.BalancedInduction.induced J N
  let hL := probeOldInduced_evaluatesCoefficients D m Sc ν i N hN
  (probeQuotientInducedModuleIso D Sc m (i :: ν) L hL).symm ≪≫
    (ELVOld.BalancedInduction.inductionComp J U).app N ≪≫
      ELVOld.BalancedInduction.inducedIsoOfFunctorEq (J ⋙ U) (Q ⋙ T)
        (probeOldOrdinaryFunctor_append D Sc m ν i) N ≪≫
      ((ELVOld.BalancedInduction.inductionComp Q T).app N).symm ≪≫
      (ELVOld.BalancedInduction.induction T).mapIso
        (probeQuotientInducedModuleIso D Sc m ν N hN)

end OddMath.QuiverHecke